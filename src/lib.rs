use ciphersuite::{
  group::{ff::PrimeField, Group},
  Ciphersuite, Secp256k1,
};
use elliptic_curve::point::AffineCoordinates;

pub mod paillier;

pub fn verify(
  public_key: <Secp256k1 as Ciphersuite>::G,
  message_hash: <Secp256k1 as Ciphersuite>::F,
  r: <Secp256k1 as Ciphersuite>::F,
  s: <Secp256k1 as Ciphersuite>::F,
) {
  assert_ne!(r, <Secp256k1 as Ciphersuite>::F::ZERO);
  assert_ne!(s, <Secp256k1 as Ciphersuite>::F::ZERO);

  let z = message_hash;
  let u1 = z * s.invert().unwrap();
  let u2 = r * s.invert().unwrap();
  let point = (Secp256k1::generator() * u1) + (public_key * u2);
  assert!(!bool::from(point.is_identity()));
  assert_eq!(r.to_repr(), point.to_affine().x());

  ecdsa::hazmat::verify_prehashed(
    &public_key,
    &message_hash.to_repr(),
    &ecdsa::Signature::<k256::Secp256k1>::from_scalars(r, s).unwrap(),
  )
  .unwrap()
}

#[cfg(test)]
mod tests {
  use rand_core::OsRng;
  use super::*;

  #[test]
  fn paillier() {
    use crypto_bigint::*;
    use paillier::*;

    let (private, public) = PrivateKey::new(&mut OsRng);
    println!("Created private key in paillier test");
    loop {
      let message = Uint::<{ N_LIMBS }>::random(&mut OsRng);
      if let Some(ciphertext) = public.encrypt(&mut OsRng, message) {
        assert_eq!(message, private.decrypt(ciphertext).unwrap());
        break;
      }
    }
  }

  #[test]
  fn non_distributed() {
    use ciphersuite::group::ff::Field;

    let private_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    let x = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let y = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let z = x * y;
    let d = private_key * y;

    let r = <Secp256k1 as Ciphersuite>::F::from_repr((Secp256k1::generator() * x).to_affine().x())
      .unwrap();

    let message_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let w = (message_hash * y) + (r * d);
    let s = w * z.invert().unwrap();

    verify(Secp256k1::generator() * private_key, message_hash, r, s);
  }
}
