use rand_core::{RngCore, CryptoRng};

use num_bigint::BigUint;

use ciphersuite::{
  group::{ff::PrimeField, Group},
  Ciphersuite, Secp256k1,
};
use elliptic_curve::point::AffineCoordinates;

pub mod class_group;
pub mod proofs;
pub mod mpc;

pub fn sample_number_less_than(rng: &mut (impl RngCore + CryptoRng), bound: &BigUint) -> BigUint {
  loop {
    let mut bytes = vec![0; bound.bits().div_ceil(8).try_into().unwrap()];
    rng.fill_bytes(&mut bytes);
    let x = BigUint::from_bytes_be(&bytes);
    if x >= *bound {
      continue;
    }
    break x;
  }
}

pub fn verify(
  public_key: <Secp256k1 as Ciphersuite>::G,
  m1_hash: <Secp256k1 as Ciphersuite>::F,
  r: <Secp256k1 as Ciphersuite>::F,
  s: <Secp256k1 as Ciphersuite>::F,
) {
  assert_ne!(r, <Secp256k1 as Ciphersuite>::F::ZERO);
  assert_ne!(s, <Secp256k1 as Ciphersuite>::F::ZERO);

  let z = m1_hash;
  let u1 = z * s.invert().unwrap();
  let u2 = r * s.invert().unwrap();
  let point = (Secp256k1::generator() * u1) + (public_key * u2);
  assert!(!bool::from(point.is_identity()));
  assert_eq!(r.to_repr(), point.to_affine().x());

  ecdsa::hazmat::verify_prehashed(
    &public_key,
    &m1_hash.to_repr(),
    &ecdsa::Signature::<k256::Secp256k1>::from_scalars(r, s).unwrap(),
  )
  .unwrap()
}

#[cfg(test)]
mod tests {
  use rand_core::{RngCore, OsRng};
  use crypto_bigint::*;
  use ciphersuite::group::ff::Field;
  use super::*;

  #[test]
  fn non_distributed() {
    let private_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    let x = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let y = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let z = x * y;
    let d = private_key * y;

    let r = <Secp256k1 as Ciphersuite>::F::from_repr((Secp256k1::generator() * x).to_affine().x())
      .unwrap();

    let m1_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let w = (m1_hash * y) + (r * d);
    let s = w * z.invert().unwrap();

    verify(Secp256k1::generator() * private_key, m1_hash, r, s);
  }

  #[test]
  fn class_group() {
    use num_traits::*;
    use class_group::*;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let (private_key, public_key) = cg.key_gen(&mut OsRng);

    let mut m1 = vec![0; 31];
    OsRng.fill_bytes(&mut m1);
    let m1 = num_bigint::BigUint::from_be_bytes(&m1);
    assert_eq!(cg.decrypt(&private_key, &cg.encrypt(&mut OsRng, &public_key, &m1)).unwrap(), m1);

    let mut m2 = vec![0; 31];
    OsRng.fill_bytes(&mut m2);
    let m2 = num_bigint::BigUint::from_be_bytes(&m2);
    assert_eq!(cg.decrypt(&private_key, &cg.encrypt(&mut OsRng, &public_key, &m2)).unwrap(), m2);

    assert_eq!(
      cg.decrypt(
        &private_key,
        &cg.add(
          &mut OsRng,
          &public_key,
          &cg.encrypt(&mut OsRng, &public_key, &m1),
          &cg.encrypt(&mut OsRng, &public_key, &m2)
        ),
      )
      .unwrap(),
      &m1 + &m2,
    );

    assert_eq!(
      cg.decrypt(
        &private_key,
        &cg.mul(&mut OsRng, &public_key, &cg.encrypt(&mut OsRng, &public_key, &m1), &m2)
      )
      .unwrap(),
      (&m1 * &m2) % &secp256k1_mod,
    );
  }

  #[test]
  fn mta() {
    /*
    - `ciphertext_x_i` = `Enc(x_i)` <- 1 round of communication
    - `ciphertext_x` = `Product(ciphertext_x_i)`
    - `ciphertext_xy_i` = `ciphertext_x ** y_i` <- 1 round of communication
    - `ciphertext_z` = `Product(ciphertext_xy_i)`
    - `z_i` = `rand()` for i in 2 ..= t
    - `ciphertext_z_i` = `Enc(-z_i)` <- 1 round of communication
    - `ciphertext_z_1` = `Product(ciphertext_z, ciphertext_z_i)`
    - Send `1` decryption share for `ciphertext_z_1` if i in 2 ..= t <- 1 round of communication
    */

    use ciphersuite::group::ff::Field;

    use num_traits::*;
    use num_bigint::*;

    use class_group::*;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let (private, public) = cg.key_gen(&mut OsRng);

    let mut x = vec![];
    let mut y = vec![];
    for _ in 0 .. 4 {
      x.push(<Secp256k1 as Ciphersuite>::F::random(&mut OsRng));
      y.push(<Secp256k1 as Ciphersuite>::F::random(&mut OsRng));
    }
    let z = x.iter().sum::<<Secp256k1 as Ciphersuite>::F>() *
      y.iter().sum::<<Secp256k1 as Ciphersuite>::F>();

    let mut x_i_ciphertexts = vec![];
    for x in &x {
      let mut num_bytes = [0; 32];
      num_bytes.copy_from_slice(x.to_repr().as_ref());
      x_i_ciphertexts.push(cg.encrypt(&mut OsRng, &public, &BigUint::from_bytes_be(&num_bytes)));
    }

    let mut x_ciphertext = x_i_ciphertexts.pop().unwrap();
    for x_i_ciphertext in &x_i_ciphertexts {
      x_ciphertext = x_ciphertext.add_without_randomness(x_i_ciphertext);
    }

    let mut xy_i_ciphertexts = vec![];
    for y in &y {
      let mut num_bytes = [0; 32];
      num_bytes.copy_from_slice(y.to_repr().as_ref());
      xy_i_ciphertexts.push(cg.mul(
        &mut OsRng,
        &public,
        &x_ciphertext,
        &BigUint::from_bytes_be(&num_bytes),
      ));
    }

    let mut z_ciphertext = xy_i_ciphertexts.pop().unwrap();
    for xy_ciphertext in &xy_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(xy_ciphertext);
    }

    let mut z_i = vec![];
    for _ in 0 .. 3 {
      z_i.push(<Secp256k1 as Ciphersuite>::F::random(&mut OsRng));
    }

    let mut z_i_ciphertexts = vec![];
    for z_i in &z_i {
      let mut num_bytes = [0; 32];
      num_bytes.copy_from_slice((-z_i).to_repr().as_ref());
      z_i_ciphertexts.push(cg.encrypt(&mut OsRng, &public, &BigUint::from_bytes_be(&num_bytes)));
    }

    for z_i_ciphertext in &z_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(z_i_ciphertext);
    }

    let mut final_z_i = cg.decrypt(&private, &z_ciphertext).unwrap().to_bytes_be();
    assert!(final_z_i.len() <= 32);
    while final_z_i.len() < 32 {
      final_z_i.insert(0, 0);
    }
    let mut final_z_i_repr = [0; 32];
    final_z_i_repr.copy_from_slice(&final_z_i[(final_z_i.len() - 32) ..]);

    assert_eq!(
      z_i.into_iter().sum::<<Secp256k1 as Ciphersuite>::F>() +
        <Secp256k1 as Ciphersuite>::F::from_repr(final_z_i_repr.into()).unwrap(),
      z,
    );
  }

  #[test]
  fn dlog_without_subgroup() {
    use num_traits::*;

    use transcript::{Transcript, RecommendedTranscript};

    use class_group::*;
    use proofs::ZkDlogWithoutSubgroupProof;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let (private_key, public_key) = cg.key_gen(&mut OsRng);
    let transcript = || RecommendedTranscript::new(b"DLog Without Subgroup Proof Test");
    ZkDlogWithoutSubgroupProof::prove(&mut OsRng, &cg, &mut transcript(), &private_key)
      .verify(&cg, &mut transcript(), &public_key)
      .unwrap();
  }

  #[test]
  fn integer_secret_sharing() {
    use num_traits::*;

    use class_group::*;
    use mpc::IntegerSecretSharing;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    IntegerSecretSharing::new(&mut OsRng, &cg, 3, 4);
  }
}
