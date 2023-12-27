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
  use rand_core::OsRng;
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
  pub fn protocol() {
    use std::collections::HashMap;

    use transcript::{Transcript, RecommendedTranscript};

    use num_traits::*;
    use num_integer::Integer;
    use num_bigint::{Sign, BigInt};

    use class_group::*;
    use proofs::*;
    use mpc::*;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let transcript = || RecommendedTranscript::new(b"Protocol Test");
    let mut shares = HashMap::new();
    for i in 1u16 ..= 4u16 {
      shares.insert(i, BigUint::zero());
    }
    let mut delta = None;
    let mut public_key: Option<Element> = None;
    let mut verification_shares = HashMap::new();
    for _ in 1u16 ..= 4u16 {
      let iss = IntegerSecretSharing::new(&mut OsRng, &cg, &mut transcript(), 3, 4);
      if delta.is_none() {
        delta = Some(iss.delta.clone());
      }
      assert_eq!(delta.as_ref(), Some(&iss.delta));
      let contribution = &iss.commitments[0].commitment;
      if let Some(public_key) = &mut public_key {
        for i in 1u16 ..= 4u16 {
          let mut eval = iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta));
          #[allow(non_snake_case)]
          for (C_i, C) in iss.commitments[1 ..].iter().enumerate() {
            let C_i = C_i + 1;
            let i = BigUint::from(i);
            eval = eval.add(&C.commitment.mul(&i.pow(u32::try_from(C_i).unwrap())));
          }
          let existing: &mut Element = verification_shares.get_mut(&i).unwrap();
          let new = existing.add(&eval);
          *existing = new;
        }
        *public_key = public_key.add(contribution);
      } else {
        for i in 1u16 ..= 4u16 {
          let mut eval = iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta));
          #[allow(non_snake_case)]
          for (C_i, C) in iss.commitments[1 ..].iter().enumerate() {
            let C_i = C_i + 1;
            let i = BigUint::from(i);
            eval = eval.add(&C.commitment.mul(&i.pow(u32::try_from(C_i).unwrap())));
          }
          verification_shares.insert(i, eval);
        }
        public_key = Some(contribution.clone());
      }
      for (i, share) in iss.shares {
        *shares.get_mut(&i).unwrap() += share;
      }
    }
    let delta = delta.unwrap();
    let public_key = public_key.unwrap();
    dbg!("Shimmed key gen");

    // Round 1: Publish additive shares of the nonce
    let mut x_is = vec![];
    #[allow(non_snake_case)]
    let mut X_is = vec![];
    let mut x_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      let mut num_bytes = [0; 32];
      let x_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(x_i.to_repr().as_ref());
      x_is.push(x_i);

      #[allow(non_snake_case)]
      let X = <Secp256k1 as Ciphersuite>::generator() * x_i;
      X_is.push(<Secp256k1 as Ciphersuite>::generator() * x_i);

      let message = BigUint::from_bytes_be(&num_bytes);
      // TODO: Replace this ciphertext validity proof with 2020-084 Fig 7, as comprehensive to X_i
      let (ciphertext, proof) =
        ZkEncryptionProof::prove(&mut OsRng, &cg, &mut transcript(), &public_key, &message);
      proof.verify(&cg, &mut transcript(), &public_key, &ciphertext).unwrap();
      x_i_ciphertexts.push(ciphertext);
    }
    let x = x_is.into_iter().sum::<<Secp256k1 as Ciphersuite>::F>();
    #[allow(non_snake_case)]
    let X = X_is.into_iter().sum::<<Secp256k1 as Ciphersuite>::G>();

    // Everyone now calculates the sum nonce
    let mut x_ciphertext = x_i_ciphertexts.pop().unwrap();
    for x_i_ciphertext in &x_i_ciphertexts {
      x_ciphertext = x_ciphertext.add_without_randomness(x_i_ciphertext);
    }

    // Round 2: Perform multiplication of the sum nonce by our shares of y
    let mut y_is = vec![];
    let mut xy_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      let mut num_bytes = [0; 32];
      let y_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(y_i.to_repr().as_ref());
      y_is.push(y_i);
      // If x_ciphertext has no randomness, this would immediately allow decryption, leaking our
      // y_i
      // x_ciphertext does have randomness from every participant participating (including
      // ourselves)
      // This randomness will also never be revealed
      // The eventual decryption of the remaining z_i value is after re-randomization by each
      // substractive share
      // This re-randomization doesn't include new randomness from signer i == 1, meaning a
      // malicious t-1 may give the decryptor this randomness, leaking all prior values
      // For the decryptor to notice and do so would require they also be malicious, preserving the
      // t threshold
      let scalar = BigUint::from_bytes_be(&num_bytes);
      let xy_i_ciphertext = x_ciphertext.mul_without_randomness(&scalar);

      // Prove this was correctly scaled
      let proof = ZkDlogEqualityProof::prove(&mut OsRng, &cg, &mut transcript(), &x_ciphertext.0, &x_ciphertext.1, &scalar);
      proof.verify(&cg, &mut transcript(), cg.p(), &x_ciphertext.0, &x_ciphertext.1, &xy_i_ciphertext.0, &xy_i_ciphertext.1).unwrap();
      xy_i_ciphertexts.push(xy_i_ciphertext);
    }
    let y = y_is.into_iter().sum::<<Secp256k1 as Ciphersuite>::F>();

    // Also, for signers i != 0, publish the subtractive shares
    let mut z_is = vec![];
    let mut z_i_ciphertexts = vec![];
    for _ in 1 .. 3 {
      let mut num_bytes = [0; 32];
      let z_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice((-z_i).to_repr().as_ref());
      z_is.push(z_i);
      let message = BigUint::from_bytes_be(&num_bytes);
      let (ciphertext, proof) =
        ZkEncryptionProof::prove(&mut OsRng, &cg, &mut transcript(), &public_key, &message);
      proof.verify(&cg, &mut transcript(), &public_key, &ciphertext).unwrap();
      z_i_ciphertexts.push(ciphertext);
    }

    // Everyone now calculates xy and the sum of the posted subtractive shares
    let mut z_ciphertext = xy_i_ciphertexts.pop().unwrap();
    for xy_ciphertext in &xy_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(xy_ciphertext);
    }
    for z_i_ciphertext in &z_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(z_i_ciphertext);
    }

    // Round 3: For signers i != 1, publish the decryption share for the remaining ciphertext
    let set = [1, 2, 3];
    #[allow(non_snake_case)]
    let mut W_is = vec![];
    for i in 2u16 ..= 3 {
      #[allow(non_snake_case)]
      let W_i = z_ciphertext.0.mul(&(&shares[&i] * &delta));

      // Prove this is a correct decryption share
      let coefficient_size = BigUint::one() << cg.secret_bits();
      // Coefficient 0 is of size coefficient * delta
      // Coefficient t for t != 0 is of size coefficient * n.pow(n)
      // There are t-1 such coefficients

      let share_max_size = (&coefficient_size * &delta) + ((&coefficient_size * BigUint::from(4u16).pow(4u16)) * BigUint::from(3u16 - 1));
      let proof = ZkDlogEqualityProof::prove(&mut OsRng, &cg, &mut transcript(), cg.g(), &z_ciphertext.0, &(&shares[&i] * &delta));
      proof.verify(&cg, &mut transcript(), &share_max_size, cg.g(), &z_ciphertext.0, &verification_shares[&i], &W_i).unwrap();

      // Technically, the lagrange coefficient can be applied after collecting shares
      // The provided lagrange function inlines the delta multiplication so it can return a single
      // value, so to post-include the lagrange would be to include delta twice (as delta must be
      // included here)
      // While we could rewrite the lagrange function to return a (numerator, denominator), we
      // don't need post-determinism of the lagrange coefficient
      let lagrange = IntegerSecretSharing::lagrange(4, i, &set);
      #[allow(non_snake_case)]
      let W_i = if lagrange < BigInt::zero() {
        W_i.neg().mul(&(-lagrange).to_biguint().unwrap())
      } else {
        W_i.mul(&lagrange.to_biguint().unwrap())
      };
      W_is.push(W_i);
    }

    // For signer 1, calculate and keep the final decryption share to be the sole decryptor of what
    // remains of z
    #[allow(non_snake_case)]
    let mut W = z_ciphertext.0.mul(
      &(&shares[&1] * &delta * IntegerSecretSharing::lagrange(4, 1, &set).to_biguint().unwrap()),
    );
    #[allow(non_snake_case)]
    for W_i in W_is {
      W = W.add(&W_i);
    }

    // Recover the message
    let z_i_1 = {
      #[allow(non_snake_case)]
      let M = z_ciphertext.1.mul(&(&delta * &delta * &delta)).add(&W.neg());
      let value_scaled_by = BigInt::from_biguint(Sign::Plus, (&delta * &delta * &delta) % cg.p());
      // Invert value_scaled_by over p
      let p = BigInt::from_biguint(Sign::Plus, cg.p().clone());
      let gcd = p.extended_gcd(&value_scaled_by);
      assert!(gcd.gcd.is_one());
      let inverse = if gcd.y.sign() == num_bigint::Sign::Plus { gcd.y } else { &p + gcd.y };
      assert!((&inverse * &value_scaled_by).mod_floor(&p).is_one());
      let inverse = inverse.to_biguint().unwrap();
      (cg.solve(M).unwrap() * inverse) % cg.p()
    };
    let z_i_2_and_3 = z_is.iter().sum::<<Secp256k1 as Ciphersuite>::F>();
    assert_eq!(
      (BigUint::from_bytes_be(z_i_2_and_3.to_repr().as_ref()) + z_i_1) % cg.p(),
      BigUint::from_bytes_be((x * y).to_repr().as_ref()),
    );

    // Round 4: Publish signature shares
    // TODO. Requires:
    // - Pulling in the dkg crate
    // - Having setup create a ciphertext for k (same process as for x)
    // - Not just publishing xy_i ciphertexts yet ky_i ciphertexts
    // - Also taking subtractive shares of ky
  }
}
