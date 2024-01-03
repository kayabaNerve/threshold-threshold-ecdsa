#![allow(non_snake_case)]

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

    use num_traits::{Zero, One, Signed, FromBytes};
    use num_integer::Integer;

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

    // TODO: Replace with a proven, decentralized flow
    let ec_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let k_ciphertext =
      cg.encrypt(&mut OsRng, &public_key, &BigUint::from_bytes_be(ec_key.to_repr().as_ref())).1;
    let ec_key = <Secp256k1 as Ciphersuite>::generator() * ec_key;
    dbg!("Shimmed key gen");

    let mut segment_time = std::time::Instant::now();

    // Round 1: Publish additive shares of the nonce
    let mut x_is = vec![];
    let mut X_is = vec![];
    let mut x_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      let mut num_bytes = [0; 32];
      let x_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(x_i.to_repr().as_ref());
      x_is.push(x_i);

      X_is.push(<Secp256k1 as Ciphersuite>::generator() * x_i);

      let (_, ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key,
        &x_i,
      );
      println!(
        "Proved for X_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
      proof
        .verify(&cg, &mut transcript(), &public_key, &ciphertext, *X_is.last().unwrap())
        .unwrap();
      println!(
        "Verified X_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
      x_i_ciphertexts.push(ciphertext);
    }
    let X = X_is.into_iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let r = <Secp256k1 as Ciphersuite>::F::from_repr(X.to_affine().x()).unwrap();

    // Everyone now calculates the sum nonce
    let mut x_ciphertext = x_i_ciphertexts.pop().unwrap();
    for x_i_ciphertext in &x_i_ciphertexts {
      x_ciphertext = x_ciphertext.add_without_randomness(x_i_ciphertext);
    }

    println!(
      "Calculated X: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Round 2: Perform multiplication of the sum nonce by our shares of y
    let mut y_is = vec![];
    let mut y_i_ciphertexts = vec![];
    let mut xy_i_ciphertexts = vec![];
    let mut ky_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      // Decide y
      let mut num_bytes = [0; 32];
      let y_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(y_i.to_repr().as_ref());
      y_is.push(y_i);

      let y_i_uint = BigUint::from_bytes_be(&num_bytes);
      let (y_randomness, y_i_ciphertext) = cg.encrypt(&mut OsRng, &public_key, &y_i_uint);
      println!(
        "Encrypted Y_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();

      // Create xy_i_ciphertext and ky_i_ciphertext
      let (xy_randomness, xy_i_ciphertext) =
        cg.mul(&mut OsRng, &public_key, &x_ciphertext, &y_i_uint);
      let (ky_randomness, ky_i_ciphertext) =
        cg.mul(&mut OsRng, &public_key, &k_ciphertext, &y_i_uint);

      println!(
        "Created xy_i ky_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();

      // For 2022-1437 5.2, a scaled ciphertext proof can be created with:
      // m=2, ws [a, y]
      // i=2, Ys [(a + by)G, (a + by)K + xyF]
      //      Xs [[G, bG], [K, bK + xF]]
      //
      // For an additionally proven Y_i with ciphertext aG, aK + yF, we need to add 2 is:
      // +Ys [aG, aK + yF]
      // +Xs [[G, Identity], [K, F]]
      //
      // And then finally, since we need to prove both xy and ky, we add:
      // +m for randomness c, padding prior Xs with Identity
      // +Ys [ky_i_ciphertext.0, ky_i_ciphertext.1]
      // +Xs [[Identity, k_ciphertext.0, G], [Identity, k_ciphertext.1, K]]
      //
      // Re-organized, and with distinct randomness for the y_i ciphertext and further usage, we
      // create a m=4, i=6 we organize as follows:
      // a = y randomness
      // b = xy randomness
      // c = ky randomness
      // ws = [a, b, c, y]
      // Ys = [..y_ciphertext, ..xy_ciphertext, ..ky_ciphertext]
      // Xs = [
      //   [G,        Identity, Identity, Identity],
      //   [K,        Identity, Identity, F],
      //   [Identity, G,        Identity, x_ciphertext.0],
      //   [Identity, K,        Identity, x_ciphertext.1],
      //   [Identity, Identity, G,        k_ciphertext.0],
      //   [Identity, Identity, K,        k_ciphertext.1],
      // ]
      #[rustfmt::skip]
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [
          [cg.g(),        cg.identity(), cg.identity(), cg.identity()],
          [&public_key,   cg.identity(), cg.identity(), cg.f()],
          [cg.identity(), cg.g(),        cg.identity(), &x_ciphertext.0],
          [cg.identity(), &public_key,   cg.identity(), &x_ciphertext.1],
          [cg.identity(), cg.identity(), cg.g(),        &k_ciphertext.0],
          [cg.identity(), cg.identity(), &public_key,   &k_ciphertext.1],
        ],
        [&y_randomness, &xy_randomness, &ky_randomness, &y_i_uint],
      );
      println!(
        "Proved for y_i xy_i ky_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();
      #[rustfmt::skip]
      proof
        .verify(
          &cg,
          &mut transcript(),
          // Assumes the ZkEncryptionProof randomness bound is <= this
          &cg.secret_bound(),
          [
            [cg.g(),        cg.identity(), cg.identity(), cg.identity()],
            [&public_key,   cg.identity(), cg.identity(), cg.f()],
            [cg.identity(), cg.g(),        cg.identity(), &x_ciphertext.0],
            [cg.identity(), &public_key,   cg.identity(), &x_ciphertext.1],
            [cg.identity(), cg.identity(), cg.g(),        &k_ciphertext.0],
            [cg.identity(), cg.identity(), &public_key,   &k_ciphertext.1],
          ],
          [
            &y_i_ciphertext.0,  &y_i_ciphertext.1,
            &xy_i_ciphertext.0, &xy_i_ciphertext.1,
            &ky_i_ciphertext.0, &ky_i_ciphertext.1,
          ],
        )
        .unwrap();
      println!(
        "Verified y_i xy_i ky_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();

      y_i_ciphertexts.push(y_i_ciphertext);
      xy_i_ciphertexts.push(xy_i_ciphertext);
      ky_i_ciphertexts.push(ky_i_ciphertext);
    }

    // Everyone now calculates y, z, and d
    let mut y_ciphertext = y_i_ciphertexts.pop().unwrap();
    for y_i_ciphertext in &y_i_ciphertexts {
      y_ciphertext = y_ciphertext.add_without_randomness(y_i_ciphertext);
    }
    let mut z_ciphertext = xy_i_ciphertexts.pop().unwrap();
    for xy_ciphertext in &xy_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(xy_ciphertext);
    }
    let mut d_ciphertext = ky_i_ciphertexts.pop().unwrap();
    for ky_ciphertext in &ky_i_ciphertexts {
      d_ciphertext = d_ciphertext.add_without_randomness(ky_ciphertext);
    }

    println!(
      "y, z, and d sums: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Multiply d by r
    let dr_ciphertext =
      d_ciphertext.mul_without_randomness(&BigUint::from_bytes_be(r.to_repr().as_ref()));
    println!(
      "dr ciphertext calculation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Round 3
    // Technically, any threshold can perform this round, even if distinct from the prior used set
    let m1_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    // Multiply y by H(m)
    let my_ciphertext =
      y_ciphertext.mul_without_randomness(&BigUint::from_bytes_be(m1_hash.to_repr().as_ref()));

    let w_ciphertext = my_ciphertext.add_without_randomness(&dr_ciphertext);
    println!(
      "w ciphertext calculation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Publish the decryption shares for w and z
    // z can be decrypted in additional preprocess round if minimization of this round is desired
    let set = [1, 2, 3];
    let mut W_is = vec![];
    let mut Z_is = vec![];
    for i in 1u16 ..= 3 {
      // Calculate the literal shares
      let share_to_use = &shares[&i] * &delta;
      // The lagrange can be post-calculated so that the first `t` to publish shares for a
      // completed signature may be used together
      let lagrange = IntegerSecretSharing::lagrange(4, i, &set);
      let share_to_use = share_to_use * lagrange.abs().to_biguint().unwrap();

      // If the lagrange (a publicly known coefficient) is negative, use the negative form of the
      // ciphertext's randomness element
      let w_ciphertext_neg = w_ciphertext.0.clone().neg();
      let w_ciphertext_base =
        if lagrange.is_positive() { &w_ciphertext.0 } else { &w_ciphertext_neg };
      let W_i = w_ciphertext_base.mul(&share_to_use);
      let z_ciphertext_neg = z_ciphertext.0.clone().neg();
      let z_ciphertext_base =
        if lagrange.is_positive() { &z_ciphertext.0 } else { &z_ciphertext_neg };
      let Z_i = z_ciphertext_base.mul(&share_to_use);

      let share_max_size = BigUint::one() <<
        (IntegerSecretSharing::share_size(&cg, 3, 4) + delta.bits() + lagrange.bits());

      // Prove the encryption shares are well-formed
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [[cg.g()], [w_ciphertext_base], [z_ciphertext_base]],
        [&share_to_use],
      );
      println!(
        "Calculated and proved for decryption shares: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();

      // Verification of these can be delayed and only performed if an invalid signature is
      // produced
      proof
        .verify(
          &cg,
          &mut transcript(),
          &share_max_size,
          [[cg.g()], [w_ciphertext_base], [z_ciphertext_base]],
          [&verification_shares[&i].mul(&lagrange.abs().to_biguint().unwrap()), &W_i, &Z_i],
        )
        .unwrap();
      println!(
        "Verified decryption shares: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();

      W_is.push(W_i);
      Z_is.push(Z_i);
    }

    // Sum the decryption shares
    let mut W = W_is.pop().unwrap();
    for W_i in &W_is {
      W = W.add(W_i);
    }
    let mut Z = Z_is.pop().unwrap();
    for Z_i in &Z_is {
      Z = Z.add(Z_i);
    }

    println!(
      "Summed decryption shares: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Recover the messages
    let w = {
      let M = w_ciphertext.1.mul(&(&delta * &delta * &delta)).add(&W.neg());
      let value_scaled_by = (&delta * &delta * &delta) % cg.p();
      // Invert value_scaled_by over p
      let inverse = value_scaled_by.modpow(&(cg.p() - 2u8), cg.p());
      assert!((&inverse * &value_scaled_by).mod_floor(cg.p()).is_one());
      (cg.solve(M).unwrap() * inverse) % cg.p()
    };
    let z = {
      let M = z_ciphertext.1.mul(&(&delta * &delta * &delta)).add(&Z.neg());
      let value_scaled_by = (&delta * &delta * &delta) % cg.p();
      // Invert value_scaled_by over p
      let inverse = value_scaled_by.modpow(&(cg.p() - 2u8), cg.p());
      assert!((&inverse * &value_scaled_by).mod_floor(cg.p()).is_one());
      (cg.solve(M).unwrap() * inverse) % cg.p()
    };

    println!(
      "w and z decryption: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Add the share for signer 1
    // Create and publish the signature
    let s = ({
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      bytes_ref.copy_from_slice(&w.to_bytes_be());
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    }) * ({
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      bytes_ref.copy_from_slice(&z.to_bytes_be());
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    })
    .invert()
    .unwrap();

    println!(
      "Signature creation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    // segment_time = std::time::Instant::now();

    verify(ec_key, m1_hash, r, s);
  }
}
