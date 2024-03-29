#![allow(non_snake_case)]

use rand_core::{RngCore, CryptoRng};

use malachite::{
  num::{logic::traits::*, conversion::traits::*},
  *,
};

use ciphersuite::{
  group::{ff::PrimeField, Group},
  Ciphersuite, Secp256k1,
};
use elliptic_curve::point::AffineCoordinates;

pub mod class_group;
pub mod proofs;
pub mod mpc;

pub fn sample_number_less_than(rng: &mut (impl RngCore + CryptoRng), bound: &Natural) -> Natural {
  loop {
    let mut bytes = vec![0; bound.significant_bits().div_ceil(8).try_into().unwrap()];
    rng.fill_bytes(&mut bytes);
    let x = Natural::from_digits_desc(&256, bytes.into_iter().map(u16::from)).unwrap();
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
  use core::cmp::Ordering;

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

    use malachite::num::{basic::traits::*, arithmetic::traits::*};

    use class_group::*;
    use proofs::*;
    use mpc::*;

    use super::*;

    const PARTICIPANTS: u16 = 4;
    const THRESHOLD: u16 = 3;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod =
      Natural::from_digits_desc(&256, secp256k1_mod.into_iter().map(u16::from)).unwrap();

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let transcript = || RecommendedTranscript::new(b"Protocol Test");

    let mut iss_s = vec![];
    let mut delta = None;
    let mut public_key = cg.identity().clone();
    for p in 1u16 ..= PARTICIPANTS {
      println!("Sharing for participant {p}");
      let iss =
        IntegerSecretSharing::new(&mut OsRng, &cg, &mut transcript(), THRESHOLD, PARTICIPANTS);
      if delta.is_none() {
        delta = Some(iss.delta.clone());
      }
      assert_eq!(delta.as_ref(), Some(&iss.delta));
      public_key = public_key.add(&iss.commitments[0].commitment);

      iss_s.push(iss);
    }
    let delta = delta.unwrap();
    let delta_square = delta.clone().pow(2);
    let public_key_table = public_key.large_table();

    let mut shares = HashMap::new();
    for i in 1u16 ..= PARTICIPANTS {
      shares.insert(i, Natural::ZERO);
    }
    let mut verification_shares = HashMap::new();
    for p in 1u16 ..= PARTICIPANTS {
      println!("Accumulating shares for {p}");
      let mut scalars = vec![];
      let mut points = vec![];
      for sender in 1u16 ..= PARTICIPANTS {
        *shares.get_mut(&p).unwrap() += &iss_s[usize::from(sender - 1)].shares[&p];

        scalars.push(delta_square.clone());
        points.push(&iss_s[usize::from(sender - 1)].commitments[0].commitment);
        for (C_i, C) in iss_s[usize::from(sender - 1)].commitments[1 ..].iter().enumerate() {
          let C_i = C_i + 1;
          scalars.push(Natural::from(p).pow(u64::try_from(C_i).unwrap()));
          points.push(&C.commitment);
        }
      }
      verification_shares.insert(p, multiexp(&mut scalars, &points, &[]));
    }

    // TODO: Replace with a proven, decentralized flow
    let ec_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let k_ciphertext = cg
      .encrypt(
        &mut OsRng,
        &public_key_table,
        &Natural::from_digits_desc(&256, ec_key.to_repr().into_iter().map(u16::from)).unwrap(),
      )
      .1;
    let k_ciphertext_0 = k_ciphertext.0.large_table();
    let k_ciphertext_1 = k_ciphertext.1.large_table();
    let ec_key = <Secp256k1 as Ciphersuite>::generator() * ec_key;
    dbg!("Shimmed key gen");

    let mut segment_time = std::time::Instant::now();

    let commitment =
      |y_ciphertext: &Ciphertext, ky_ciphertext: &Ciphertext, xy_randomness: &Element| {
        let mut transcript = transcript();
        y_ciphertext.0.transcript(b"y_randomness", &mut transcript);
        y_ciphertext.1.transcript(b"y_message", &mut transcript);
        ky_ciphertext.0.transcript(b"ky_randomness", &mut transcript);
        ky_ciphertext.1.transcript(b"ky_message", &mut transcript);
        xy_randomness.transcript(b"xy_randomness", &mut transcript);
        transcript.challenge(b"commitment")
      };

    // Round 1: Publish additive shares of the nonce
    let mut x_is = vec![];
    let mut X_is = vec![];
    let mut x_i_ciphertexts = vec![];
    let mut y_i_full = vec![];
    let mut ky_i_full = vec![];
    let mut xy_i_randomnesses = vec![];
    let mut commitments = vec![];
    let mut r1_proofs = vec![];
    for _ in 0 .. THRESHOLD {
      let x_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      x_is.push(x_i);

      X_is.push(<Secp256k1 as Ciphersuite>::generator() * x_i);

      let (_, ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key_table,
        &x_i,
      );
      println!(
        "Proved for X_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
      r1_proofs.push(proof);
      x_i_ciphertexts.push(ciphertext);

      // The following are decided and committed to yet withheld
      let y_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      let y_i_uint =
        Natural::from_digits_desc(&256, y_i.to_repr().into_iter().map(u16::from)).unwrap();

      let (y_i_randomness, y_i_ciphertext) = cg.encrypt(&mut OsRng, &public_key_table, &y_i_uint);
      println!(
        "Encrypted Y_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();

      let ky_i_randomness = cg.sample_secret(&mut OsRng);
      let mut ky_i_ciphertext =
        Ciphertext(&k_ciphertext_0 * &y_i_uint, &k_ciphertext_1 * &y_i_uint);
      ky_i_ciphertext.0 = ky_i_ciphertext.0.add(&(cg.g_table() * &ky_i_randomness));
      ky_i_ciphertext.1 = ky_i_ciphertext.1.add(&(&public_key_table * &ky_i_randomness));
      println!(
        "Scaled k by y_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();

      let xy_i_randomness = cg.sample_secret(&mut OsRng);

      // Commit to the ciphertexts we can and the xy randomness (as we can't form the xy ciphertext
      // yet)
      // This prevents deciding randomness after seeing everyone else's and using Wagner's
      // algorithm to efficiently calculate randomnesses which will cause unintended encryptions
      let xy_i_commitment = cg.g_table() * &xy_i_randomness;
      commitments
        .push((commitment(&y_i_ciphertext, &ky_i_ciphertext, &xy_i_commitment), xy_i_commitment));

      y_i_full.push((y_i_uint, y_i_randomness, y_i_ciphertext));
      ky_i_full.push((ky_i_randomness, ky_i_ciphertext));
      xy_i_randomnesses.push(xy_i_randomness);

      println!(
        "Committed to further randomness: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
    }

    // Round 2
    let X = X_is.iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let r = <Secp256k1 as Ciphersuite>::F::from_repr(X.to_affine().x()).unwrap();

    // Everyone now calculates the sum nonce
    let mut x_ciphertext = x_i_ciphertexts[0].clone();
    for x_i_ciphertext in &x_i_ciphertexts[1 ..] {
      x_ciphertext = x_ciphertext.add_without_randomness(x_i_ciphertext);
    }
    let x_ciphertext_0 = x_ciphertext.0.small_table();
    let x_ciphertext_1 = x_ciphertext.1.small_table();
    println!(
      "Calculated X: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Perform multiplication of the sum nonce by our shares of y

    // For 2022-1437 5.2:
    // a = y randomness
    // b = xy randomness
    // c = ky randomness
    // ws = [a, b, c, y]
    // Ys = [..y_ciphertext, xy_randomness_commitment, ..xy_ciphertext, ..ky_ciphertext]
    // Xs = [
    //   [G,        Identity, Identity, Identity],
    //   [K,        Identity, Identity, F],
    //
    //   [Identity, G,        Identity, Identity],
    //   [Identity, G,        Identity, x_ciphertext.0],
    //   [Identity, K,        Identity, x_ciphertext.1],
    //
    //   [Identity, Identity, G,        k_ciphertext.0],
    //   [Identity, Identity, K,        k_ciphertext.1],
    // ]
    #[rustfmt::skip]
    let relations = [
      [cg.g_table().into(),        ElementOrTable::Identity,       ElementOrTable::Identity,   ElementOrTable::Identity],
      [(&public_key_table).into(), ElementOrTable::Identity,       ElementOrTable::Identity,   cg.f_table().into()],

      // TODO: The commitments almost certainly MUST be over a distinct generator
      [ElementOrTable::Identity,       cg.g_table().into(),        ElementOrTable::Identity,   ElementOrTable::Identity],
      [ElementOrTable::Identity,       cg.g_table().into(),        ElementOrTable::Identity,   (&x_ciphertext_0).into()],
      [ElementOrTable::Identity,       (&public_key_table).into(), ElementOrTable::Identity,   (&x_ciphertext_1).into()],

      [ElementOrTable::Identity,       ElementOrTable::Identity,   cg.g_table().into(),        (&k_ciphertext_0).into()],
      [ElementOrTable::Identity,       ElementOrTable::Identity,   (&public_key_table).into(), (&k_ciphertext_1).into()],
    ];

    let mut y_i_ciphertexts = vec![];
    let mut ky_i_ciphertexts = vec![];
    let mut xy_i_ciphertexts = vec![];
    let mut r2_proofs = vec![];
    for i in 0 .. usize::from(THRESHOLD) {
      let (y_i_uint, y_i_randomness, y_i_ciphertext) = y_i_full[i].clone();
      let (ky_i_randomness, ky_i_ciphertext) = ky_i_full[i].clone();
      let xy_i_randomness = xy_i_randomnesses[i].clone();

      let mut xy_i_ciphertext =
        Ciphertext(&x_ciphertext_0 * &y_i_uint, &x_ciphertext_1 * &y_i_uint);
      xy_i_ciphertext.0 = xy_i_ciphertext.0.add(&(cg.g_table() * &xy_i_randomness));
      xy_i_ciphertext.1 = xy_i_ciphertext.1.add(&(&public_key_table * &xy_i_randomness));
      println!(
        "Created xy_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();

      // Verify the hashed commitment
      assert_eq!(
        commitments[i].0,
        commitment(&y_i_ciphertext, &ky_i_ciphertext, &commitments[i].1,)
      );

      #[rustfmt::skip]
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        relations,
        [&y_i_randomness, &xy_i_randomness, &ky_i_randomness, &y_i_uint],
      );
      r2_proofs.push(proof);
      y_i_ciphertexts.push(y_i_ciphertext);
      xy_i_ciphertexts.push(xy_i_ciphertext);
      ky_i_ciphertexts.push(ky_i_ciphertext);
      println!(
        "Proved for y_i xy_i ky_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();
    }

    // Round 3
    // Technically, any threshold can perform this round, even if distinct from the prior used set
    let m1_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    {
      let mut verifier = BatchVerifier::new();
      for (i, proof) in r1_proofs.iter().enumerate() {
        proof
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            &public_key_table,
            &x_i_ciphertexts[i],
            X_is[i],
          )
          .unwrap();
      }
      for (i, proof) in r2_proofs.iter().enumerate() {
        #[rustfmt::skip]
        proof
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            // Assumes the ZkEncryptionProof randomness bound is <= this
            &cg.secret_bound(),
            relations,
            [
              &y_i_ciphertexts[i].0,
              &y_i_ciphertexts[i].1,

              &commitments[i].1,
              &xy_i_ciphertexts[i].0,
              &xy_i_ciphertexts[i].1,

              &ky_i_ciphertexts[i].0,
              &ky_i_ciphertexts[i].1,
            ],
          )
          .unwrap();
      }
      assert!(verifier.verify());
      println!(
        "Verified X_is, y_i xy_i ky_i ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();
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
    let dr_ciphertext = d_ciphertext.mul_without_randomness(
      &Natural::from_digits_desc(&256, r.to_repr().into_iter().map(u16::from)).unwrap(),
    );
    println!(
      "dr ciphertext calculation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Multiply y by H(m)
    let my_ciphertext = y_ciphertext.mul_without_randomness(
      &Natural::from_digits_desc(&256, m1_hash.to_repr().into_iter().map(u16::from)).unwrap(),
    );

    // dr_ciphertext is composed of d_ciphertext is ky ciphertexts
    // ky was commited to in round 1 and not revealed until round 2
    // r is static to the X ciphertexts from round 1
    // Accordingly, dr_ciphertext is safe to decrypt re: Wagner's
    //
    // The y ciphertext was committed to, yet `m` was only just decided and could be maliciously
    // In order to achieve concurrent security, one of three things is needed:
    // 1) An extra round to introduce new randomness
    // 2) The message has to be set at the start so it can't be post-decided
    // 3) Potentially, a binomial nonce scheme could be used
    // TODO
    let w_ciphertext = my_ciphertext.add_without_randomness(&dr_ciphertext);
    println!(
      "w ciphertext calculation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Publish the decryption shares for w and z
    // z can be decrypted in additional preprocess round if minimization of this round is desired
    let set: [u16; THRESHOLD as usize] = core::array::from_fn(|i| u16::try_from(i + 1).unwrap());
    let mut W_is = vec![];
    let mut Z_is = vec![];
    let mut r3_proofs = vec![];
    for i in 1u16 ..= THRESHOLD {
      // Calculate the literal shares
      let share_to_use = &shares[&i] * &delta;
      // The lagrange can be post-calculated so that the first `t` to publish shares for a
      // completed signature may be used together
      let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i, &set);
      let share_to_use = share_to_use * lagrange.clone().unsigned_abs();

      // If the lagrange (a publicly known coefficient) is negative, use the negative form of the
      // ciphertext's randomness element
      let w_ciphertext_neg = w_ciphertext.0.clone().neg();
      let w_ciphertext_base =
        if lagrange.sign() == Ordering::Greater { &w_ciphertext.0 } else { &w_ciphertext_neg };
      let W_i = w_ciphertext_base.mul(&share_to_use);
      let z_ciphertext_neg = z_ciphertext.0.clone().neg();
      let z_ciphertext_base =
        if lagrange.sign() == Ordering::Greater { &z_ciphertext.0 } else { &z_ciphertext_neg };
      let Z_i = z_ciphertext_base.mul(&share_to_use);

      // Prove the encryption shares are well-formed
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [[cg.g_table().into()], [w_ciphertext_base.into()], [z_ciphertext_base.into()]],
        [&share_to_use],
      );
      r3_proofs.push(proof);
      W_is.push(W_i);
      Z_is.push(Z_i);
      println!(
        "Calculated and proved for decryption shares: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
    }

    // Completion

    {
      let w_ciphertext_neg = w_ciphertext.0.clone().neg();
      let z_ciphertext_neg = z_ciphertext.0.clone().neg();

      let mut lagranges = vec![];
      let mut lagranged_shares = vec![];
      for i in 0 .. r3_proofs.len() {
        let i_u16 = u16::try_from(i + 1).unwrap();
        let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i_u16, &set);
        lagranged_shares.push(verification_shares[&i_u16].mul(&lagrange.clone().unsigned_abs()));
        lagranges.push(lagrange);
      }
      let mut verifier = BatchVerifier::new();
      for (i, proof) in r3_proofs.iter().enumerate() {
        let lagrange = &lagranges[i];
        let share_max_size = Natural::ONE <<
          (IntegerSecretSharing::share_size(&cg, THRESHOLD, PARTICIPANTS) +
            delta.significant_bits() +
            lagrange.significant_bits());

        let w_ciphertext_base =
          if lagrange.sign() == Ordering::Greater { &w_ciphertext.0 } else { &w_ciphertext_neg };
        let z_ciphertext_base =
          if lagrange.sign() == Ordering::Greater { &z_ciphertext.0 } else { &z_ciphertext_neg };

        // Verification of these can be delayed and only performed if an invalid signature is
        // produced
        proof
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            &share_max_size,
            [[cg.g_table().into()], [w_ciphertext_base.into()], [z_ciphertext_base.into()]],
            [&lagranged_shares[i], &W_is[i], &Z_is[i]],
          )
          .unwrap();
      }
      assert!(verifier.verify());
      println!(
        "Verified decryption shares (only necessary if signature creation fails): {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
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
    let delta_cubed = &delta * &delta * &delta;
    let value_scaled_by = &delta_cubed % cg.p();
    // Invert value_scaled_by over p
    let inverse = value_scaled_by.clone().mod_pow(&(cg.p() - Natural::from(2u8)), cg.p());
    debug_assert!(((&inverse * &value_scaled_by) % cg.p()) == Natural::ONE);

    let w = {
      let M = w_ciphertext.1.mul(&delta_cubed).add(&W.neg());
      (cg.solve(M).unwrap() * &inverse) % cg.p()
    };
    let z = {
      let M = z_ciphertext.1.mul(&delta_cubed).add(&Z.neg());
      (cg.solve(M).unwrap() * &inverse) % cg.p()
    };

    println!(
      "w and z decryption: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Create and publish the signature
    let s = ({
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      let w_bytes =
        w.to_digits_desc(&256u16).into_iter().map(|b| u8::try_from(b).unwrap()).collect::<Vec<_>>();
      bytes_ref[(32 - w_bytes.len()) ..].copy_from_slice(&w_bytes);
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    }) * ({
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      let z_bytes =
        z.to_digits_desc(&256u16).into_iter().map(|b| u8::try_from(b).unwrap()).collect::<Vec<_>>();
      bytes_ref[(32 - z_bytes.len()) ..].copy_from_slice(&z_bytes);
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
