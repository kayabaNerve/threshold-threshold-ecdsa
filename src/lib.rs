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
    let _public_key_table = public_key.large_table();

    let mut k_is = HashMap::new();
    for i in 1u16 ..= PARTICIPANTS {
      k_is.insert(i, Natural::ZERO);
    }
    let mut verification_shares = HashMap::new();
    for p in 1u16 ..= PARTICIPANTS {
      println!("Accumulating shares for {p}");
      let mut scalars = vec![];
      let mut points = vec![];
      for sender in 1u16 ..= PARTICIPANTS {
        *k_is.get_mut(&p).unwrap() += &iss_s[usize::from(sender - 1)].shares[&p];

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

    // TODO: Use hash to points here
    let A = (cg.g_table() * &cg.sample_secret(&mut OsRng)).large_table();
    let B = (cg.g_table() * &cg.sample_secret(&mut OsRng)).large_table();

    let set: [u16; THRESHOLD as usize] = core::array::from_fn(|i| u16::try_from(i + 1).unwrap());

    // TODO: Replace with a proven, decentralized flow
    let ec_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let mut P_ciphertext = cg.f_table() *
      &Natural::from_digits_desc(&256, ec_key.to_repr().into_iter().map(u16::from)).unwrap();
    for i in 1 ..= THRESHOLD {
      let k_i_interpolated = &k_is[&i] * &delta;
      let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i, &set);
      let k_i_interpolated = k_i_interpolated * lagrange.clone().unsigned_abs();

      let mut share = &A * &k_i_interpolated;
      if lagrange.sign() == Ordering::Less {
        share = share.neg();
      }
      P_ciphertext = P_ciphertext.add(&share);
    }
    let P_ciphertext = P_ciphertext.large_table();
    let ec_key = <Secp256k1 as Ciphersuite>::generator() * ec_key;
    dbg!("Shimmed key gen");

    let mut segment_time = std::time::Instant::now();

    // Round 1: Publish additive shares of the nonce and y commitments
    let mut r_x_is = vec![];
    let mut X_is = vec![];
    let mut X_i_ciphertexts = vec![];
    let mut x_proofs = vec![];

    let mut y_is = vec![];
    let mut y_A_is = vec![];
    let mut y_B_is = vec![];
    let mut y_proofs = vec![];
    for _ in 0 .. THRESHOLD {
      {
        let x_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
        X_is.push(<Secp256k1 as Ciphersuite>::generator() * x_i);

        let (r_x_i, ciphertext, proof) =
          ZkEncryptionProof::<Secp256k1>::prove(&mut OsRng, &cg, &mut transcript(), &B, &x_i);
        r_x_is.push(r_x_i);
        // Transmit the full ciphertext for the rG component, as needed for the proof
        // TODO: Create a proof without such an element?
        X_i_ciphertexts.push(ciphertext);
        x_proofs.push(proof);
        println!(
          "Proved for X_i: {}",
          std::time::Instant::now().duration_since(segment_time).as_millis()
        );
        segment_time = std::time::Instant::now();
      }

      {
        let y_i = cg.sample_secret(&mut OsRng);

        let proof = ZkRelationProof::prove(
          &mut OsRng,
          &cg,
          &mut transcript(),
          [[(&A).into()], [(&B).into()]],
          [&y_i],
        );
        y_A_is.push(&A * &y_i);
        y_B_is.push(&B * &y_i);
        y_is.push(y_i);
        y_proofs.push(proof);
        println!(
          "Proved for y_A_i, y_B_i: {}",
          std::time::Instant::now().duration_since(segment_time).as_millis(),
        );
        segment_time = std::time::Instant::now();
      }
    }

    // Verify prior proofs (x_proofs and y_proofs)
    let mut verifier = BatchVerifier::new();
    for (i, proof) in x_proofs.iter().enumerate() {
      proof
        .verify(&cg, &mut verifier, &mut transcript(), &B, &X_i_ciphertexts[i], X_is[i])
        .unwrap();
    }
    for (i, proof) in y_proofs.iter().enumerate() {
      proof
        .verify(
          &cg,
          &mut verifier,
          &mut transcript(),
          &cg.secret_bound(),
          [[(&A).into()], [(&B).into()]],
          [&y_A_is[i], &y_B_is[i]],
        )
        .unwrap();
    }
    assert!(verifier.verify());
    println!(
      "Verified everyones' y_A_is, y_B_is: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis(),
    );
    segment_time = std::time::Instant::now();

    // Round 2
    let X = X_is.iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let mut X_ciphertext = X_i_ciphertexts[0].clone().1;
    for X_i_ciphertext in &X_i_ciphertexts[1 ..] {
      X_ciphertext = X_ciphertext.add(&X_i_ciphertext.1);
    }
    let r_scalar = <Secp256k1 as Ciphersuite>::F::from_repr(X.to_affine().x()).unwrap();
    let r = Natural::from_digits_desc(&256, r_scalar.to_repr().into_iter().map(u16::from)).unwrap();
    println!(
      "Calculated X and r: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    let mut y_A = y_A_is[0].clone();
    for y_A_i in &y_A_is[1 ..] {
      y_A = y_A.add(y_A_i);
    }
    let mut y_B = y_B_is[0].clone();
    for y_B_i in &y_B_is[1 ..] {
      y_B = y_B.add(y_B_i);
    }
    println!(
      "Calculated y_A and y_B: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    let message = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let N = (P_ciphertext * &r).add(
      &(cg.f_table() *
        &Natural::from_digits_desc(&256, message.to_repr().into_iter().map(u16::from)).unwrap()),
    );

    let mut N_is = vec![];
    let mut R_N_is = vec![];
    let mut D_is = vec![];
    let mut R_D_is = vec![];
    let mut num_denom_proofs = vec![];
    for i in 1 ..= THRESHOLD {
      // Calculate the literal shares
      let k_i_interpolated = &k_is[&i] * &delta;
      let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i, &set);
      let k_i_interpolated = k_i_interpolated * lagrange.clone().unsigned_abs();

      N_is.push(N.mul(&y_is[usize::from(i - 1)]));
      let mut R_N_i = y_A.mul(&(&r * &k_i_interpolated));
      if lagrange.sign() == Ordering::Less {
        R_N_i = R_N_i.neg();
      }
      R_N_is.push(R_N_i);

      D_is.push(X_ciphertext.mul(&y_is[usize::from(i - 1)]));
      R_D_is.push(y_B.mul(&r_x_is[usize::from(i - 1)]));

      println!(
        "Calculated N_i, R_N_i, D_i, R_D_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();

      // Prove the above
      #[rustfmt::skip]
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [
          // y_A_i, N_i, D_i
          [(&A).into(),            cg.identity().into(),    cg.identity().into()],
          [(&N).into(),            cg.identity().into(),    cg.identity().into()],
          [(&X_ciphertext).into(), cg.identity().into(),    cg.identity().into()],
          // R_N_i, interpolated verification share
          [cg.identity().into(),   (&(y_A.mul(&r))).into(), cg.identity().into()],
          [cg.identity().into(),   cg.g_table().into(),     cg.identity().into()],
          // X_i_ciphertexts[i].0, R_D_i
          [cg.identity().into(),   cg.identity().into(),    cg.g_table().into()],
          [cg.identity().into(),   cg.identity().into(),    (&y_B).into()],
        ],
        [&y_is[usize::from(i - 1)], &k_i_interpolated, &r_x_is[usize::from(i - 1)]],
      );
      num_denom_proofs.push(proof);
      println!(
        "Proved for N_i, R_N_i, D_i, R_D_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
    }

    // Verify the numerator and denominator variables
    // This can be delayed until after the signature fails to verify, and skipped if it verifies
    let mut verifier = BatchVerifier::new();
    let y_A_r = y_A.mul(&r);

    let mut lagranges = vec![];
    let mut lagranged_shares = vec![];
    let mut proof_R_N_is = vec![];
    for i in 0 .. num_denom_proofs.len() {
      let lagrange =
        IntegerSecretSharing::lagrange(PARTICIPANTS, u16::try_from(i + 1).unwrap(), &set);
      let mut proof_R_N_i = R_N_is[i].clone();
      let verification_share =
        verification_shares[&u16::try_from(i + 1).unwrap()].mul(&lagrange.clone().unsigned_abs());
      if lagrange.sign() == Ordering::Less {
        proof_R_N_i = proof_R_N_i.neg();
      }
      lagranges.push(lagrange);
      lagranged_shares.push(verification_share);
      proof_R_N_is.push(proof_R_N_i);
    }

    for (i, proof) in num_denom_proofs.iter().enumerate() {
      let share_max_size = Natural::ONE <<
        (IntegerSecretSharing::share_size(&cg, THRESHOLD, PARTICIPANTS) +
          delta.significant_bits() +
          lagranges[i].significant_bits());

      #[rustfmt::skip]
      proof
        .verify(
          &cg,
          &mut verifier,
          &mut transcript(),
          &share_max_size.max(cg.secret_bound()),
          [
            // y_A_i, N_i, D_i
            [(&A).into(),            cg.identity().into(), cg.identity().into()],
            [(&N).into(),            cg.identity().into(), cg.identity().into()],
            [(&X_ciphertext).into(), cg.identity().into(), cg.identity().into()],
            // R_N_i, interpolated verification share
            [cg.identity().into(),   (&y_A_r).into(),      cg.identity().into()],
            [cg.identity().into(),   cg.g_table().into(),  cg.identity().into()],
            // X_i_ciphertexts[i].0, R_D_i
            [cg.identity().into(),   cg.identity().into(), cg.g_table().into()],
            [cg.identity().into(),   cg.identity().into(), (&y_B).into()],
          ],
          [
            &y_A_is[i], &N_is[i], &D_is[i],
            &proof_R_N_is[i], &lagranged_shares[i],
            &X_i_ciphertexts[i].0, &R_D_is[i],
          ],
        )
        .unwrap();
    }
    assert!(verifier.verify());
    println!(
      "Verified everyones' numerator/denominator variables: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis(),
    );
    segment_time = std::time::Instant::now();

    // Completion
    let mut N = N_is[0].clone();
    for N_i in &N_is[1 ..] {
      N = N.add(N_i);
    }
    let mut R_N = R_N_is[0].clone();
    for R_N_i in &R_N_is[1 ..] {
      R_N = R_N.add(R_N_i);
    }
    let mut D = D_is[0].clone();
    for D_i in &D_is[1 ..] {
      D = D.add(D_i);
    }
    let mut R_D = R_D_is[0].clone();
    for R_D_i in &R_D_is[1 ..] {
      R_D = R_D.add(R_D_i);
    }
    println!(
      "Summed ciphertexts and decryption shares: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    let n = cg.solve(N.add(&R_N.neg())).unwrap() % cg.p();
    let d = cg.solve(D.add(&R_D.neg())).unwrap() % cg.p();
    println!(
      "n and d decryption: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    let to_scalar = |number: Natural| {
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      let number_bytes = number
        .to_digits_desc(&256u16)
        .into_iter()
        .map(|b| u8::try_from(b).unwrap())
        .collect::<Vec<_>>();
      bytes_ref[(32 - number_bytes.len()) ..].copy_from_slice(&number_bytes);
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    };

    // Create and publish the signature
    let s = to_scalar(n) * to_scalar(d).invert().unwrap();
    println!(
      "Signature creation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    // segment_time = std::time::Instant::now();

    verify(ec_key, message, r_scalar, s);
  }
}
