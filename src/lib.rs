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
  c: <Secp256k1 as Ciphersuite>::F,
  R: <Secp256k1 as Ciphersuite>::G,
  s: <Secp256k1 as Ciphersuite>::F,
) {
  // s = r + cx
  // sG = R + cX

  assert_eq!(<Secp256k1 as Ciphersuite>::generator() * s, R + (public_key * c));
}

#[cfg(test)]
mod tests {
  use core::cmp::Ordering;

  use rand_core::OsRng;

  use crypto_bigint::*;
  use ciphersuite::group::ff::Field;

  use super::*;

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
    let ec_key = <Secp256k1 as Ciphersuite>::generator() * ec_key;
    dbg!("Shimmed key gen");

    let mut segment_time = std::time::Instant::now();

    // Round 1: Publish additive shares of each nonce
    let mut nonce1_i_points = vec![];
    let mut nonce2_i_points = vec![];
    let mut nonce1_i_ciphertexts = vec![];
    let mut nonce2_i_ciphertexts = vec![];
    let mut proofs = vec![];
    for _ in 0 .. THRESHOLD {
      let nonce1_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      let nonce2_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

      nonce1_i_points.push(<Secp256k1 as Ciphersuite>::generator() * nonce1_i);
      nonce2_i_points.push(<Secp256k1 as Ciphersuite>::generator() * nonce2_i);

      let (_, ciphertext1, proof1) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key_table,
        &nonce1_i,
      );
      let (_, ciphertext2, proof2) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key_table,
        &nonce2_i,
      );
      proofs.push((proof1, proof2));
      nonce1_i_ciphertexts.push(ciphertext1);
      nonce2_i_ciphertexts.push(ciphertext2);
      println!(
        "Proved nonces: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
    }

    // Round 2

    // Verify proofs from prior round
    {
      let mut verifier = BatchVerifier::new();
      for (i, (proof1, proof2)) in proofs.iter().enumerate() {
        proof1
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            &public_key_table,
            &nonce1_i_ciphertexts[i],
            nonce1_i_points[i],
          )
          .unwrap();
        proof2
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            &public_key_table,
            &nonce2_i_ciphertexts[i],
            nonce2_i_points[i],
          )
          .unwrap();
      }
      assert!(verifier.verify());
      println!(
        "Verified nonce ciphertexts: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis(),
      );
      segment_time = std::time::Instant::now();
    }

    // Decide challenge, binding factor
    // This should be the HRAm
    let c = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    // This should be a hash of the entire context, ideally as specified in the IETF draft + all of
    // the ciphertexts specified thus far
    let binding = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    // Everyone now calculates the sum nonce
    let nonce1 = nonce1_i_points.iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let nonce2 = nonce2_i_points.iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let R = nonce1 + (nonce2 * binding);

    let mut nonce1_ciphertext = nonce1_i_ciphertexts[0].clone();
    for nonce1_i_ciphertext in &nonce1_i_ciphertexts[1 ..] {
      nonce1_ciphertext = nonce1_ciphertext.add_without_randomness(&nonce1_i_ciphertext);
    }
    let mut nonce2_ciphertext = nonce2_i_ciphertexts[0].clone();
    for nonce2_i_ciphertext in &nonce2_i_ciphertexts[1 ..] {
      nonce2_ciphertext = nonce2_ciphertext.add_without_randomness(&nonce2_i_ciphertext);
    }
    let nonce_ciphertext =
      nonce1_ciphertext.add_without_randomness(&nonce2_ciphertext.mul_without_randomness(
        &Natural::from_digits_desc(&256, binding.to_repr().into_iter().map(u16::from)).unwrap(),
      ));
    println!(
      "Calculated nonces: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Everyone now calculates r + cx
    let s_ciphertext =
      nonce_ciphertext.add_without_randomness(&k_ciphertext.mul_without_randomness(
        &Natural::from_digits_desc(&256, c.to_repr().into_iter().map(u16::from)).unwrap(),
      ));

    println!("s: {}", std::time::Instant::now().duration_since(segment_time).as_millis());
    segment_time = std::time::Instant::now();

    // Publish the decryption shares for s
    let set: [u16; THRESHOLD as usize] = core::array::from_fn(|i| u16::try_from(i + 1).unwrap());
    let mut S_is = vec![];
    let mut proofs = vec![];
    for i in 1u16 ..= THRESHOLD {
      // Calculate the literal shares
      let share_to_use = &shares[&i] * &delta;
      // The lagrange can be post-calculated so that the first `t` to publish shares for a
      // completed signature may be used together
      let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i, &set);
      let share_to_use = share_to_use * lagrange.clone().unsigned_abs();

      // If the lagrange (a publicly known coefficient) is negative, use the negative form of the
      // ciphertext's randomness element
      let s_ciphertext_neg = s_ciphertext.0.clone().neg();
      let s_ciphertext_base =
        if lagrange.sign() == Ordering::Greater { &s_ciphertext.0 } else { &s_ciphertext_neg };
      let S_i = s_ciphertext_base.mul(&share_to_use);

      // Prove the encryption shares are well-formed
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [[cg.g_table().into()], [s_ciphertext_base.into()]],
        [&share_to_use],
      );
      proofs.push(proof);
      S_is.push(S_i);
      println!(
        "Calculated and proved for decryption share: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
    }

    // Completion

    {
      let s_ciphertext_neg = s_ciphertext.0.clone().neg();

      let mut lagranges = vec![];
      let mut lagranged_shares = vec![];
      for i in 0 .. proofs.len() {
        let i_u16 = u16::try_from(i + 1).unwrap();
        let lagrange = IntegerSecretSharing::lagrange(PARTICIPANTS, i_u16, &set);
        lagranged_shares.push(verification_shares[&i_u16].mul(&lagrange.clone().unsigned_abs()));
        lagranges.push(lagrange);
      }
      let mut verifier = BatchVerifier::new();
      for (i, proof) in proofs.iter().enumerate() {
        let lagrange = &lagranges[i];
        let share_max_size = Natural::ONE <<
          (IntegerSecretSharing::share_size(&cg, THRESHOLD, PARTICIPANTS) +
            delta.significant_bits() +
            lagrange.significant_bits());

        let s_ciphertext_base =
          if lagrange.sign() == Ordering::Greater { &s_ciphertext.0 } else { &s_ciphertext_neg };

        // Verification of these can be delayed and only performed if an invalid signature is
        // produced
        proof
          .verify(
            &cg,
            &mut verifier,
            &mut transcript(),
            &share_max_size,
            [[cg.g_table().into()], [s_ciphertext_base.into()]],
            [&lagranged_shares[i], &S_is[i]],
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
    let mut S = S_is.pop().unwrap();
    for S_i in &S_is {
      S = S.add(S_i);
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

    let s = {
      let M = s_ciphertext.1.mul(&delta_cubed).add(&S.neg());
      (cg.solve(M).unwrap() * &inverse) % cg.p()
    };

    println!(
      "s decryption: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Create and publish the signature
    let s = {
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      let s_bytes =
        s.to_digits_desc(&256u16).into_iter().map(|b| u8::try_from(b).unwrap()).collect::<Vec<_>>();
      bytes_ref[(32 - s_bytes.len()) ..].copy_from_slice(&s_bytes);
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    };

    println!(
      "Signature creation: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    // segment_time = std::time::Instant::now();

    verify(ec_key, c, R, s);
  }
}
