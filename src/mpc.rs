use std::collections::HashMap;

use rand_core::{RngCore, CryptoRng};

use num_traits::One;
use num_bigint::{Sign, BigUint, BigInt};

use transcript::Transcript;

use crate::{class_group::*, proofs::*};

pub struct CommitmentWithProof {
  pub(crate) commitment: Element,
  proof: ZkDlogOutsideSubgroupProof,
}

impl CommitmentWithProof {
  pub fn new(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    dlog: &BigUint,
  ) -> Self {
    let commitment = cg.g().mul(dlog);
    let proof = ZkDlogOutsideSubgroupProof::prove(rng, cg, transcript, dlog);
    Self { commitment, proof }
  }
  #[allow(clippy::result_unit_err)]
  pub fn verify(&self, cg: &ClassGroup, transcript: &mut impl Transcript) -> Result<(), ()> {
    self.proof.verify(cg, transcript, &self.commitment)
  }
}

// TODO: Review the impact of 2022-1437 Remark 7 on the below
pub struct IntegerSecretSharing {
  pub(crate) delta: BigUint,
  pub(crate) commitments: Vec<CommitmentWithProof>,
  pub(crate) shares: HashMap<u16, BigUint>,
}
impl IntegerSecretSharing {
  fn delta(n: u16) -> BigUint {
    let mut accum = BigUint::one();
    for i in 2 ..= n {
      accum *= i;
    }
    accum
  }
  pub fn new(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    t: u16,
    n: u16,
  ) -> IntegerSecretSharing {
    let mut gen_coefficient = || {
      // TODO: This uses the same size for all coefficients
      // 2022-1437 distinguishes secret size and coefficient size.
      let secret_bits = cg.secret_bits() - 1;
      let mut secret = vec![0; secret_bits.div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut secret);
      secret[0] &= 0xff >> (8 - (secret_bits % 8));
      BigUint::from_bytes_be(&secret)
    };

    let alpha = gen_coefficient();
    let delta = Self::delta(n);
    let alpha_tilde = &alpha * &delta;

    let mut r = vec![];
    for _ in 1 ..= (t - 1) {
      r.push(gen_coefficient());
    }

    let f = |i: u16| {
      &alpha_tilde +
        r.iter()
          .enumerate()
          .map(|(r_i, r)| r * i.pow((r_i + 1).try_into().unwrap()))
          .sum::<BigUint>()
    };

    let mut y = HashMap::new();
    for i in 1 ..= n {
      y.insert(i, f(i));
    }

    // The paper specifies to prove all are valid such as via DLog proofs, yet the later proof only
    // requires the first element have a known DLog for the prover. Can a PedPoP-esque approach be
    // taken to remove the additional proofs? (TODO)
    #[allow(non_snake_case)]
    let mut commitments = vec![];
    commitments.push(CommitmentWithProof::new(rng, cg, transcript, &alpha));
    for r in &r {
      commitments.push(CommitmentWithProof::new(rng, cg, transcript, &(r * &delta)));
    }

    #[cfg(test)]
    for (i, y) in &y {
      let mut eval = commitments[0].commitment.mul(&(&delta * &delta));
      #[allow(non_snake_case)]
      for (C_i, C) in commitments[1 ..].iter().enumerate() {
        let C_i = C_i + 1;
        let i = BigUint::from(*i);
        eval = eval.add(&C.commitment.mul(&i.pow(u32::try_from(C_i).unwrap())));
      }
      assert_eq!(cg.g().mul(&(y * &delta)), eval);
    }

    IntegerSecretSharing { delta, commitments, shares: y }
  }

  pub fn lagrange(n: u16, i: u16, set: &[u16]) -> BigInt {
    let mut numerator = Self::delta(n);
    let mut denominator = BigInt::one();
    for j in set {
      let j = *j;
      if i == j {
        continue;
      }
      numerator *= j;
      denominator *= i32::from(j) - i32::from(i);
    }
    let numerator = BigInt::from_biguint(Sign::Plus, numerator);
    numerator / denominator
  }
}

#[test]
fn integer_secret_sharing() {
  use rand_core::OsRng;
  use transcript::RecommendedTranscript;

  use num_traits::{Zero, FromBytes};

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let transcript = || RecommendedTranscript::new(b"Integer Secret Sharing Test");
  let iss = IntegerSecretSharing::new(&mut OsRng, &cg, &mut transcript(), 3, 4);

  let mut reconstructed = BigInt::zero();
  let set = [1u16, 2, 4];
  for i in set {
    reconstructed += BigInt::from_biguint(Sign::Plus, iss.shares[&i].clone()) *
      IntegerSecretSharing::lagrange(4, i, &set);
  }
  assert_eq!(
    cg.g().mul(&reconstructed.to_biguint().unwrap()),
    iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta))
  );
}