use std::collections::HashMap;

use rand_core::{RngCore, CryptoRng};

use malachite::{
  num::{basic::traits::*, arithmetic::traits::*, logic::traits::*, conversion::traits::*},
  *,
};

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
    dlog: &Natural,
  ) -> Self {
    let (commitment, proof) = ZkDlogOutsideSubgroupProof::prove(rng, cg, transcript, dlog);
    Self { commitment, proof }
  }
  #[allow(clippy::result_unit_err)]
  pub fn verify<'a>(
    &'a self,
    cg: &'a ClassGroup,
    verifier: &mut BatchVerifier<'a>,
    transcript: &mut impl Transcript,
  ) -> Result<(), ()> {
    self.proof.verify(cg, verifier, transcript, &self.commitment)
  }
}

// TODO: Review the impact of 2022-1437 Remark 7 on the below
pub struct IntegerSecretSharing {
  pub(crate) delta: Natural,
  pub(crate) commitments: Vec<CommitmentWithProof>,
  pub(crate) shares: HashMap<u16, Natural>,
}
impl IntegerSecretSharing {
  fn delta(n: u16) -> Natural {
    Natural::factorial(n.into())
  }

  pub(crate) fn share_size(cg: &ClassGroup, t: u16, n: u16) -> u64 {
    let delta = Self::delta(n);
    // alpha is shared as alpha * delta
    let alpha_bits = cg.p().significant_bits() + delta.significant_bits();
    let coefficient_bits =
      cg.p().significant_bits() + (&delta * Natural::from(t)).significant_bits() + 2;
    // Coefficients have a factor of the following length
    let coefficient_factor_bits = Natural::from(n).pow(n.into()).significant_bits();
    alpha_bits + ((coefficient_bits + coefficient_factor_bits) * u64::from(t - 1))
  }

  pub fn new(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    t: u16,
    n: u16,
  ) -> IntegerSecretSharing {
    let delta = Self::delta(n);
    // 2022-1437 distinguishes secret size and coefficient size.
    // For alpha, it should be from the distribution Dq.
    let alpha = crate::sample_number_less_than(&mut *rng, cg.p());
    let alpha_tilde = &alpha * &delta;

    // For the coefficient, the security proof requires the size be l + log2(hmax * t) + 1.
    // This is interpreted as ceil(log2(Dq)) + log2(2 * delta * t) + 1.
    // TODO: Double check this.
    let secret_bits =
      cg.p().significant_bits() + (&delta * Natural::from(t)).significant_bits() + 2;
    let mut gen_coefficient = || {
      let mut secret = vec![0; secret_bits.div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut secret);
      secret[0] &= 0xff >> (8 - (secret_bits % 8));
      Natural::from_digits_desc(&256, secret.into_iter().map(u16::from)).unwrap()
    };

    let mut r = vec![];
    for _ in 1 ..= (t - 1) {
      r.push(gen_coefficient());
    }

    let f = |i: u16| {
      &alpha_tilde +
        r.iter()
          .enumerate()
          .map(|(r_i, r)| r * Natural::from(i).pow((r_i + 1).try_into().unwrap()))
          .sum::<Natural>()
    };

    let mut y = HashMap::new();
    for i in 1 ..= n {
      y.insert(i, f(i));
    }

    // The paper specifies to prove all are valid such as via DLog proofs, yet the later proof only
    // requires the first element have a known DLog for the prover. Can a PedPoP-esque approach be
    // taken to remove the additional proofs? (TODO)
    let mut commitments = vec![];
    commitments.push(CommitmentWithProof::new(rng, cg, transcript, &alpha));
    for r in &r {
      commitments.push(CommitmentWithProof::new(rng, cg, transcript, &(r * &delta)));
    }

    #[cfg(debug_assertions)]
    let delta_squared = delta.clone().pow(2);
    #[cfg(debug_assertions)]
    for (i, y) in &y {
      let i = Natural::from(*i);
      let mut eval = commitments[0].commitment.mul(&delta_squared);
      for (C_i, C) in commitments[1 ..].iter().enumerate() {
        let C_i = C_i + 1;
        eval = eval.add(&C.commitment.mul(&i.clone().pow(u64::try_from(C_i).unwrap())));
      }
      debug_assert_eq!(cg.g_table() * &(y * &delta), eval);
    }

    IntegerSecretSharing { delta, commitments, shares: y }
  }

  pub fn lagrange(n: u16, i: u16, set: &[u16]) -> Integer {
    let mut numerator = Self::delta(n);
    let mut denominator = Integer::ONE;
    for j in set {
      let j = *j;
      if i == j {
        continue;
      }
      numerator *= Natural::from(j);
      denominator *= Integer::from(i32::from(j) - i32::from(i));
    }
    let numerator = Integer::from(numerator);
    numerator / denominator
  }
}

#[test]
fn integer_secret_sharing() {
  use rand_core::OsRng;
  use transcript::RecommendedTranscript;

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod =
    Natural::from_digits_desc(&256, secp256k1_mod.into_iter().map(u16::from)).unwrap();

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let transcript = || RecommendedTranscript::new(b"Integer Secret Sharing Test");
  let iss = IntegerSecretSharing::new(&mut OsRng, &cg, &mut transcript(), 3, 4);

  let mut reconstructed = Integer::ZERO;
  let set = [1u16, 2, 4];
  for i in set {
    reconstructed +=
      Integer::from(iss.shares[&i].clone()) * IntegerSecretSharing::lagrange(4, i, &set);
  }
  assert_eq!(
    cg.g_table() * &Natural::try_from(reconstructed).unwrap(),
    iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta))
  );
}
