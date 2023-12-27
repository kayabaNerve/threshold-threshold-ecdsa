use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_safe_prime_with_rng;

use num_traits::*;
use num_bigint::*;

use transcript::Transcript;

use crate::class_group::*;

// https://eprint.iacr.org/2021/205 Algorithm 2
#[allow(non_snake_case)]
pub struct ZkDlogWithoutSubgroupProof {
  R: Element,
  D: Element,
  e: BigUint,
  Q: Element,
  r: BigUint,
}

impl ZkDlogWithoutSubgroupProof {
  #[allow(non_snake_case)]
  fn transcript_R(cg: &ClassGroup, transcript: &mut impl Transcript, R: &Element) -> BigUint {
    transcript.domain_separate(b"ZkDlogWithoutSubgroupProof");
    R.transcript(b"R", transcript);
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

  #[allow(non_snake_case)]
  fn transcript_De(transcript: &mut impl Transcript, D: &Element, e: &BigUint) -> BigUint {
    D.transcript(b"D", transcript);
    transcript.append_message(b"e", e.to_bytes_be());

    // The soundness error is 1/2**(bits - log2 bits), so a 136 bit prime should be fine for the
    // targetted 128-bits of security
    assert_eq!(Uint::<{ 256 / 64 }>::BITS, 256);
    // TODO: Does crypto-primes guarantee a uniform distribution? As-current, it iterates from a
    // random starting point when using generate_prime (generate_safe_prime is distinct regarding
    // its pattern) which doesn't guarantee true uniformity.
    // https://github.com/entropyxyz/crypto-primes/issues/23 for the relevant issue
    let l = generate_prime_with_rng::<{ 256 / 64 }>(
      &mut ChaCha20Rng::from_seed(transcript.rng_seed(b"l")),
      None,
    );
    BigUint::from_bytes_be(l.to_be_bytes().as_ref())
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    x: &BigUint,
  ) -> ZkDlogWithoutSubgroupProof {
    let k = cg.sample_secret(rng);
    // k is intended to be sampled from [-B, B]. We achieve -B sampling by potentially negating `g`
    // If this is moved off `g`, we MUST transcript g
    let neg_g = cg.g().clone().neg();
    #[allow(non_snake_case)]
    let R = (if (rng.next_u64() % 2) == 1 { cg.g() } else { &neg_g }).mul(&k);

    let c = Self::transcript_R(cg, transcript, &R);

    let s = k + (&c * x);
    let (d, e) = (s.div_euclid(cg.p()), s.rem_euclid(cg.p()));
    #[allow(non_snake_case)]
    let D = cg.g().mul(&d);

    let l = Self::transcript_De(transcript, &D, &e);
    let (q, r) = (s.div_euclid(&l), s.rem_euclid(&l));
    #[allow(non_snake_case)]
    let Q = cg.g().mul(&q);

    ZkDlogWithoutSubgroupProof { R, D, e, Q, r }
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    w: &Element,
  ) -> Result<(), ()> {
    let c = Self::transcript_R(cg, transcript, &self.R);
    if self.e >= *cg.p() {
      Err(())?
    }
    #[allow(non_snake_case)]
    let Rwc = self.R.add(&w.mul(&c));
    if self.D.mul(cg.p()).add(&cg.g().mul(&self.e)) != Rwc {
      Err(())?
    }
    let l = Self::transcript_De(transcript, &self.D, &self.e);
    if self.r >= l {
      Err(())?
    }
    if self.Q.mul(&l).add(&cg.g().mul(&self.r)) != Rwc {
      Err(())?
    }
    Ok(())
  }
}
