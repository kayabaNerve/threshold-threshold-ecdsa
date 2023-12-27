use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_prime_with_rng;

use num_traits::*;
use num_bigint::*;

use transcript::Transcript;

use crate::class_group::*;

// https://eprint.iacr.org/2021/205 Algorithm 2
#[allow(non_snake_case)]
pub struct ZkDlogOutsideSubgroupProof {
  R: Element,
  D: Element,
  e: BigUint,
  Q: Element,
  r: BigUint,
}

impl ZkDlogOutsideSubgroupProof {
  #[allow(non_snake_case)]
  fn transcript_R(cg: &ClassGroup, transcript: &mut impl Transcript, R: &Element) -> BigUint {
    transcript.domain_separate(b"ZkDlogOutsideSubgroupProof");
    R.transcript(b"R", transcript);
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

  #[allow(non_snake_case)]
  fn transcript_De(transcript: &mut impl Transcript, D: &Element, e: &BigUint) -> BigUint {
    D.transcript(b"D", transcript);
    transcript.append_message(b"e", e.to_bytes_be());

    // The soundness error is 1/2**(bits - log2 bits), so a 136 bit prime should be fine for the
    // targeted 128-bits of security
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
  ) -> Self {
    // k is intended to be sampled from [-B, B]. We reduce the space by half yet don't sample from
    // -B as we can't calculate negatives over a field of unknown order (which has implications
    // later when s is calculated)
    let k = cg.sample_secret(rng);
    // If this is moved off `g`, we MUST transcript the g used
    #[allow(non_snake_case)]
    let R = cg.g().mul(&k);

    let c = Self::transcript_R(cg, transcript, &R);

    let s = k + (&c * x);
    let (d, e) = (s.div_euclid(cg.p()), s.rem_euclid(cg.p()));
    #[allow(non_snake_case)]
    let D = cg.g().mul(&d);

    let l = Self::transcript_De(transcript, &D, &e);
    let (q, r) = (s.div_euclid(&l), s.rem_euclid(&l));
    #[allow(non_snake_case)]
    let Q = cg.g().mul(&q);

    ZkDlogOutsideSubgroupProof { R, D, e, Q, r }
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

// https://eprint.iacr.org/2021/205 Algorithm 5
#[allow(non_snake_case)]
pub struct ZkEncryptionProof {
  S1: Element,
  S2: Element,
  u_m: BigUint,
  D1: Element,
  D2: Element,
  e_r: BigUint,
  Q1: Element,
  Q2: Element,
  r_r: BigUint,
}

impl ZkEncryptionProof {
  #[allow(non_snake_case)]
  fn transcript_Ss(
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    S1: &Element,
    S2: &Element,
  ) -> BigUint {
    transcript.domain_separate(b"ZkEncryptionProof");
    S1.transcript(b"S1", transcript);
    S2.transcript(b"S2", transcript);
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

  #[allow(non_snake_case)]
  fn transcript_u_Ds_e(
    transcript: &mut impl Transcript,
    u: &BigUint,
    D1: &Element,
    D2: &Element,
    e: &BigUint,
  ) -> BigUint {
    transcript.append_message(b"u", u.to_bytes_be());
    D1.transcript(b"D1", transcript);
    D2.transcript(b"D2", transcript);
    transcript.append_message(b"e", e.to_bytes_be());

    // The soundness error is 1/2**(bits - log2 bits), so a 136 bit prime should be fine for the
    // targeted 128-bits of security
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
    public_key: &Element,
    message: &BigUint,
  ) -> (Ciphertext, Self) {
    // TODO: This randomness is sampled over Bp yet our proof is for p over B * 2**128.
    // Is this okay?
    let (randomness, ciphertext) = cg.encrypt(rng, public_key, message);
    // Increases statistical distance tolerance from 1/(2**80) to 1/(2**128)
    // TODO: Check this does actually do that as intended
    #[allow(non_snake_case)]
    let B_2_exp = 128 + 128 + 2;
    // The bound B (of the class group) is labeled s (accented) by 2021-205 and used to define its
    // own B
    #[allow(non_snake_case)]
    let B = (BigUint::one() << B_2_exp) * cg.bound();
    // s_r is also supposed to be sampled [-B, B], see prior comment on this
    // p -> randomness, s_p -> s_r, u_p -> u_r, d/e_p -> d/e_r, q/r_p -> q/r_r
    let s_r = crate::sample_number_less_than(rng, &B);
    let s_m = crate::sample_number_less_than(rng, cg.p());
    #[allow(non_snake_case)]
    let S1 = public_key.mul(&s_r).add(&cg.f().mul(&s_m));
    #[allow(non_snake_case)]
    let S2 = cg.g().mul(&s_r);

    let c = Self::transcript_Ss(cg, transcript, &S1, &S2);
    let u_r = s_r + (&c * &randomness);
    let u_m = (s_m + (&c * message)) % cg.p();

    let (d_r, e_r) = (u_r.div_euclid(cg.p()), u_r.rem_euclid(cg.p()));
    #[allow(non_snake_case)]
    let D1 = public_key.mul(&d_r);
    #[allow(non_snake_case)]
    let D2 = cg.g().mul(&d_r);
    let l = Self::transcript_u_Ds_e(transcript, &u_m, &D1, &D2, &e_r);

    let (q_r, r_r) = (u_r.div_euclid(&l), u_r.rem_euclid(&l));
    #[allow(non_snake_case)]
    let Q1 = public_key.mul(&q_r);
    #[allow(non_snake_case)]
    let Q2 = cg.g().mul(&q_r);

    (ciphertext, Self { S1, S2, u_m, D1, D2, e_r, Q1, Q2, r_r })
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    public_key: &Element,
    ciphertext: &Ciphertext,
  ) -> Result<(), ()> {
    let c = Self::transcript_Ss(cg, transcript, &self.S1, &self.S2);
    if self.e_r >= *cg.p() {
      Err(())?
    }
    let fum = cg.f().mul(&self.u_m);
    // 2021-205 uses an inverted ordering for ciphertext members
    #[allow(non_snake_case)]
    let S1C1c = self.S1.add(&ciphertext.1.mul(&c));
    #[allow(non_snake_case)]
    let S2C2c = self.S2.add(&ciphertext.0.mul(&c));

    if self.D1.mul(cg.p()).add(&public_key.mul(&self.e_r)).add(&fum) != S1C1c {
      Err(())?
    }
    if self.D2.mul(cg.p()).add(&cg.g().mul(&self.e_r)) != S2C2c {
      Err(())?
    }
    let l = Self::transcript_u_Ds_e(transcript, &self.u_m, &self.D1, &self.D2, &self.e_r);

    if self.r_r >= l {
      Err(())?
    }
    if self.Q1.mul(&l).add(&public_key.mul(&self.r_r)).add(&fum) != S1C1c {
      Err(())?
    }
    if self.Q2.mul(&l).add(&cg.g().mul(&self.r_r)) != S2C2c {
      Err(())?
    }
    Ok(())
  }
}

// https://eprint.iacr.org/2022/1437 Section 5.2 where n = 2 and m = 1 for 0 <= w < cg.p()
// S = cg.p()
// A = cg.secret_bound()
// c = 2 ** 256
#[allow(non_snake_case)]
pub struct ZkDlogEqualityProof {
  T0: Element,
  T1: Element,
  u: BigUint,
}
impl ZkDlogEqualityProof {
  #[allow(non_snake_case)]
  fn transcript_Ts(transcript: &mut impl Transcript, T0: &Element, T1: &Element) -> BigUint {
    transcript.domain_separate(b"ZkDlogEqualityProof");
    T0.transcript(b"T0", transcript);
    T1.transcript(b"T1", transcript);
    // Any 256-bit number should work as a challenge
    BigUint::from_bytes_be(&transcript.challenge(b"c").as_ref()[.. 32])
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    generator_0: &Element,
    generator_1: &Element,
    dlog: &BigUint,
  ) -> Self {
    // X = [generator_0, generator_1]
    // w = [dlog]
    let r = cg.sample_secret(rng);
    #[allow(non_snake_case)]
    let T0 = generator_0.mul(&r);
    #[allow(non_snake_case)]
    let T1 = generator_1.mul(&r);
    let c = Self::transcript_Ts(transcript, &T0, &T1);
    let u = r + (c * dlog);
    ZkDlogEqualityProof { T0, T1, u }
  }
  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    generator_0: &Element,
    generator_1: &Element,
    element_0: &Element,
    element_1: &Element,
  ) -> Result<(), ()> {
    if self.u > ((cg.p() * &(BigUint::one() << 256)) + cg.secret_bound()) {
      dbg!(Err(()))?
    }
    let c = Self::transcript_Ts(transcript, &self.T0, &self.T1);
    if self.T0.add(&element_0.mul(&c)) != generator_0.mul(&self.u) {
      dbg!(Err(()))?
    }
    if self.T1.add(&element_1.mul(&c)) != generator_1.mul(&self.u) {
      dbg!(Err(()))?
    }
    Ok(())
  }
}

#[test]
fn dlog_without_subgroup() {
  use rand_core::OsRng;
  use transcript::RecommendedTranscript;

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);
  let transcript = || RecommendedTranscript::new(b"DLog Outside Subgroup Proof Test");
  ZkDlogOutsideSubgroupProof::prove(&mut OsRng, &cg, &mut transcript(), &private_key)
    .verify(&cg, &mut transcript(), &public_key)
    .unwrap();
}

#[test]
fn encryption() {
  use rand_core::OsRng;
  use transcript::RecommendedTranscript;

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);

  let transcript = || RecommendedTranscript::new(b"Encryption Proof Test");

  let mut m1 = vec![0; 31];
  OsRng.fill_bytes(&mut m1);
  let m1 = num_bigint::BigUint::from_be_bytes(&m1);
  let (ciphertext, proof) =
    ZkEncryptionProof::prove(&mut OsRng, &cg, &mut transcript(), &public_key, &m1);
  proof.verify(&cg, &mut transcript(), &public_key, &ciphertext).unwrap();
  assert_eq!(cg.decrypt(&private_key, &ciphertext).unwrap(), m1);
}

#[test]
fn dleq() {
  use rand_core::OsRng;
  use transcript::RecommendedTranscript;

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (_, public_key) = cg.key_gen(&mut OsRng);

  let mut m1 = vec![0; 31];
  OsRng.fill_bytes(&mut m1);
  let m1 = num_bigint::BigUint::from_be_bytes(&m1);
  let ciphertext = cg.encrypt(&mut OsRng, &public_key, &m1).1;

  let transcript = || RecommendedTranscript::new(b"Discrete Log Equality Proof Test");

  let mut dlog = vec![0; 31];
  OsRng.fill_bytes(&mut dlog);
  let dlog = num_bigint::BigUint::from_be_bytes(&dlog);
  let proof = ZkDlogEqualityProof::prove(
    &mut OsRng,
    &cg,
    &mut transcript(),
    &ciphertext.0,
    &ciphertext.1,
    &dlog,
  );
  proof
    .verify(
      &cg,
      &mut transcript(),
      &ciphertext.0,
      &ciphertext.1,
      &ciphertext.0.mul(&dlog),
      &ciphertext.1.mul(&dlog),
    )
    .unwrap();
}
