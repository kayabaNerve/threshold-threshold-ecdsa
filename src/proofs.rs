use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_prime_with_rng;

use num_traits::{Zero, One};
use num_integer::Integer;
use num_bigint::*;

use transcript::Transcript;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    GroupEncoding,
  },
  Ciphersuite,
};

use crate::class_group::*;

// https://eprint.iacr.org/2021/205 Algorithm 2
pub struct ZkDlogOutsideSubgroupProof {
  R: Element,
  D: Element,
  e: BigUint,
  Q: Element,
  r: BigUint,
}

impl ZkDlogOutsideSubgroupProof {
  fn transcript_statement(transcript: &mut impl Transcript, element: &Element) {
    transcript.domain_separate(b"ZkDlogOutsideSubgroupProof");
    element.transcript(b"element", transcript);
  }

  fn transcript_R(cg: &ClassGroup, transcript: &mut impl Transcript, R: &Element) -> BigUint {
    R.transcript(b"R", transcript);
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

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
      Some(136),
    );
    BigUint::from_bytes_be(l.to_be_bytes().as_ref())
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    x: &BigUint,
  ) -> Self {
    Self::transcript_statement(transcript, &cg.g().mul(x));

    // k is intended to be sampled from [-B, B]. We reduce the space by half yet don't sample from
    // -B as we can't calculate negatives over a field of unknown order (which has implications
    // later when s is calculated)
    let k = cg.sample_secret(rng);
    // If this is moved off `g`, we MUST transcript the g used
    let R = cg.g().mul(&k);

    let c = Self::transcript_R(cg, transcript, &R);

    let s = k + (&c * x);
    let (d, e) = (&s / cg.p(), s.mod_floor(cg.p()));
    let D = cg.g().mul(&d);

    let l = Self::transcript_De(transcript, &D, &e);
    let (q, r) = (&s / &l, s.mod_floor(&l));
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
    Self::transcript_statement(transcript, w);

    let c = Self::transcript_R(cg, transcript, &self.R);
    if self.e >= *cg.p() {
      Err(())?
    }
    let Rwc = self.R.add(&w.mul(&c));
    if multiexp(&[cg.p(), &self.e], &[&self.D, cg.g()]) != Rwc {
      Err(())?
    }
    let l = Self::transcript_De(transcript, &self.D, &self.e);
    if self.r >= l {
      Err(())?
    }
    if multiexp(&[&l, &self.r], &[&self.Q, cg.g()]) != Rwc {
      Err(())?
    }
    Ok(())
  }
}

// https://eprint.iacr.org/2021/205 Algorithm 6, without the column proving the public key is
// well-formed. The caller is expected to have already checked that.
// TODO: Review https://eprint.iacr.org/2022/297 as an alternative
pub struct ZkEncryptionProof<C: Ciphersuite> {
  S1: Element,
  S2: Element,
  S_caret: C::G,
  u_m: C::F,
  D1: Element,
  D2: Element,
  e_p: BigUint,
  Q1: Element,
  Q2: Element,
  r_p: BigUint,
}

impl<C: Ciphersuite> ZkEncryptionProof<C> {
  fn transcript_statement(
    transcript: &mut impl Transcript,
    public_key: &Element,
    ciphertext: &Ciphertext,
    point: C::G,
  ) {
    transcript.domain_separate(b"ZkEncryptionProof");
    public_key.transcript(b"public_key", transcript);
    ciphertext.0.transcript(b"ciphertext_randomness", transcript);
    ciphertext.1.transcript(b"ciphertext_message", transcript);
    transcript.append_message(b"point", point.to_bytes());
  }

  fn transcript_Ss(
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    S1: &Element,
    S2: &Element,
    S_caret: C::G,
  ) -> BigUint {
    S1.transcript(b"S1", transcript);
    S2.transcript(b"S2", transcript);
    transcript.append_message(b"S_caret", S_caret.to_bytes());
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

  fn transcript_u_Ds_es(
    transcript: &mut impl Transcript,
    u_m: C::F,
    D1: &Element,
    D2: &Element,
    e_p: &BigUint,
  ) -> BigUint {
    transcript.append_message(b"u_m", u_m.to_repr());
    D1.transcript(b"D1", transcript);
    D2.transcript(b"D2", transcript);
    transcript.append_message(b"e_p", e_p.to_bytes_be());

    // The soundness error is 1/2**(bits - log2 bits), so a 136 bit prime should be fine for the
    // targeted 128-bits of security
    assert_eq!(Uint::<{ 256 / 64 }>::BITS, 256);
    // TODO: Does crypto-primes guarantee a uniform distribution? As-current, it iterates from a
    // random starting point when using generate_prime (generate_safe_prime is distinct regarding
    // its pattern) which doesn't guarantee true uniformity.
    // https://github.com/entropyxyz/crypto-primes/issues/23 for the relevant issue
    let l = generate_prime_with_rng::<{ 256 / 64 }>(
      &mut ChaCha20Rng::from_seed(transcript.rng_seed(b"l")),
      Some(136),
    );
    BigUint::from_bytes_be(l.to_be_bytes().as_ref())
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    public_key: &Element,
    scalar: &C::F,
  ) -> (BigUint, Ciphertext, Self) {
    let randomness = crate::sample_number_less_than(rng, &(cg.bound() << 128));
    let mut scalar_uint = BigUint::zero();
    for (i, bit) in scalar.to_le_bits().into_iter().enumerate() {
      scalar_uint += BigUint::from(u8::from(bit)) << i;
    }
    let ciphertext = cg.encrypt_with_randomness(public_key, &randomness, &scalar_uint);

    Self::transcript_statement(transcript, public_key, &ciphertext, C::generator() * *scalar);

    let B = cg.bound() << (128 + 128 + 2);

    // TODO: These are sampled 0 .. B, not -B .. B
    let s_p = crate::sample_number_less_than(rng, &B);
    let s_m = C::F::random(rng);

    let mut s_m_uint = BigUint::zero();
    for (i, bit) in s_m.to_le_bits().into_iter().enumerate() {
      s_m_uint += BigUint::from(u8::from(bit)) << i;
    }

    let S1 = public_key.mul(&s_p).add(&cg.f().mul(&s_m_uint));
    let S2 = cg.g().mul(&s_p);
    let S_caret = C::generator() * s_m;
    let c = Self::transcript_Ss(cg, transcript, &S1, &S2, S_caret);
    let mut c_as_scalar = C::F::ZERO;
    for b in 0 .. c.bits() {
      c_as_scalar = c_as_scalar.double();
      if c.bit(c.bits() - b - 1) {
        c_as_scalar += C::F::ONE;
      }
    }

    let u_p = s_p + (c * &randomness);
    let u_m = s_m + (c_as_scalar * scalar);

    let d_p = &u_p / cg.p();
    let e_p = u_p.mod_floor(cg.p());

    let D1 = public_key.mul(&d_p);
    let D2 = cg.g().mul(&d_p);

    let l = Self::transcript_u_Ds_es(transcript, u_m, &D1, &D2, &e_p);

    let q_p = &u_p / &l;
    let r_p = u_p.mod_floor(&l);

    let Q1 = public_key.mul(&q_p);
    let Q2 = cg.g().mul(&q_p);

    (randomness, ciphertext, Self { S1, S2, S_caret, u_m, D1, D2, e_p, Q1, Q2, r_p })
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    public_key: &Element,
    ciphertext: &Ciphertext,
    point: C::G,
  ) -> Result<(), ()> {
    Self::transcript_statement(transcript, public_key, ciphertext, point);

    let c = Self::transcript_Ss(cg, transcript, &self.S1, &self.S2, self.S_caret);
    let mut c_as_scalar = C::F::ZERO;
    for b in 0 .. c.bits() {
      c_as_scalar = c_as_scalar.double();
      if c.bit(c.bits() - b - 1) {
        c_as_scalar += C::F::ONE;
      }
    }
    if (self.S_caret + (point * c_as_scalar)) != (C::generator() * self.u_m) {
      Err(())?;
    }

    let mut u_m_uint = BigUint::zero();
    for (i, bit) in self.u_m.to_le_bits().into_iter().enumerate() {
      u_m_uint += BigUint::from(u8::from(bit)) << i;
    }
    let fum = cg.f().mul(&u_m_uint);
    let S1C1c = self.S1.add(&ciphertext.1.mul(&c));
    if multiexp(&[cg.p(), &self.e_p], &[&self.D1, public_key]).add(&fum) != S1C1c {
      Err(())?
    }
    let S2C2c = self.S2.add(&ciphertext.0.mul(&c));
    if multiexp(&[cg.p(), &self.e_p], &[&self.D2, cg.g()]) != S2C2c {
      Err(())?
    }

    let l = Self::transcript_u_Ds_es(transcript, self.u_m, &self.D1, &self.D2, &self.e_p);
    if self.r_p >= l {
      Err(())?
    }
    if multiexp(&[&l, &self.r_p], &[&self.Q1, public_key]).add(&fum) != S1C1c {
      Err(())?;
    }
    if multiexp(&[&l, &self.r_p], &[&self.Q2, cg.g()]) != S2C2c {
      Err(())?;
    }

    Ok(())
  }
}

// https://eprint.iacr.org/2022/1437 5.2
pub struct ZkRelationProof<const N: usize, const M: usize> {
  Ts: [Element; N],
  us: [BigUint; M],
}
impl<const N: usize, const M: usize> ZkRelationProof<N, M> {
  fn transcript_statement(
    transcript: &mut impl Transcript,
    Xs: &[[&Element; M]; N],
    Ys: &[&Element; N],
  ) {
    transcript.domain_separate(b"ZkRelationProof");
    transcript.append_message(b"n", u32::try_from(N).unwrap().to_le_bytes());
    transcript.append_message(b"m", u32::try_from(M).unwrap().to_le_bytes());
    for Xs in Xs {
      for X in Xs {
        X.transcript(b"X", transcript);
      }
    }
    for Y in Ys {
      Y.transcript(b"Y", transcript);
    }
  }

  fn transcript_Ts(transcript: &mut impl Transcript, Ts: &[Element]) -> BigUint {
    for T in Ts {
      T.transcript(b"Ts", transcript);
    }
    // Any 256-bit number should work as a challenge
    BigUint::from_bytes_be(&transcript.challenge(b"c").as_ref()[.. 32])
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    Xs: [[&Element; M]; N],
    ws: [&BigUint; M],
  ) -> Self {
    let mut Ys: [_; N] = core::array::from_fn(|_| cg.identity().clone());
    for (i, Xs) in Xs.iter().enumerate() {
      for (j, X) in Xs.iter().enumerate() {
        Ys[i] = Ys[i].add(&X.mul(ws[j]));
      }
    }
    Self::transcript_statement(transcript, &Xs, &core::array::from_fn(|i| &Ys[i]));

    let rs = core::array::from_fn::<_, M, _>(|_| cg.sample_secret(rng));
    let mut Ts = core::array::from_fn(|_| cg.identity().clone());
    for i in 0 .. N {
      #[allow(clippy::needless_range_loop)]
      for j in 0 .. M {
        Ts[i] = Ts[i].add(&Xs[i][j].mul(&rs[j]));
      }
    }
    let c = Self::transcript_Ts(transcript, &Ts);
    let mut us = core::array::from_fn(|_| BigUint::zero());
    for j in 0 .. M {
      us[j] = &rs[j] + (&c * ws[j]);
    }
    ZkRelationProof { Ts, us }
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    // Limit for the discrete logarithms
    // TODO: Should this be individualized?
    S: &BigUint,
    Xs: [[&Element; M]; N],
    Ys: [&Element; N],
  ) -> Result<(), ()> {
    Self::transcript_statement(transcript, &Xs, &Ys);

    for u in &self.us {
      if u > &((S * &(BigUint::one() << 256)) + cg.secret_bound()) {
        Err(())?
      }
    }

    let c = Self::transcript_Ts(transcript, &self.Ts);
    for i in 0 .. N {
      let lhs = self.Ts[i].add(&Ys[i].mul(&c));
      let mut scalars = vec![];
      let mut elements = vec![];
      for j in 0 .. M {
        scalars.push(&self.us[j]);
        elements.push(Xs[i][j]);
      }
      if lhs != multiexp(&scalars, &elements) {
        Err(())?
      }
    }
    Ok(())
  }
}

#[test]
fn dlog_without_subgroup() {
  use rand_core::OsRng;

  use num_traits::FromBytes;

  use transcript::RecommendedTranscript;
  use ciphersuite::Secp256k1;

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

  use num_traits::FromBytes;

  use transcript::RecommendedTranscript;
  use ciphersuite::Secp256k1;

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);

  let transcript = || RecommendedTranscript::new(b"Encryption Proof Test");

  let m = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
  let (_randomness, ciphertext, proof) =
    ZkEncryptionProof::<Secp256k1>::prove(&mut OsRng, &cg, &mut transcript(), &public_key, &m);
  proof
    .verify(&cg, &mut transcript(), &public_key, &ciphertext, Secp256k1::generator() * m)
    .unwrap();
  assert_eq!(cg.decrypt(&private_key, &ciphertext).unwrap(), BigUint::from_be_bytes(&m.to_repr()));
}
