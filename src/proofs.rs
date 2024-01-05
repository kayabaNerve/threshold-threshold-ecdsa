use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_prime_with_rng;

use malachite::{
  num::{basic::traits::*, logic::traits::*, conversion::traits::*},
  *,
};

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
  e: Natural,
  Q: Element,
  r: Natural,
}

impl ZkDlogOutsideSubgroupProof {
  fn transcript_statement(transcript: &mut impl Transcript, element: &Element) {
    transcript.domain_separate(b"ZkDlogOutsideSubgroupProof");
    element.transcript(b"element", transcript);
  }

  fn transcript_R(cg: &ClassGroup, transcript: &mut impl Transcript, R: &Element) -> Natural {
    R.transcript(b"R", transcript);
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"c")), cg.p())
  }

  fn transcript_De(transcript: &mut impl Transcript, D: &Element, e: &Natural) -> Natural {
    D.transcript(b"D", transcript);
    transcript.append_message(
      b"e",
      e.to_digits_desc(&256u16).into_iter().map(|b| u8::try_from(b).unwrap()).collect::<Vec<_>>(),
    );

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
    Natural::from_digits_desc(&256, l.to_be_bytes().into_iter().map(u16::from)).unwrap()
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    x: &Natural,
  ) -> Self {
    Self::transcript_statement(transcript, &(cg.g_table() * x));

    // k is intended to be sampled from [-B, B]. We reduce the space by half yet don't sample from
    // -B as we can't calculate negatives over a field of unknown order (which has implications
    // later when s is calculated)
    let k = cg.sample_secret(rng);
    // If this is moved off `g`, we MUST transcript the g used
    let R = cg.g_table() * &k;

    let c = Self::transcript_R(cg, transcript, &R);

    let s = k + (&c * x);
    let (d, e) = (&s / cg.p(), &s % cg.p());
    let D = cg.g_table() * &d;

    let l = Self::transcript_De(transcript, &D, &e);
    let (q, r) = (&s / &l, &s % &l);
    let Q = cg.g_table() * &q;

    ZkDlogOutsideSubgroupProof { R, D, e, Q, r }
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify<'a>(
    &'a self,
    cg: &'a ClassGroup,
    batch_verifier: &mut BatchVerifier<'a>,
    transcript: &mut impl Transcript,
    w: &Element,
  ) -> Result<(), ()> {
    Self::transcript_statement(transcript, w);

    let c = Self::transcript_R(cg, transcript, &self.R);
    if self.e >= *cg.p() {
      Err(())?
    }

    batch_verifier.queue(
      [(cg.p(), &self.D)],
      [(&Natural::ONE, self.R.clone().neg()), (&c, w.clone().neg())],
      [(&self.e, cg.g_table())],
    );
    let l = Self::transcript_De(transcript, &self.D, &self.e);
    if self.r >= l {
      Err(())?
    }
    batch_verifier.queue(
      [(&l, &self.Q)],
      [(&Natural::ONE, self.R.clone().neg()), (&c, w.clone().neg())],
      [(&self.r, cg.g_table())],
    );
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
  e_p: Natural,
  Q1: Element,
  Q2: Element,
  r_p: Natural,
}

impl<C: Ciphersuite> ZkEncryptionProof<C> {
  fn transcript_statement(
    transcript: &mut impl Transcript,
    public_key_table: &Table,
    ciphertext: &Ciphertext,
    point: C::G,
  ) {
    transcript.domain_separate(b"ZkEncryptionProof");
    public_key_table[0].transcript(b"public_key", transcript);
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
  ) -> Natural {
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
    e_p: &Natural,
  ) -> Natural {
    transcript.append_message(b"u_m", u_m.to_repr());
    D1.transcript(b"D1", transcript);
    D2.transcript(b"D2", transcript);
    transcript.append_message(
      b"e_p",
      e_p.to_digits_desc(&256u16).into_iter().map(|b| u8::try_from(b).unwrap()).collect::<Vec<_>>(),
    );

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
    Natural::from_digits_desc(&256, l.to_be_bytes().into_iter().map(u16::from)).unwrap()
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    public_key_table: &Table,
    scalar: &C::F,
  ) -> (Natural, Ciphertext, Self) {
    let randomness = crate::sample_number_less_than(rng, &(cg.bound() << 128));
    let mut scalar_uint = Natural::ZERO;
    for (i, bit) in scalar.to_le_bits().into_iter().enumerate() {
      scalar_uint += Natural::from(u8::from(bit)) << i;
    }
    let ciphertext = cg.encrypt_with_randomness(&public_key_table[0], &randomness, &scalar_uint);

    Self::transcript_statement(transcript, public_key_table, &ciphertext, C::generator() * *scalar);

    let B = cg.bound() << (128 + 128 + 2);

    // TODO: These are sampled 0 .. B, not -B .. B
    let s_p = crate::sample_number_less_than(rng, &B);
    let s_m = C::F::random(rng);

    let mut s_m_uint = Natural::ZERO;
    for (i, bit) in s_m.to_le_bits().into_iter().enumerate() {
      s_m_uint += Natural::from(u8::from(bit)) << i;
    }

    let S1 = multiexp(&mut [s_p.clone(), s_m_uint], &[], &[public_key_table, cg.f_table()]);
    let S2 = cg.g_table() * &s_p;
    let S_caret = C::generator() * s_m;
    let c = Self::transcript_Ss(cg, transcript, &S1, &S2, S_caret);
    let mut c_as_scalar = C::F::ZERO;
    for b in 0 .. c.significant_bits() {
      c_as_scalar = c_as_scalar.double();
      if c.get_bit(c.significant_bits() - b - 1) {
        c_as_scalar += C::F::ONE;
      }
    }

    let u_p = s_p + (c * &randomness);
    let u_m = s_m + (c_as_scalar * scalar);

    let d_p = &u_p / cg.p();
    let e_p = &u_p % cg.p();

    let D1 = public_key_table * &d_p;
    let D2 = cg.g_table() * &d_p;

    let l = Self::transcript_u_Ds_es(transcript, u_m, &D1, &D2, &e_p);

    let q_p = &u_p / &l;
    let r_p = &u_p % &l;

    let Q1 = public_key_table * &q_p;
    let Q2 = cg.g_table() * &q_p;

    (randomness, ciphertext, Self { S1, S2, S_caret, u_m, D1, D2, e_p, Q1, Q2, r_p })
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify<'a>(
    &'a self,
    cg: &'a ClassGroup,
    verifier: &mut BatchVerifier<'a>,
    transcript: &mut impl Transcript,
    public_key_table: &'a Table,
    ciphertext: &'a Ciphertext,
    point: C::G,
  ) -> Result<(), ()> {
    Self::transcript_statement(transcript, public_key_table, ciphertext, point);

    let c = Self::transcript_Ss(cg, transcript, &self.S1, &self.S2, self.S_caret);
    let mut c_as_scalar = C::F::ZERO;
    for b in 0 .. c.significant_bits() {
      c_as_scalar = c_as_scalar.double();
      if c.get_bit(c.significant_bits() - b - 1) {
        c_as_scalar += C::F::ONE;
      }
    }
    if (self.S_caret + (point * c_as_scalar)) != (C::generator() * self.u_m) {
      Err(())?;
    }

    let mut u_m_uint = Natural::ZERO;
    for (i, bit) in self.u_m.to_le_bits().into_iter().enumerate() {
      u_m_uint += Natural::from(u8::from(bit)) << i;
    }

    verifier.queue(
      [(cg.p(), &self.D1)],
      [(&Natural::ONE, self.S1.clone().neg()), (&c, ciphertext.1.clone().neg())],
      [(&self.e_p, public_key_table), (&u_m_uint, cg.f_table())],
    );
    verifier.queue(
      [(cg.p(), &self.D2)],
      [(&Natural::ONE, self.S2.clone().neg()), (&c, ciphertext.0.clone().neg())],
      [(&self.e_p, cg.g_table())],
    );

    let l = Self::transcript_u_Ds_es(transcript, self.u_m, &self.D1, &self.D2, &self.e_p);
    if self.r_p >= l {
      Err(())?
    }

    verifier.queue(
      [(&l, &self.Q1)],
      [(&Natural::ONE, self.S1.clone().neg()), (&c, ciphertext.1.clone().neg())],
      [(&self.r_p, public_key_table), (&u_m_uint, cg.f_table())],
    );
    verifier.queue(
      [(&l, &self.Q2)],
      [(&Natural::ONE, self.S2.clone().neg()), (&c, ciphertext.0.clone().neg())],
      [(&self.r_p, cg.g_table())],
    );

    Ok(())
  }
}

#[derive(Clone, Copy)]
pub enum ElementOrTable<'a> {
  Identity,
  Element(&'a Element),
  Table(&'a Table),
}
impl<'a> From<&'a Element> for ElementOrTable<'a> {
  fn from(element: &'a Element) -> Self {
    if element.is_identity() {
      return ElementOrTable::Identity;
    }
    ElementOrTable::Element(element)
  }
}
impl<'a> From<&'a Table> for ElementOrTable<'a> {
  fn from(table: &'a Table) -> Self {
    ElementOrTable::Table(table)
  }
}

// https://eprint.iacr.org/2022/1437 5.2
pub struct ZkRelationProof<const N: usize, const M: usize> {
  Ts: [Element; N],
  us: [Natural; M],
}
impl<const N: usize, const M: usize> ZkRelationProof<N, M> {
  fn transcript_statement(
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    Xs: &[[ElementOrTable<'_>; M]; N],
    Ys: &[&Element; N],
  ) {
    transcript.domain_separate(b"ZkRelationProof");
    transcript.append_message(b"n", u32::try_from(N).unwrap().to_le_bytes());
    transcript.append_message(b"m", u32::try_from(M).unwrap().to_le_bytes());
    for Xs in Xs {
      for X in Xs {
        let X = match X {
          ElementOrTable::Identity => cg.identity(),
          ElementOrTable::Element(X) => X,
          ElementOrTable::Table(X) => &X[0],
        };
        X.transcript(b"X", transcript);
      }
    }
    for Y in Ys {
      Y.transcript(b"Y", transcript);
    }
  }

  fn transcript_Ts(transcript: &mut impl Transcript, Ts: &[Element]) -> Natural {
    for T in Ts {
      T.transcript(b"Ts", transcript);
    }
    // Any 256-bit number should work as a challenge
    Natural::from_digits_desc(
      &256,
      transcript.challenge(b"c").as_ref()[.. 32].iter().map(|b| u16::from(*b)),
    )
    .unwrap()
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    Xs: [[ElementOrTable<'_>; M]; N],
    ws: [&Natural; M],
  ) -> Self {
    let identity_table = cg.identity().small_table();
    let mut adhoc_tables = vec![];
    for Xs in Xs {
      for X in Xs {
        if let ElementOrTable::Element(X) = X {
          adhoc_tables.push(X.small_table());
        }
      }
    }

    let mut a_t = 0;
    let tables: [[_; M]; N] = core::array::from_fn(|i| {
      core::array::from_fn(|j| match Xs[i][j] {
        ElementOrTable::Identity => &identity_table,
        ElementOrTable::Element(_) => {
          let res = &adhoc_tables[a_t];
          a_t += 1;
          res
        }
        ElementOrTable::Table(X) => X,
      })
    });

    let mut Ys: [_; N] = core::array::from_fn(|_| cg.identity().clone());
    for (i, Xs) in tables.iter().enumerate() {
      let mut scalars = vec![];
      let mut tables = vec![];
      for (j, X) in Xs.iter().enumerate() {
        scalars.push(ws[j].clone());
        tables.push(*X);
      }
      Ys[i] = multiexp(&mut scalars, &[], &tables);
    }
    Self::transcript_statement(cg, transcript, &Xs, &core::array::from_fn(|i| &Ys[i]));

    let rs = core::array::from_fn::<_, M, _>(|_| cg.sample_secret(rng));
    let mut Ts = core::array::from_fn(|_| cg.identity().clone());
    for i in 0 .. N {
      let mut scalars = vec![];
      let mut these_tables = vec![];
      #[allow(clippy::needless_range_loop)]
      for j in 0 .. M {
        scalars.push(rs[j].clone());
        these_tables.push(tables[i][j]);
      }
      Ts[i] = multiexp(&mut scalars, &[], &these_tables);
    }
    let c = Self::transcript_Ts(transcript, &Ts);
    let mut us = core::array::from_fn(|_| Natural::ZERO);
    for j in 0 .. M {
      us[j] = &rs[j] + (&c * ws[j]);
    }
    ZkRelationProof { Ts, us }
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify<'a>(
    &'a self,
    cg: &'a ClassGroup,
    verifier: &mut BatchVerifier<'a>,
    transcript: &mut impl Transcript,
    // Limit for the discrete logarithms
    // TODO: Should this be individualized?
    S: &Natural,
    Xs: [[ElementOrTable<'a>; M]; N],
    Ys: [&'a Element; N],
  ) -> Result<(), ()> {
    Self::transcript_statement(cg, transcript, &Xs, &Ys);

    for u in &self.us {
      if u > &((S * &(Natural::ONE << 256)) + cg.secret_bound()) {
        Err(())?
      }
    }

    let c = Self::transcript_Ts(transcript, &self.Ts);
    for i in 0 .. N {
      let mut pairs = vec![];
      let mut tabled_pairs = vec![];
      for j in 0 .. M {
        match Xs[i][j] {
          ElementOrTable::Identity => continue,
          ElementOrTable::Element(X) => pairs.push((&self.us[j], X)),
          ElementOrTable::Table(X) => tabled_pairs.push((&self.us[j], X)),
        }
      }
      verifier.queue(
        pairs,
        [(&Natural::ONE, self.Ts[i].clone().neg()), (&c, Ys[i].clone().neg())],
        tabled_pairs,
      );
    }
    Ok(())
  }
}

#[test]
fn dlog_without_subgroup() {
  use rand_core::OsRng;

  use transcript::RecommendedTranscript;
  use ciphersuite::Secp256k1;

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod =
    Natural::from_digits_desc(&256, secp256k1_mod.into_iter().map(u16::from)).unwrap();

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);
  let transcript = || RecommendedTranscript::new(b"DLog Outside Subgroup Proof Test");
  let mut verifier = BatchVerifier::new();
  let proof = ZkDlogOutsideSubgroupProof::prove(&mut OsRng, &cg, &mut transcript(), &private_key);
  proof.verify(&cg, &mut verifier, &mut transcript(), &public_key).unwrap();
  assert!(verifier.verify());
}

#[test]
fn encryption() {
  use rand_core::OsRng;

  use transcript::RecommendedTranscript;
  use ciphersuite::Secp256k1;

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod =
    Natural::from_digits_desc(&256, secp256k1_mod.into_iter().map(u16::from)).unwrap();

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);
  let public_key_table = public_key.small_table();

  let transcript = || RecommendedTranscript::new(b"Encryption Proof Test");

  let m = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
  let (_randomness, ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
    &mut OsRng,
    &cg,
    &mut transcript(),
    &public_key_table,
    &m,
  );

  let mut verifier = BatchVerifier::new();
  proof
    .verify(
      &cg,
      &mut verifier,
      &mut transcript(),
      &public_key_table,
      &ciphertext,
      Secp256k1::generator() * m,
    )
    .unwrap();
  assert!(verifier.verify());

  assert_eq!(
    cg.decrypt(&private_key, &ciphertext).unwrap(),
    Natural::from_digits_desc(&256, m.to_repr().iter().map(|b| u16::from(*b))).unwrap()
  );
}
