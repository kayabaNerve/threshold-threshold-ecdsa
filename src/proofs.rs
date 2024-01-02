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
    ff::{Field, PrimeFieldBits},
    GroupEncoding,
  },
  Ciphersuite,
};

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
    // k is intended to be sampled from [-B, B]. We reduce the space by half yet don't sample from
    // -B as we can't calculate negatives over a field of unknown order (which has implications
    // later when s is calculated)
    let k = cg.sample_secret(rng);
    // If this is moved off `g`, we MUST transcript the g used
    #[allow(non_snake_case)]
    let R = cg.g().mul(&k);

    let c = Self::transcript_R(cg, transcript, &R);

    let s = k + (&c * x);
    let (d, e) = (&s / cg.p(), s.mod_floor(cg.p()));
    #[allow(non_snake_case)]
    let D = cg.g().mul(&d);

    let l = Self::transcript_De(transcript, &D, &e);
    let (q, r) = (&s / &l, s.mod_floor(&l));
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

// https://eprint.iacr.org/2020/085 Figure 7
#[allow(non_snake_case)]
pub struct ZkEncryptionProof<C: Ciphersuite> {
  t1: Element,
  t2: Element,
  T: C::G,
  u1: BigUint,
  u2: C::F,
}

impl<C: Ciphersuite> ZkEncryptionProof<C> {
  #[allow(non_snake_case)]
  fn transcript_Ts(
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    t1: &Element,
    t2: &Element,
    T: &C::G,
  ) -> BigUint {
    transcript.domain_separate(b"ZkEncryptionProof");
    t1.transcript(b"t1", transcript);
    t2.transcript(b"t2", transcript);
    transcript.append_message(b"T", T.to_bytes());
    crate::sample_number_less_than(&mut ChaCha20Rng::from_seed(transcript.rng_seed(b"k")), cg.p())
  }

  pub fn sample_randomness(rng: &mut (impl RngCore + CryptoRng), cg: &ClassGroup) -> BigUint {
    #[allow(non_snake_case)]
    let A = cg.bound() << 40;
    crate::sample_number_less_than(rng, &A)
  }

  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    public_key: &Element,
    randomness: &BigUint,
    scalar: &C::F,
  ) -> (Ciphertext, Self) {
    #[allow(non_snake_case)]
    let A = cg.bound() << 40;
    // TODO: The proof specifies g as `cg.g() * t`, where `t` is a random scalar
    // (potentially private?)
    // Yet this proof only works if this g is the same as the one used for ciphertexts
    // Is this g valid? Do we need to ensure the g from setup meets some requirement?
    let g = cg.g();
    #[allow(non_snake_case)]
    let C = cg.p();

    let mut scalar_uint = BigUint::zero();
    for (i, bit) in scalar.to_le_bits().into_iter().enumerate() {
      scalar_uint += BigUint::from(u8::from(bit)) << i;
    }
    let ciphertext = cg.encrypt_with_randomness(public_key, randomness, &scalar_uint);

    let r1 = crate::sample_number_less_than(rng, &(&A * C * &(BigUint::one() << 40)));
    let r2 = crate::sample_number_less_than(rng, cg.p());

    let t1 = g.mul(&r1);
    let t2 = public_key.mul(&r1).add(&(cg.f().mul(&r2)));

    let mut r2_as_scalar = C::F::ZERO;
    for b in 0 .. r2.bits() {
      r2_as_scalar = r2_as_scalar.double();
      if r2.bit(r2.bits() - b - 1) {
        r2_as_scalar += C::F::ONE;
      }
    }

    #[allow(non_snake_case)]
    let T = C::generator() * r2_as_scalar;
    let k = Self::transcript_Ts(cg, transcript, &t1, &t2, &T);
    let u1 = r1 + (&k * randomness);

    let mut k_as_scalar = C::F::ZERO;
    for b in 0 .. k.bits() {
      k_as_scalar = k_as_scalar.double();
      if k.bit(k.bits() - b - 1) {
        k_as_scalar += C::F::ONE;
      }
    }
    let u2 = r2_as_scalar + (k_as_scalar * scalar);

    (ciphertext, Self { t1, t2, T, u1, u2 })
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
    #[allow(non_snake_case)]
    let A = cg.bound() << 40;
    let g = cg.g();
    #[allow(non_snake_case)]
    let C = cg.p();

    let k = Self::transcript_Ts(cg, transcript, &self.t1, &self.t2, &self.T);
    if self.u1 >= (A * C * ((BigUint::one() << 40) + BigUint::one())) {
      Err(())?;
    }
    if g.mul(&self.u1) != self.t1.add(&ciphertext.0.mul(&k)) {
      Err(())?;
    }

    let mut k_as_scalar = C::F::ZERO;
    for b in 0 .. k.bits() {
      k_as_scalar = k_as_scalar.double();
      if k.bit(k.bits() - b - 1) {
        k_as_scalar += C::F::ONE;
      }
    }
    if (self.T + (point * k_as_scalar)) != (C::generator() * self.u2) {
      Err(())?;
    }

    let mut u2_uint = BigUint::zero();
    for (i, bit) in self.u2.to_le_bits().into_iter().enumerate() {
      u2_uint += BigUint::from(u8::from(bit)) << i;
    }
    if public_key.mul(&self.u1).add(&cg.f().mul(&u2_uint)) != self.t2.add(&ciphertext.1.mul(&k)) {
      Err(())?;
    }
    Ok(())
  }
}

// https://eprint.iacr.org/2022/1437 5.2
#[allow(non_snake_case)]
pub struct ZkRelationProof<const N: usize, const M: usize> {
  Ts: [Element; N],
  us: [BigUint; M],
}
impl<const N: usize, const M: usize> ZkRelationProof<N, M> {
  #[allow(non_snake_case)]
  fn transcript_Ts(transcript: &mut impl Transcript, Ts: &[Element]) -> BigUint {
    transcript.domain_separate(b"ZkRelationProof");
    for T in Ts {
      T.transcript(b"Ts", transcript);
    }
    // Any 256-bit number should work as a challenge
    BigUint::from_bytes_be(&transcript.challenge(b"c").as_ref()[.. 32])
  }

  #[allow(non_snake_case)]
  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    cg: &ClassGroup,
    transcript: &mut impl Transcript,
    Xs: [[&Element; M]; N],
    ws: [&BigUint; M],
  ) -> Self {
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

  #[allow(non_snake_case, clippy::result_unit_err)]
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
    for u in &self.us {
      if u > &((S * &(BigUint::one() << 256)) + cg.secret_bound()) {
        Err(())?
      }
    }

    let c = Self::transcript_Ts(transcript, &self.Ts);
    for i in 0 .. N {
      let lhs = self.Ts[i].add(&Ys[i].mul(&c));
      let mut rhs = cg.identity().clone();
      for j in 0 .. M {
        rhs = rhs.add(&Xs[i][j].mul(&self.us[j]));
      }
      if lhs != rhs {
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
  use ciphersuite::{group::ff::PrimeField, Secp256k1};

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
  use ciphersuite::{group::ff::PrimeField, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);

  let transcript = || RecommendedTranscript::new(b"Encryption Proof Test");

  let r = ZkEncryptionProof::<Secp256k1>::sample_randomness(&mut OsRng, &cg);
  let m = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
  let (ciphertext, proof) =
    ZkEncryptionProof::<Secp256k1>::prove(&mut OsRng, &cg, &mut transcript(), &public_key, &r, &m);
  proof
    .verify(&cg, &mut transcript(), &public_key, &ciphertext, Secp256k1::generator() * m)
    .unwrap();
  assert_eq!(cg.decrypt(&private_key, &ciphertext).unwrap(), BigUint::from_be_bytes(&m.to_repr()));
}
