use rand_core::{RngCore, CryptoRng};

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_safe_prime_with_rng;

use num_traits::*;
use num_integer::*;
use num_bigint::*;

use transcript::Transcript;

#[cfg(test)]
const RHO_BITS: usize = 640;
// delta k needs to be 1828 bits for 128-bit security
#[cfg(not(test))]
const RHO_BITS: usize = 1828;

const P_BITS: usize = 521;

fn transcript_int(label: &'static [u8], transcript: &mut impl Transcript, i: &BigInt) {
  let (sign, bytes) = i.to_bytes_be();
  transcript.append_message(
    b"sign",
    [match sign {
      Sign::Minus => 255,
      Sign::NoSign => 0,
      Sign::Plus => 1,
    }],
  );
  transcript.append_message(label, bytes);
}

// https://eprint.iacr.org/2015/047 3.1 Proposition 1
#[allow(non_snake_case)]
fn L(m: BigUint, p_uint: &BigUint) -> BigInt {
  let m = BigInt::from(m.mod_floor(p_uint));
  let p = BigInt::from(p_uint.clone());

  // Invert m over p
  let gcd = p.extended_gcd(&m);
  assert!(gcd.gcd.is_one());
  let inverse = if gcd.y.sign() == Sign::Plus { gcd.y } else { &p + gcd.y };
  assert!((&inverse * &m).mod_floor(&p).is_one());
  let inverse = inverse.to_biguint().unwrap();

  if inverse.is_odd() {
    inverse.into()
  } else {
    BigInt::from_biguint(Sign::Minus, p_uint - inverse)
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Element {
  a: BigInt,
  b: BigInt,
  c: BigInt,
}

impl Element {
  pub fn transcript(&self, label: &'static [u8], transcript: &mut impl Transcript) {
    transcript.append_message(b"Element", label);
    transcript_int(b"a", transcript, &self.a);
    transcript_int(b"b", transcript, &self.b);
    // c is deterministic off a/b per the discriminant, so transcripting c achieves binding to the
    // discriminant
    transcript_int(b"c", transcript, &self.c);
  }

  // https://eprint.iacr.org/2015/047 B.2 provides this formula
  fn c(a: &BigInt, b: BigInt, discriminant: &BigInt) -> Option<BigInt> {
    // b**2 - 4ac = discriminant
    //  b**2 - discriminant = 4ac
    let four_ac: BigInt = b.pow(2u8) - discriminant;
    if !(&four_ac & BigInt::from(3u8)).is_zero() {
      None?
    }
    let ac = four_ac >> 2u8;
    let (res, rem) = ac.div_rem(a);
    if !rem.is_zero() {
      None?
    }
    Some(res)
  }

  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  pub fn reduce(self) -> Self {
    let Element { mut a, mut b, mut c } = self;
    let step_2 = |a: &mut BigInt, b: &mut BigInt, c: &mut BigInt| {
      let two_a = &*a << 1;
      let (mut q, mut r) = (b.div_euclid(&two_a), b.rem_euclid(&two_a));
      assert_eq!(*b, (&two_a * &q) + &r);
      if r > *a {
        r -= &two_a;
        q += 1;
      }
      assert_eq!(*b, (&two_a * &q) + &r);
      assert!(-&*a < r);
      assert!(r <= *a);
      *c -= ((&*b + &r) >> 1) * &q;
      *b = r;
    };
    if !((-&a < b) && (b <= a)) {
      step_2(&mut a, &mut b, &mut c);
    }
    while a > c {
      b = -b;
      std::mem::swap(&mut a, &mut c);
      step_2(&mut a, &mut b, &mut c);
    }
    if (a == c) && b.is_negative() {
      b = -b;
    }
    Element { a, b, c }
  }

  // Algorithm 5.4.7 of A Course in Computational Algebraic Number Theory
  pub fn add(&self, other: &Self) -> Self {
    // Step 1
    let (f1, f2) = if self.a > other.a { (other, self) } else { (self, other) };
    let s = (&f1.b + &f2.b) >> 1u8;
    let n = &f2.b - &s;

    let ExtendedGcd { x: u, y: v, gcd: d } = f2.a.extended_gcd(&f1.a);
    assert_eq!((&u * &f2.a) + (&v * &f1.a), d);
    let y1 = u;

    let ExtendedGcd { x: u, y: v, gcd: d1 } = s.extended_gcd(&d);
    assert_eq!((&u * &s) + (&v * &d), d1);

    let x2 = u;
    let y2 = -v;

    let v1 = &f1.a / &d1;
    let v2 = &f2.a / &d1;
    let r = ((&y1 * &y2 * &n) - (&x2 * &f2.c)).mod_floor(&v1);
    let b3 = &f2.b + ((&v2 * &r) << 1u8);
    let a3 = &v1 * &v2;
    let c3 = ((&f2.c * &d1) + (&r * (&f2.b + (v2 * &r)))) / v1;

    (Element { a: a3, b: b3, c: c3 }).reduce()
  }

  pub fn double(&self) -> Self {
    self.add(self)
  }

  pub fn neg(self) -> Self {
    Self { a: self.a, b: -self.b, c: self.c }.reduce()
  }

  pub fn mul(&self, pow: &BigUint) -> Self {
    let mut res: Option<Self> = None;
    for b in 0 .. pow.bits() {
      let b = pow.bits() - 1 - b;
      if let Some(res) = &mut res {
        *res = res.double();
      }
      if pow.bit(b) {
        if let Some(res) = &mut res {
          *res = res.add(self);
        } else {
          res = Some(self.clone());
        }
      }
    }
    res.unwrap()
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ciphertext(pub(crate) Element, pub(crate) Element);
impl Ciphertext {
  pub fn add_without_randomness(&self, other: &Ciphertext) -> Self {
    Ciphertext(self.0.add(&other.0), self.1.add(&other.1))
  }
  pub fn mul_without_randomness(&self, scalar: &BigUint) -> Self {
    Ciphertext(self.0.mul(scalar), self.1.mul(scalar))
  }
}

#[allow(non_snake_case)]
pub struct ClassGroup {
  B: BigUint,
  p: BigUint,
  g: Element,
  f: Element,
  delta_p: BigInt,
}
impl ClassGroup {
  // https://eprint.iacr.org/2015/047 Figure 2
  // TODO: Replace with https://eprint.iacr.org/2021/291 Figure 2
  pub fn setup(rng: &mut (impl RngCore + CryptoRng), p: BigUint) -> Self {
    {
      let lambda = (RHO_BITS + P_BITS) / 2;
      assert!(lambda >= (P_BITS + 2));
    }

    let q = loop {
      assert_eq!(Uint::<{ RHO_BITS / 64 }>::BITS, RHO_BITS);
      let q = generate_safe_prime_with_rng::<{ RHO_BITS / 64 }>(&mut *rng, None);
      let q = BigUint::from_bytes_be(q.to_be_bytes().as_ref());
      // p * q is congruent to -1 mod 4
      if ((&p * &q) & BigUint::from(3u8)) != BigUint::from(3u8) {
        continue;
      }
      // jacobi of p/q = -1
      let q_minus_one = &q - 1u8;
      let exp = &q_minus_one >> 1;
      let res = p.modpow(&exp, &q);
      assert!((res.is_zero()) || (res.is_one()) || (res == q_minus_one));
      if res != q_minus_one {
        continue;
      }
      break q;
    };

    let delta_k = BigInt::from_biguint(Sign::Minus, &p * &q);

    let p_square = p.clone().pow(2u8);
    let delta_p = &delta_k * BigInt::from(p_square.clone());
    let f_a = BigInt::from_biguint(Sign::Plus, p_square.clone());
    let f_b = BigInt::from_biguint(Sign::Plus, p.clone());
    let f = Element { c: Element::c(&f_a, f_b.clone(), &delta_p).unwrap(), a: f_a, b: f_b };

    let r = loop {
      let r = generate_safe_prime_with_rng::<{ P_BITS / 64 }>(&mut *rng, None);
      let r = BigUint::from_bytes_be(r.to_be_bytes().as_ref());
      if r == p {
        continue;
      }

      let r_int = BigInt::from(r.clone());

      // jacobi of delta_k/r = 1
      let r_minus_one = &r_int - 1u8;
      let exp = &r_minus_one >> 1;
      let res = delta_k.mod_floor(&r_int).modpow(&exp, &r_int);
      assert!((res.is_zero()) || (res.is_one()) || (res == r_minus_one));
      if res.is_one() {
        break r;
      }
    };

    let k = loop {
      let mut k_bytes = vec![0; p.bits().div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut k_bytes);
      let k = BigUint::from_bytes_be(&k_bytes);
      if (k.is_zero()) || (k > p) {
        continue;
      }
      break k;
    };

    let abs_delta_k_cubed: BigUint = delta_k.abs().to_biguint().unwrap().pow(3u8);
    let mut quad_root = abs_delta_k_cubed.nth_root(4);
    // Make this a ceil quad root instead of a floor quad root with a binary search until overflow
    // TODO: Just use this from the get go, instead of the sqrt calls?
    let mut jump: BigUint = BigUint::from(1u8) << (((4096 + 2048) / 4) - 3);
    while !jump.is_zero() {
      while quad_root.clone().pow(4u8) < abs_delta_k_cubed {
        quad_root += &jump;
      }
      jump >>= 1;
      while quad_root.clone().pow(4u8) > abs_delta_k_cubed {
        quad_root -= &jump;
      }
      jump >>= 1;
    }
    assert!(quad_root.clone().pow(4u8) < abs_delta_k_cubed);
    quad_root += 1u8;
    assert!(quad_root.clone().pow(4u8) >= abs_delta_k_cubed);
    #[allow(non_snake_case)]
    let B = quad_root;

    #[allow(non_snake_case)]
    let L = L(r.pow(2u8), &p) * BigInt::from(p.clone());
    let g_init_a = p_square.into();
    let g_init =
      Element { c: Element::c(&g_init_a, L.clone(), &delta_p).unwrap(), a: g_init_a, b: L };
    let g = g_init.mul(&p).add(&f.mul(&k));

    ClassGroup { B, p, g, f, delta_p }
  }

  pub fn bound(&self) -> &BigUint {
    &self.B
  }
  pub fn p(&self) -> &BigUint {
    &self.p
  }
  pub fn g(&self) -> &Element {
    &self.g
  }
  pub fn f(&self) -> &Element {
    &self.f
  }
  pub fn delta_p(&self) -> &BigInt {
    &self.delta_p
  }

  // Sample a secret from the upper bound for the order multiplied by the prime field messages are
  // over, as specified in the original 2015-047 paper.
  //
  // Future papers frequently specify to sample B * 2**d, where d is the statistical distance
  // tolerance. Please be aware of this distinction.
  pub fn sample_secret(&self, rng: &mut (impl RngCore + CryptoRng)) -> BigUint {
    #[allow(non_snake_case)]
    let Bp = &self.B * &self.p;
    crate::sample_number_less_than(rng, &Bp)
  }

  pub fn key_gen(&self, rng: &mut (impl RngCore + CryptoRng)) -> (BigUint, Element) {
    let x = self.sample_secret(rng);
    let h = self.g.mul(&x);
    (x, h)
  }

  pub fn private_key_bits(&self) -> u64 {
    (&self.B * &self.p).bits()
  }

  pub fn encrypt(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    key: &Element,
    m: &BigUint,
  ) -> (BigUint, Ciphertext) {
    let r = self.sample_secret(rng);

    let c1 = self.g.mul(&r);
    let c2 = self.f.mul(m).add(&key.mul(&r));
    (r, Ciphertext(c1, c2))
  }

  #[allow(non_snake_case)]
  pub(crate) fn solve(&self, X: Element) -> Option<BigUint> {
    let p = BigInt::from(self.p.clone());
    let x = &X.b / &p;

    let gcd = p.extended_gcd(&x.mod_floor(&p));
    assert!(gcd.gcd.is_one());
    let inverse = if gcd.y.sign() == Sign::Plus { gcd.y } else { &p + gcd.y };
    assert!((&inverse * &x).mod_floor(&p).is_one());
    Some(inverse.to_biguint().unwrap())
  }

  pub fn decrypt(&self, key: &BigUint, ciphertext: &Ciphertext) -> Option<BigUint> {
    self.solve(ciphertext.1.add(&ciphertext.0.mul(key).neg()))
  }

  pub fn add(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    public_key: &Element,
    ciphertext: &Ciphertext,
    other: &Ciphertext,
  ) -> Ciphertext {
    let mut res = ciphertext.add_without_randomness(other);

    let r = self.sample_secret(rng);

    res.0 = res.0.add(&self.g.mul(&r));
    res.1 = res.1.add(&public_key.mul(&r));
    res
  }

  pub fn mul(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    public_key: &Element,
    ciphertext: &Ciphertext,
    scalar: &BigUint,
  ) -> Ciphertext {
    let mut res = ciphertext.mul_without_randomness(scalar);

    let r = self.sample_secret(rng);

    res.0 = res.0.add(&self.g.mul(&r));
    res.1 = res.1.add(&public_key.mul(&r));
    res
  }
}

#[test]
fn class_group() {
  use rand_core::OsRng;

  use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1};

  const LIMBS: usize = 256 / 64;
  let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
  let mut secp256k1_mod = [0; LIMBS * 8];
  secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
  secp256k1_mod[(LIMBS * 8) - 1] += 1;
  let secp256k1_mod = num_bigint::BigUint::from_be_bytes(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);

  let mut m1 = vec![0; 31];
  OsRng.fill_bytes(&mut m1);
  let m1 = num_bigint::BigUint::from_be_bytes(&m1);
  assert_eq!(cg.decrypt(&private_key, &cg.encrypt(&mut OsRng, &public_key, &m1).1).unwrap(), m1);

  let mut m2 = vec![0; 31];
  OsRng.fill_bytes(&mut m2);
  let m2 = num_bigint::BigUint::from_be_bytes(&m2);
  assert_eq!(cg.decrypt(&private_key, &cg.encrypt(&mut OsRng, &public_key, &m2).1).unwrap(), m2);

  assert_eq!(
    cg.decrypt(
      &private_key,
      &cg.add(
        &mut OsRng,
        &public_key,
        &cg.encrypt(&mut OsRng, &public_key, &m1).1,
        &cg.encrypt(&mut OsRng, &public_key, &m2).1,
      ),
    )
    .unwrap(),
    &m1 + &m2,
  );

  assert_eq!(
    cg.decrypt(
      &private_key,
      &cg.mul(&mut OsRng, &public_key, &cg.encrypt(&mut OsRng, &public_key, &m1).1, &m2)
    )
    .unwrap(),
    (&m1 * &m2) % &secp256k1_mod,
  );
}
