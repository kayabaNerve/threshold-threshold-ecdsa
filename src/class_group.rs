use rand_core::{RngCore, CryptoRng};

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_safe_prime_with_rng;

use num_traits::{Zero, One, Signed, Pow, Euclid};
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
fn L(m: BigUint, p: &BigUint) -> BigInt {
  // Invert m over p
  let inverse = m.modpow(&(p - 2u8), p);
  if inverse.is_odd() {
    inverse.into()
  } else {
    BigInt::from_biguint(Sign::Minus, p - inverse)
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Element {
  a: BigInt,
  b: BigInt,
  c: BigInt,
  L: BigInt,
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
    // b**2 - discriminant = 4ac
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

  pub fn reduce(self) -> Self {
    let Element { mut a, mut b, mut c, L } = self;

    let normalize = |a: &mut BigInt, b: &mut BigInt, c: &mut BigInt| {
      let (mut q, mut r) = (b.div_euclid(&*a), b.rem_euclid(&*a));
      if q.is_odd() {
        r += &*a;
      }
      q >>= 1;
      std::mem::swap(b, &mut r);
      r += &*b;
      r >>= 1;
      *c -= q * r;
    };

    normalize(&mut a, &mut b, &mut c);
    while a > c {
      std::mem::swap(&mut a, &mut c);
      b = -b;
      normalize(&mut a, &mut b, &mut c);
    }
    if (a == c) && b.is_negative() {
      b = -b;
    }

    Element { a, b, c, L }
  }

  // Algorithm 5.4.9 of A Course in Computational Algebraic Number Theory
  pub fn add(&self, other: &Self) -> Self {
    if self.is_identity() {
      return other.clone();
    }
    if other.is_identity() {
      return self.clone();
    }

    let L = &self.L;

    let (f1, f2) = if self.a < other.a { (other, self) } else { (self, other) };
    let mut s = (&f1.b + &f2.b) >> 1u8;
    let n = &f2.b - &s;

    let ExtendedGcd { x: u, y: v, gcd: mut d } = f2.a.extended_gcd(&f1.a);
    debug_assert_eq!((&u * &f2.a) + (&v * &f1.a), d);

    let mut a1 = f1.a.clone();
    let mut a2 = f2.a.clone();

    let (A, d1) = if d.is_one() {
      let A = -u * &n;
      let d1 = d;
      (A, d1)
    } else if s.mod_floor(&d).is_zero() {
      let A = -u * &n;
      let d1 = d;
      a1 /= &d1;
      a2 /= &d1;
      s /= &d1;
      (A, d1)
    } else {
      let ExtendedGcd { x: u1, y: _, gcd: d1 } = s.extended_gcd(&d);
      if d1 > BigInt::one() {
        a1 /= &d1;
        a2 /= &d1;
        s /= &d1;
        d /= &d1;
      }

      let l = (&u * f1.c.mod_floor(&d)) + (v * f2.c.mod_floor(&d));
      let l = (&u1 * l).mod_floor(&d);
      let l = &d - l;
      let A = (&l * (&a1 / &d)) - (u * (&n / &d));
      (A, d1)
    };

    let mut A = A.mod_floor(&a1);
    let A1 = &a1 - &A;
    if A1 < A {
      A = -A1;
    }

    let parteucl = |a: BigInt, b: BigInt| {
      let mut v = BigInt::zero();
      let mut d = a;
      let mut v2 = BigInt::one();
      let mut v3 = b;
      let mut z = BigInt::zero();
      while v3.abs() > *L {
        let (q, t3) = (d.div_euclid(&v3), d.rem_euclid(&v3));
        debug_assert_eq!(t3.sign(), Sign::Plus);
        let t2 = &v - (&q * &v2);
        v = v2;
        d = v3;
        v2 = t2;
        v3 = t3;
        z += 1;
      }
      if z.is_odd() {
        v2 = -v2;
        v3 = -v3;
      }
      (v, d, v2, v3, z)
    };

    let (mut v, d, mut v2, v3, z) = parteucl(a1.clone(), A);

    if z.is_zero() {
      let Q1 = &a2 * &v3;
      let Q2 = &Q1 + &n;
      let f = &Q2 / &d;
      let g = ((&v3 * &s) + &f2.c) / &d;
      let a3 = &d * &a2;
      let c3 = (&v3 * &f) + (&g * &d1);
      let b3 = (Q1 << 1) + &f2.b;
      return (Element { a: a3, b: b3, c: c3, L: self.L.clone() }).reduce();
    }

    let b = ((&a2 * &d) + (&n * &v)) / &a1;
    let Q1 = &b * &v3;
    let Q2 = &Q1 + &n;
    let f = &Q2 / &d;
    let e = ((&s * &d) + (&f2.c * &v)) / &a1;
    let Q3 = &e * &v2;
    let Q4 = &Q3 - &s;
    let g = &Q4 / &v;
    if d1 > BigInt::one() {
      v2 = &d1 * &v2;
      v = &d1 * &v;
    }

    let a3 = (&d * &b) + (&e * &v);
    let c3 = (&v3 * &f) + (&g * &v2);
    let b3 = (&Q1 + &Q2) + (&d1 * (&Q3 + &Q4));
    (Element { a: a3, b: b3, c: c3, L: self.L.clone() }).reduce()
  }

  // Algorithm 5.4.8 of A Course in Computational Algebraic Number Theory
  pub fn double(&self) -> Self {
    let L = &self.L;

    let ExtendedGcd { x: u, y: v, gcd: d1 } = self.b.extended_gcd(&self.a);
    debug_assert_eq!((&u * &self.b) + (&v * &self.a), d1);
    let A = &self.a / &d1;
    let B = &self.b / &d1;
    let mut C = -(&self.c * &u).mod_floor(&A);
    let C1 = &A - &C;
    if C1 < C {
      C = -C1;
    }

    let parteucl = |a: BigInt, b: BigInt| {
      let mut v = BigInt::zero();
      let mut d = a;
      let mut v2 = BigInt::one();
      let mut v3 = b;
      let mut z = BigInt::zero();
      while v3.abs() > *L {
        let (q, t3) = (d.div_euclid(&v3), d.rem_euclid(&v3));
        let t2 = &v - (&q * &v2);
        v = v2;
        d = v3;
        v2 = t2;
        v3 = t3;
        z += 1;
      }
      if z.is_odd() {
        v2 = -v2;
        v3 = -v3;
      }
      (v, d, v2, v3, z)
    };

    let (mut v, d, mut v2, v3, z) = parteucl(A.clone(), C);
    if z.is_zero() {
      let g = ((&B * &v3) + &self.c) / &d;
      let a2 = &d * &d;
      let c2 = &v3 * &v3;
      let b2_part = &d + &v3;
      let b2 = &self.b + (&b2_part * &b2_part) - &a2 - &c2;
      let c2 = &c2 + (&g * &d1);
      return (Element { a: a2, b: b2, c: c2, L: self.L.clone() }).reduce();
    }

    let e = ((&self.c * &v) + (&B * &d)) / &A;
    let g = ((&e * &v2) - &B) / &v;
    let mut b2 = (&e * &v2) + (&v * &g);
    if d1 > BigInt::one() {
      b2 = &d1 * &b2;
      v = &d1 * &v;
      v2 = &d1 * &v2;
    }
    let a2 = &d * &d;
    let c2 = &v3 * &v3;
    let b2_part = &d + &v3;
    let b2 = &b2 + (&b2_part * &b2_part) - &a2 - &c2;
    let a2 = &a2 + (&e * &v);
    let c2 = &c2 + (&g * &v2);
    (Element { a: a2, b: b2, c: c2, L: self.L.clone() }).reduce()
  }

  pub fn neg(self) -> Self {
    Self { a: self.a, b: -self.b, c: self.c, L: self.L.clone() }.reduce()
  }

  pub fn small_table(&self) -> Table {
    let mut table = core::array::from_fn::<_, 31, _>(|_| self.clone());
    for i in 2 .. 32 {
      table[i - 1] = table[i - 2].add(self);
    }
    Table::Small(SmallTable(table).into())
  }

  pub fn large_table(&self) -> Table {
    let mut table = core::array::from_fn::<_, 1023, _>(|_| self.clone());
    for i in 2 .. 1024 {
      table[i - 1] = table[i - 2].add(self);
    }
    Table::Large(LargeTable(table).into())
  }

  pub fn mul(&self, scalar: &BigUint) -> Self {
    if self.is_identity() {
      return self.clone();
    }

    let table = self.small_table();
    table * scalar
  }

  pub fn is_identity(&self) -> bool {
    self.a.is_one() && self.b.is_one()
  }
}

pub struct SmallTable(pub(crate) [Element; 31]);
impl core::ops::Mul<&BigUint> for &SmallTable {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    // TODO: Return identity on 0 scalar
    let mut res: Option<Element> = None;

    let mut bits = 0;
    for b in 0 .. scalar.bits() {
      let full_bits = (b % 5) == 4;
      let b = scalar.bits() - 1 - b;
      bits <<= 1;
      bits |= u16::from(scalar.bit(b));
      if full_bits {
        if let Some(res) = &mut res {
          for _ in 0 .. 5 {
            *res = res.double();
          }
        }
        if bits == 0 {
          continue;
        }
        let to_add = &self.0[usize::from(bits) - 1];
        bits = 0;
        if let Some(res) = &mut res {
          *res = res.add(to_add);
        } else {
          res = Some(to_add.clone());
        }
      }
    }
    if let Some(res) = &mut res {
      for _ in 0 .. (scalar.bits() % 5) {
        *res = res.double();
      }
    }
    if bits != 0 {
      let to_add = &self.0[usize::from(bits) - 1];
      if let Some(res) = &mut res {
        *res = res.add(to_add);
      } else {
        res = Some(to_add.clone());
      }
    }
    res.unwrap()
  }
}
impl core::ops::Mul<&BigUint> for SmallTable {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    &self * scalar
  }
}

pub struct LargeTable(pub(crate) [Element; 1023]);
impl core::ops::Mul<&BigUint> for &LargeTable {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    // TODO: Return identity on 0 scalar
    let mut res: Option<Element> = None;

    let mut bits: u16 = 0;
    for b in 0 .. scalar.bits() {
      let full_bits = (b % 10) == 9;
      let b = scalar.bits() - 1 - b;
      bits <<= 1;
      bits |= u16::from(scalar.bit(b));
      if full_bits {
        if let Some(res) = &mut res {
          for _ in 0 .. 10 {
            *res = res.double();
          }
        }
        if bits == 0 {
          continue;
        }
        let to_add = &self.0[usize::from(bits) - 1];
        bits = 0;
        if let Some(res) = &mut res {
          *res = res.add(to_add);
        } else {
          res = Some(to_add.clone());
        }
      }
    }
    if let Some(res) = &mut res {
      for _ in 0 .. (scalar.bits() % 10) {
        *res = res.double();
      }
    }
    if bits != 0 {
      let to_add = &self.0[usize::from(bits) - 1];
      if let Some(res) = &mut res {
        *res = res.add(to_add);
      } else {
        res = Some(to_add.clone());
      }
    }
    res.unwrap()
  }
}
impl core::ops::Mul<&BigUint> for LargeTable {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    &self * scalar
  }
}

pub enum Table {
  Small(Box<SmallTable>),
  Large(Box<LargeTable>),
}
impl core::ops::Mul<&BigUint> for &Table {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    match self {
      Table::Small(table) => &**table * scalar,
      Table::Large(table) => &**table * scalar,
    }
  }
}
impl core::ops::Mul<&BigUint> for Table {
  type Output = Element;
  fn mul(self, scalar: &BigUint) -> Element {
    &self * scalar
  }
}

impl core::ops::Index<usize> for Table {
  type Output = Element;
  fn index(&self, index: usize) -> &Element {
    match self {
      Table::Small(table) => &table.0[index],
      Table::Large(table) => &table.0[index],
    }
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

pub struct ClassGroup {
  B: BigUint,
  p: BigUint,
  identity: Element,
  g_table: Table,
  f_table: Table,
  delta_p: BigInt,
}
impl ClassGroup {
  // https://eprint.iacr.org/2015/047 Figure 2
  // TODO: Replace with https://eprint.iacr.org/2021/291 Figure 2
  pub fn setup(rng: &mut (impl RngCore + CryptoRng), p: BigUint) -> Self {
    {
      let lambda = (RHO_BITS + P_BITS) / 2;
      debug_assert!(lambda >= (P_BITS + 2));
    }

    let q = loop {
      debug_assert_eq!(Uint::<{ RHO_BITS / 64 }>::BITS, RHO_BITS);
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
      debug_assert!((res.is_zero()) || (res.is_one()) || (res == q_minus_one));
      if res != q_minus_one {
        continue;
      }
      break q;
    };

    let delta_k = BigInt::from_biguint(Sign::Minus, &p * &q);

    let p_square = p.clone().pow(2u8);
    let delta_p = &delta_k * BigInt::from(p_square.clone());

    let double_L: BigInt = &delta_p >> 2;
    let double_L = double_L.abs().sqrt().sqrt();

    let f_a = BigInt::from_biguint(Sign::Plus, p_square.clone());
    let f_b = BigInt::from_biguint(Sign::Plus, p.clone());
    let f = Element {
      c: Element::c(&f_a, f_b.clone(), &delta_p).unwrap(),
      a: f_a,
      b: f_b,
      L: double_L.clone(),
    };

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
      debug_assert!((res.is_zero()) || (res.is_one()) || (res == r_minus_one));
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
    debug_assert!(quad_root.clone().pow(4u8) < abs_delta_k_cubed);
    quad_root += 1u8;
    debug_assert!(quad_root.clone().pow(4u8) >= abs_delta_k_cubed);
    let B = quad_root;

    let L = L(r.pow(2u8), &p) * BigInt::from(p.clone());
    let g_init_a = p_square.into();
    let g_init = Element {
      c: Element::c(&g_init_a, L.clone(), &delta_p).unwrap(),
      a: g_init_a,
      b: L,
      L: double_L.clone(),
    };
    let f_table = f.large_table();
    let g = multiexp(&mut [p.clone(), k.clone()], &[&g_init], &[&f_table]);

    ClassGroup {
      B,
      p,
      identity: Element {
        a: BigInt::one(),
        b: BigInt::one(),
        c: Element::c(&BigInt::one(), BigInt::one(), &delta_p).unwrap(),
        L: double_L.clone(),
      },
      g_table: g.large_table(),
      f_table,
      delta_p,
    }
  }

  pub fn bound(&self) -> &BigUint {
    &self.B
  }
  pub fn p(&self) -> &BigUint {
    &self.p
  }
  pub fn identity(&self) -> &Element {
    &self.identity
  }
  pub fn g_table(&self) -> &Table {
    &self.g_table
  }
  pub fn f_table(&self) -> &Table {
    &self.f_table
  }
  pub fn delta_p(&self) -> &BigInt {
    &self.delta_p
  }

  // Returns the upper bound for the order multiplied by the prime field messages are over, as used
  // as the bound for secrets by the original 2015-047 paper.
  pub fn secret_bound(&self) -> BigUint {
    &self.B * &self.p
  }

  // Sample a secret from the upper bound for the order multiplied by the prime field messages are
  // over, as specified in the original 2015-047 paper.
  //
  // Future papers frequently specify to sample B * 2**d, where d is the statistical distance
  // tolerance. Please be aware of this distinction.
  pub fn sample_secret(&self, rng: &mut (impl RngCore + CryptoRng)) -> BigUint {
    let Bp = self.secret_bound();
    crate::sample_number_less_than(rng, &Bp)
  }

  pub fn key_gen(&self, rng: &mut (impl RngCore + CryptoRng)) -> (BigUint, Element) {
    let x = self.sample_secret(rng);
    let h = &self.g_table * &x;
    (x, h)
  }

  pub fn secret_bits(&self) -> u64 {
    (&self.B * &self.p).bits()
  }

  pub fn encrypt_with_randomness(
    &self,
    key: &Element,
    randomness: &BigUint,
    message: &BigUint,
  ) -> Ciphertext {
    let c1 = &self.g_table * randomness;
    let c2 = multiexp(&mut [randomness.clone(), message.clone()], &[&key], &[&self.f_table]);
    Ciphertext(c1, c2)
  }

  pub fn encrypt(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    key: &Element,
    m: &BigUint,
  ) -> (BigUint, Ciphertext) {
    let r = self.sample_secret(rng);
    let ciphertext = self.encrypt_with_randomness(key, &r, m);
    (r, ciphertext)
  }

  pub(crate) fn solve(&self, X: Element) -> Option<BigUint> {
    let p = &self.p;
    let p_int = BigInt::from_biguint(Sign::Plus, p.clone());
    let x = ((&X.b / &p_int).mod_floor(&p_int)).to_biguint().unwrap();
    if x.is_zero() {
      None?
    }
    let inverse = x.modpow(&(p - 2u8), p);
    debug_assert!((&inverse * &x).mod_floor(p).is_one());
    Some(inverse)
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

    res.0 = res.0.add(&(&self.g_table * &r));
    res.1 = res.1.add(&public_key.mul(&r));
    res
  }

  pub fn mul(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    public_key: &Element,
    ciphertext: &Ciphertext,
    scalar: &BigUint,
  ) -> (BigUint, Ciphertext) {
    let mut res = ciphertext.mul_without_randomness(scalar);

    let r = self.sample_secret(rng);

    res.0 = res.0.add(&(&self.g_table * &r));
    res.1 = res.1.add(&public_key.mul(&r));
    (r, res)
  }
}

pub(crate) fn multiexp(
  scalars: &mut [BigUint],
  elements: &[&Element],
  precomputed_tables: &[&Table],
) -> Element {
  assert_eq!(scalars.len(), elements.len() + precomputed_tables.len());

  // Deduplicate common elements/tables
  let mut matches;
  for i in 0 .. scalars.len() {
    matches = std::collections::HashSet::new();
    for j in (i + 1) .. scalars.len() {
      if scalars[j].is_zero() {
        continue;
      }
      if (i < elements.len()) && (j >= elements.len()) {
        break;
      }
      if ((i < elements.len()) && (elements[i] == elements[j])) ||
        ((i >= elements.len()) &&
          (precomputed_tables[i - elements.len()][0] ==
            precomputed_tables[j - elements.len()][0]))
      {
        matches.insert(j);
      }
    }
    for j in matches {
      let value = scalars[j].clone();
      scalars[j] = BigUint::zero();
      scalars[i] += value;
    }
  }

  let mut tables_literal = Vec::with_capacity(elements.len());
  for (i, element) in elements.iter().enumerate() {
    if scalars[i].is_zero() {
      // Don't create an actual table if this is a 0 scalar
      tables_literal
        .push(Table::Small(SmallTable(core::array::from_fn(|_| (*element).clone())).into()));
    } else {
      tables_literal.push(element.small_table());
    }
  }
  let mut tables = Vec::with_capacity(scalars.len());
  for table in &tables_literal {
    tables.push(table);
  }
  for table in precomputed_tables {
    tables.push(table);
  }
  assert_eq!(scalars.len(), tables.len());

  // TODO: Return identity on None
  let mut res: Option<Element> = None;

  let mut scalar_bits = scalars.iter().map(|scalar| scalar.bits()).collect::<Vec<_>>();
  scalar_bits.sort_unstable();
  let scalar_bits = scalar_bits.pop().unwrap();

  let mut bits = vec![0u16; tables.len()];
  for b in 0 .. scalar_bits {
    for i in 0 .. tables.len() {
      if (i == 0) && ((b % 5) == 4) {
        if let Some(res) = &mut res {
          for _ in 0 .. 5 {
            *res = res.double();
          }
        }
      }

      if (i < elements.len()) && elements[i].is_identity() {
        continue;
      }

      let full_short_bits = (b % 5) == 4;
      let full_long_bits = (b % 10) == 9;
      let full_bits =
        if matches!(&tables[i], Table::Large(_)) { full_long_bits } else { full_short_bits };
      let b = scalar_bits - 1 - b;
      bits[i] <<= 1;
      bits[i] |= if b > scalars[i].bits() { continue } else { u16::from(scalars[i].bit(b)) };
      if (full_bits) && (bits[i] != 0) {
        let to_add = &tables[i][usize::from(bits[i]) - 1];
        bits[i] = 0;
        if let Some(res) = &mut res {
          *res = res.add(to_add);
        } else {
          res = Some(to_add.clone());
        }
      }
    }
  }
  if let Some(res) = &mut res {
    for _ in 0 .. (scalar_bits % 5) {
      *res = res.double();
    }
  }
  for (i, bits) in bits.into_iter().enumerate() {
    if bits != 0 {
      let to_add = &tables[i][usize::from(bits) - 1];
      if let Some(res) = &mut res {
        *res = res.add(to_add);
      } else {
        res = Some(to_add.clone());
      }
    }
  }
  res.unwrap()
}

pub struct BatchVerifier<'a> {
  pub(crate) borrowed_pairs: Vec<(BigUint, &'a Element)>,
  pub(crate) pairs: Vec<(BigUint, Element)>,
  pub(crate) tabled_pairs: Vec<(BigUint, &'a Table)>,
}
impl<'a> BatchVerifier<'a> {
  pub fn new() -> Self {
    BatchVerifier { borrowed_pairs: vec![], pairs: vec![], tabled_pairs: vec![] }
  }

  pub(crate) fn queue<'s>(
    &mut self,
    borrowed_pairs: impl IntoIterator<Item = (&'s BigUint, &'a Element)>,
    pairs: impl IntoIterator<Item = (&'s BigUint, Element)>,
    tabled_pairs: impl IntoIterator<Item = (&'s BigUint, &'a Table)>,
  ) {
    let weight = if self.borrowed_pairs.is_empty() && self.pairs.is_empty() {
      BigUint::one()
    } else {
      let mut batch_weight = [0; 16];
      // TODO: Take in an RNG
      rand_core::OsRng.fill_bytes(&mut batch_weight);
      BigUint::from_bytes_be(&batch_weight)
    };

    for borrowed_pair in borrowed_pairs {
      self.borrowed_pairs.push((borrowed_pair.0 * &weight, borrowed_pair.1));
    }
    for pair in pairs {
      self.pairs.push((pair.0 * &weight, pair.1));
    }
    for pair in tabled_pairs {
      self.tabled_pairs.push((pair.0 * &weight, pair.1));
    }
  }
  pub(crate) fn verify(self) -> bool {
    // TODO: Remove once we return identity
    if self.borrowed_pairs.is_empty() && self.pairs.is_empty() && self.tabled_pairs.is_empty() {
      return true;
    }

    let mut all_scalars =
      Vec::with_capacity(self.borrowed_pairs.len() + self.pairs.len() + self.tabled_pairs.len());
    let mut all_elements = Vec::with_capacity(self.borrowed_pairs.len() + self.pairs.len());
    let mut tables = Vec::with_capacity(self.tabled_pairs.len());
    for pair in self.borrowed_pairs {
      all_scalars.push(pair.0);
      all_elements.push(pair.1);
    }
    for pair in &self.pairs {
      all_scalars.push(pair.0.clone());
      all_elements.push(&pair.1);
    }
    for pair in &self.tabled_pairs {
      all_scalars.push(pair.0.clone());
      tables.push(pair.1);
    }
    multiexp(&mut all_scalars, &all_elements, &tables).is_identity()
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
  let secp256k1_mod = num_bigint::BigUint::from_bytes_be(&secp256k1_mod);

  let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
  let (private_key, public_key) = cg.key_gen(&mut OsRng);

  let mut m1 = vec![0; 31];
  OsRng.fill_bytes(&mut m1);
  let m1 = num_bigint::BigUint::from_bytes_be(&m1);
  assert_eq!(cg.decrypt(&private_key, &cg.encrypt(&mut OsRng, &public_key, &m1).1).unwrap(), m1);

  let mut m2 = vec![0; 31];
  OsRng.fill_bytes(&mut m2);
  let m2 = num_bigint::BigUint::from_bytes_be(&m2);
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
      &cg.mul(&mut OsRng, &public_key, &cg.encrypt(&mut OsRng, &public_key, &m1).1, &m2).1,
    )
    .unwrap(),
    (&m1 * &m2) % &secp256k1_mod,
  );
}
