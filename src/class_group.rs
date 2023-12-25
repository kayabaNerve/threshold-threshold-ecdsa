use rand_core::{RngCore, CryptoRng};

use crypto_bigint::{Encoding, Uint};
use crypto_primes::generate_safe_prime_with_rng;

use num_traits::*;
use num_integer::*;
use num_bigint::*;

#[cfg(test)]
const RHO_BITS: usize = 640;
// delta k needs to be 1828 bits for 128-bit security
#[cfg(not(test))]
const RHO_BITS: usize = 1828;

const P_BITS: usize = 521;

#[allow(non_snake_case)]
fn L(m: BigUint, p_uint: &BigUint) -> BigInt {
  let m = BigInt::from(m.mod_floor(p_uint));
  let p = BigInt::from(p_uint.clone());

  // Invert m over p
  let gcd = p.extended_gcd(&m);
  assert!(gcd.gcd.is_one());
  let inverse = if gcd.y.sign() == Sign::Plus { gcd.y } else { p.clone() + gcd.y };
  assert!((inverse.clone() * &m).mod_floor(&p).is_one());
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
}

impl Element {
  // https://eprint.iacr.org/2015/047 V.2
  fn c(&self, delta: &BigInt) -> Option<BigInt> {
    // b**2 - 4ac = delta
    //  b**2 - delta = 4ac
    let four_ac: BigInt = self.b.clone().pow(2u8) - delta;
    if !(four_ac.clone() & BigInt::from(3u8)).is_zero() {
      None?
    }
    let ac = four_ac >> 2u8;
    let (res, rem) = ac.div_rem(&self.a);
    if !rem.is_zero() {
      None?
    }
    Some(res)
  }

  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  fn reduce(self, delta: &BigInt) -> Self {
    let mut c = self.c(delta).unwrap();
    let Element { mut a, mut b } = self;
    let step_2 = |a: &mut BigInt, b: &mut BigInt, c: &mut BigInt| {
      let two_a = a.clone() << 1;
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
    let res = Element { a, b };
    assert_eq!(res.c(delta).unwrap(), c);
    res
  }

  // Algorithm 5.4.7 of A Course in Computational Algebraic Number Theory
  fn add(&self, other: &Self, delta: &BigInt) -> Self {
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

    let c2 = f2.c(delta).unwrap();
    let v1 = &f1.a / &d1;
    let v2 = &f2.a / &d1;
    let r = ((&y1 * &y2 * &n) - (&x2 * &c2)).mod_floor(&v1);
    let b3 = &f2.b + ((&v2 * &r) << 1u8);
    let a3 = &v1 * &v2;
    let c3 = ((&c2 * &d1) + (&r * (&f2.b + (v2 * &r)))) / v1;

    let res = Element { a: a3, b: b3 };
    assert_eq!(res.c(delta).unwrap(), c3);
    res.reduce(delta)
  }

  fn double(&self, delta: &BigInt) -> Self {
    self.add(self, delta)
  }

  fn neg(self, delta: &BigInt) -> Self {
    Self { a: self.a, b: -self.b }.reduce(delta)
  }

  fn mul(&self, pow: &BigUint, delta: &BigInt) -> Self {
    let mut res: Option<Self> = None;
    for b in 0 .. pow.bits() {
      let b = pow.bits() - 1 - b;
      if let Some(res) = &mut res {
        *res = res.double(delta);
      }
      if pow.bit(b) {
        if let Some(res) = &mut res {
          *res = res.add(self, delta);
        } else {
          res = Some(self.clone());
        }
      }
    }
    res.unwrap()
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ciphertext(Element, Element);
impl Ciphertext {
  pub fn add(&self, other: &Ciphertext, delta: &BigInt) -> Self {
    Ciphertext(self.0.add(&other.0, delta), self.1.add(&other.1, delta))
  }
  pub fn mul(&self, scalar: &BigUint, delta: &BigInt) -> Self {
    Ciphertext(self.0.mul(scalar, delta), self.1.mul(scalar, delta))
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
  pub fn delta_p(&self) -> &BigInt {
    &self.delta_p
  }

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
      if ((p.clone() * &q) & BigUint::from(3u8)) != BigUint::from(3u8) {
        continue;
      }
      // jacobi of p/q = -1
      let q_minus_one = &q - 1u8;
      let exp = q_minus_one.clone() >> 1;
      let res = p.modpow(&exp, &q);
      assert!((res.is_zero()) || (res.is_one()) || (res == q_minus_one));
      if res != q_minus_one {
        continue;
      }
      break q;
    };

    println!("Generated q");

    let delta_k = BigInt::from_biguint(Sign::Minus, &p * &q);

    let p_square = p.clone().pow(2u8);
    let delta_p = delta_k.clone() * BigInt::from(p_square.clone());
    let f = Element {
      a: BigInt::from_biguint(Sign::Plus, p_square.clone()),
      b: BigInt::from_biguint(Sign::Plus, p.clone()),
    };
    assert!(f.c(&delta_p).is_some());

    let r = loop {
      let r = generate_safe_prime_with_rng::<{ P_BITS / 64 }>(&mut *rng, None);
      let r = BigUint::from_bytes_be(r.to_be_bytes().as_ref());
      if r == p {
        continue;
      }

      let r_int = BigInt::from(r.clone());

      // jacobi of delta_k/r = 1
      let r_minus_one = r_int.clone() - 1u8;
      let exp = r_minus_one.clone() >> 1;
      let res = delta_k.clone().mod_floor(&r_int).modpow(&exp, &r_int);
      assert!((res.is_zero()) || (res.is_one()) || (res == r_minus_one));
      if res.is_one() {
        break r;
      }
    };
    println!("Generated r");

    let k = loop {
      let mut k_bytes = vec![0; p.bits().div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut k_bytes);
      let k = BigUint::from_bytes_be(&k_bytes);
      if (k.is_zero()) || (k > p) {
        continue;
      }
      break k;
    };
    dbg!("Generated k");

    let abs_delta_k_cubed: BigUint = delta_k.abs().to_biguint().unwrap().pow(3u8);
    let mut quad_root = abs_delta_k_cubed.nth_root(4);
    dbg!("Calculated sqrts");
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
    dbg!("Calculated ceil quad root of cube");

    // N(am) = (L(m)**2 - delta_k) / 4
    // swirl(am) = N(am), -L(m)p

    // (p_square, L(m) * p)
    // g = ([swirl(r**2)] ** p) * (f ** k)
    #[allow(non_snake_case)]
    let L = L(r.pow(2u8), &p) * BigInt::from(p.clone());
    let g_init = Element { a: p_square.into(), b: L };
    assert!(g_init.c(&delta_p).is_some());
    let g = g_init.mul(&p, &delta_p).add(&f.mul(&k, &delta_p), &delta_p);

    ClassGroup { B, p, g, f: f.clone(), delta_p: delta_p.clone() }
  }

  pub fn key_gen(&self, rng: &mut (impl RngCore + CryptoRng)) -> (BigUint, Element) {
    #[allow(non_snake_case)]
    let Bp = &self.B * &self.p;
    let x = loop {
      let mut bytes = vec![0; Bp.bits().div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut bytes);
      let x = BigUint::from_bytes_be(&bytes);
      if x >= Bp {
        continue;
      }
      break x;
    };
    let h = self.g.mul(&x, &self.delta_p);
    (x, h)
  }

  pub fn encrypt(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    key: &Element,
    m: &BigUint,
  ) -> Ciphertext {
    #[allow(non_snake_case)]
    let Bp = &self.B * &self.p;
    let r = loop {
      let mut bytes = vec![0; Bp.bits().div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut bytes);
      let r = BigUint::from_bytes_be(&bytes);
      if r >= Bp {
        continue;
      }
      break r;
    };

    let c1 = self.g.mul(&r, &self.delta_p);
    let c2 = self.f.mul(m, &self.delta_p).add(&key.mul(&r, &self.delta_p), &self.delta_p);
    Ciphertext(c1, c2)
  }

  #[allow(non_snake_case)]
  fn solve(&self, X: Element) -> Option<BigUint> {
    let p = BigInt::from(self.p.clone());
    let x = &X.b / &p;

    let gcd = p.extended_gcd(&x.mod_floor(&p));
    assert!(gcd.gcd.is_one());
    let inverse = if gcd.y.sign() == Sign::Plus { gcd.y } else { p.clone() + gcd.y };
    assert!((inverse.clone() * &x).mod_floor(&p).is_one());
    Some(inverse.to_biguint().unwrap())
  }

  pub fn decrypt(&self, key: &BigUint, ciphertext: &Ciphertext) -> Option<BigUint> {
    self.solve(
      ciphertext.1.add(&ciphertext.0.mul(key, &self.delta_p).neg(&self.delta_p), &self.delta_p),
    )
  }
}
