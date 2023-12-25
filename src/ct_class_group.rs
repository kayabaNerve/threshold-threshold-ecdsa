use rand_core::{RngCore, CryptoRng};

use subtle::{Choice, ConstantTimeEq, ConstantTimeGreater, ConditionallySelectable};
use crypto_bigint::{
  CheckedAdd, CheckedSub, Random, Encoding, Integer as _, Uint, NonZero,
  modular::runtime_mod::{DynResidueParams, DynResidue},
};
use crypto_primes::generate_safe_prime_with_rng;

#[cfg(test)]
const RHO_BITS: usize = 640;
// delta k needs to be 1828 bits for 128-bit security
#[cfg(not(test))]
const RHO_BITS: usize = 1856;

// TODO: Assert limb size is 64-bits
const RHO_LIMBS: usize = RHO_BITS / 64;

const P_BITS: usize = 576;
const P_LIMBS: usize = P_BITS / 64;

const DISCRIMINANT_K_LIMBS: usize = RHO_LIMBS + P_LIMBS;
const DISCRIMINANT_P_LIMBS: usize = DISCRIMINANT_K_LIMBS + (2 * P_LIMBS);

fn shrink<const I: usize, const O: usize>(input: Uint<I>) -> Uint<O>
where
  Uint<I>: Encoding,
{
  if O > I {
    return (&input).into();
  }

  let bytes = input.to_be_bytes();
  let byte_boundary = (Uint::<I>::BITS - Uint::<O>::BITS) / 8;
  for b in &bytes.as_ref()[.. byte_boundary] {
    assert_eq!(*b, 0);
  }
  Uint::from_be_slice(&bytes.as_ref()[byte_boundary ..])
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sign {
  Positive,
  Negative,
}

impl ConditionallySelectable for Element {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Element { a: Uint::conditional_select(&a.a, &b.a, choice),
    b: Uint::conditional_select(&a.b, &b.b, choice) }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Integer(Sign, Uint<{ DISCRIMINANT_P_LIMBS * 2 }>);
impl Integer {
  fn add_in_bounds(&self, other: &Self) -> Self {
    if self.0 == other.0 {
      Integer(self.0, self.1.checked_add(&other.1).unwrap())
    } else if self.1 < other.1 {
    Integer(other.0, other.1.checked_sub(&self.1).unwrap())
  } else {
    Integer(self.0, self.1.checked_sub(&other.1).unwrap())
  }
  }
  fn sub_in_bounds(&self, other: &Self) -> Self {
    self.add_in_bounds(
      &(if other.0 == Sign::Positive {
        Integer(Sign::Negative, other.1)
      } else {
        Integer(Sign::Positive, other.1)
      }),
    )
  }
  fn mul_in_bounds(&self, other: &Self) -> Self {
    let res = self.1.saturating_mul(&other.1);
    assert_ne!(res, Uint::MAX);
    Integer(if self.0 == other.0 { Sign::Positive } else { Sign::Negative }, res)
  }
  fn floor_div_in_bounds(&self, other: &Self) -> Self {
    let res = self.1.checked_div(&other.1).unwrap();
    Integer(if self.0 == other.0 { Sign::Positive } else { Sign::Negative }, res)
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Element {
  a: Integer,
  b: Integer,
}

impl ConditionallySelectable for Element {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Element { a: Uint::conditional_select(&a.a, &b.a, choice),
    b: Uint::conditional_select(&a.b, &b.b, choice) }
  }
}

impl Element {
  // https://eprint.iacr.org/2015/047 V.2
  fn c(&self, neg_delta: Uint<DISCRIMINANT_P_LIMBS>) -> Option<Uint<DISCRIMINANT_P_LIMBS>> {
    // b**2 - 4ac = delta
    // -b**2 + 4ac = -delta
    let four_ac = Option::<Uint<DISCRIMINANT_P_LIMBS>>::from(
      neg_delta.checked_add(&(&self.b.square()).into()),
    )?;
    if four_ac.bitand(&3u8.into()) != Uint::ZERO {
      None?
    }
    let ac = four_ac.shr(2);
    let (res, rem) = four_ac.div_rem(&NonZero::new((&self.a).into()).unwrap());
    if rem != Uint::ZERO {
      None?
    }
    Some(res)
  }

  // Algorithm 5.4.7 of A Course in Computational Algebraic Number Theory
  fn mul(&self, other: &Self) -> Self {
    // Step 1
    let (f1, f2) = {
      let self_a_greater = self.a.ct_gt(&other.a);
      // The larger a should be f2
      let f1 = Element::conditional_select(other, self, self_a_greater);
      let f2 = Element::conditional_select(other, self, !self_a_greater);
      (f1, f2)
    };
    let s = f1.b.checked_add(&f2.b).unwrap().shr(1);
    let n = f2.b.checked_sub(&s);

    // Step 2
    // TODO: Use a constant time algorithm, such as binary GCD, or mask these
    // Extended Euclidean Algorithm
    let (u, v, d) = {
      let a = f2.a;
      let b = f1.a;
      let (old_r, r) = (a, b);
      let (old_s, s) = (Uint::ONE, Uint::ZERO);
      let (old_t, t) = (Uint::ZERO, Uint::ONE);
      while r != Uint::ZERO {
        let quotient = old_r.checked_div(&r).unwrap();
        (old_r, r) = (r, old_r.checked_sub(&quotient.saturating_mul(&r)).unwrap());
        (old_s, s) = (s, old_s.checked_sub(&quotient.saturating_mul(&s)).unwrap());
        (old_t, t) = (t, old_t.checked_sub(&quotient.saturating_mul(&t)).unwrap());
      }
      (old_s, old_t, old_r)
    };
    assert_eq!(u.saturating_mul(&f2.a).checked_add(&v.saturating_mul(&f1.a)).unwrap(), d);
    let y1 = u;

    let (u, v, d1) = {
      let a = s;
      let b = d;
      let (old_r, r) = (a, b);
      let (old_s, s) = (Uint::ONE, Uint::ZERO);
      let (old_t, t) = (Uint::ZERO, Uint::ONE);
      while r != Uint::ZERO {
        let quotient = old_r.checked_div(&r).unwrap();
        (old_r, r) = (r, old_r.checked_sub(&quotient.saturating_mul(&r)).unwrap());
        (old_s, s) = (s, old_s.checked_sub(&quotient.saturating_mul(&s)).unwrap());
        (old_t, t) = (t, old_t.checked_sub(&quotient.saturating_mul(&t)).unwrap());
      }
      (old_s, old_t, old_r)
    };
    assert_eq!(u.saturating_mul(&s).checked_add(&v.saturating_mul(&d)).unwrap(), d1);

    /* TODO
    let x2 = u;
    // TODO
    let y2 = -v;

    let v1 = a1.div(d1);
    let v2 = a2.div(d1);
    let r = y1 y2 n - x2 c2 mod v1;
    let b3 = b2 + 2 v2 r
    let a3 = v1 v2
    let c3 = (c2 d1 + r(b2 + v2 r))/v1
    reduce(a3, b3, c3)
    */

    todo!()
  }

  fn square(&self) -> Self {
    self.mul(self)
  }
}

pub struct ClassGroup {
  B: Uint<{ (4096 + 2048) / 4 / 64 }>,
  p: Uint<P_LIMBS>,
  g: Element,
  f: Element,
}
impl ClassGroup {
  // https://eprint.iacr.org/2015/047 Figure 2
  // TODO: Replace with https://eprint.iacr.org/2021/291 Figure 2
  pub fn setup(rng: &mut (impl RngCore + CryptoRng), original_p: Uint<P_LIMBS>) -> Self {
    {
      let lambda = (Uint::<RHO_LIMBS>::BITS + Uint::<P_LIMBS>::BITS) / 2;
      assert!(lambda >= (Uint::<P_LIMBS>::BITS + 2));
    }

    // Increase width
    let p: Uint<RHO_LIMBS> = (&original_p).into();

    let q = loop {
      let q = generate_safe_prime_with_rng::<RHO_LIMBS>(&mut *rng, None);
      // p * q is congruent to -1 mod 4
      if p.mul(&q).bitand(&Uint::from_u8(3)) != Uint::from_u8(3) {
        continue;
      }
      // jacobi of p/q = -1
      let Some(q_minus_one) = Option::<Uint<RHO_LIMBS>>::from(q.checked_sub(&Uint::ONE)) else {
        continue;
      };
      let exp = q_minus_one.checked_div(&2u8.into()).unwrap();
      let res = DynResidue::new(&p, DynResidueParams::new(&q)).pow(&exp).retrieve();
      assert!((res == Uint::ZERO) || (res == Uint::ONE) || (res == q_minus_one));
      if res != q_minus_one {
        continue;
      }
      break q;
    };

    println!("Generated q");

    let neg_delta_k = p.mul(&q);
    // Reduce neg_delta_k from (1856 * 2) bits to (1856 + P_BITS) bits
    assert!(Uint::<P_LIMBS>::BITS <= P_BITS);
    let neg_delta_k: Uint<{ DISCRIMINANT_K_LIMBS }> = shrink(neg_delta_k);

    let p_square = original_p.square();
    let neg_delta_p: Uint<{ DISCRIMINANT_P_LIMBS }> =
      shrink(neg_delta_k.mul(&Uint::<DISCRIMINANT_K_LIMBS>::from(&p_square)));
    let f = Element { a: (&p_square).into(), b: (&original_p).into() };
    assert!(f.c(neg_delta_p).is_some());

    let r = loop {
      let r = generate_safe_prime_with_rng::<P_LIMBS>(&mut *rng, None);
      if r == original_p {
        continue;
      }

      // jacobi of delta_k/r = 1
      let Some(r_minus_one) = Option::<Uint<P_LIMBS>>::from(r.checked_sub(&Uint::ONE)) else {
        continue;
      };
      let exp = r_minus_one.checked_div(&2u8.into()).unwrap();
      let delta_k = DynResidue::new(&neg_delta_k, DynResidueParams::new(&(&r).into())).neg();
      let res = delta_k.pow(&exp).retrieve();
      assert!((res == Uint::ZERO) || (res == Uint::ONE) || (res == (&r_minus_one).into()));
      if res == Uint::ONE {
        break r;
      }
    };
    println!("Generated r");

    let k = loop {
      let mut k = Uint::random(&mut *rng);
      k = k.shr(Uint::<P_LIMBS>::BITS - original_p.bits());
      if bool::from(k.ct_eq(&Uint::ZERO) | k.ct_gt(&original_p)) {
        continue;
      }
      break k;
    };
    dbg!("Generated k");

    let neg_delta_k_squared: Uint<{ 4096 / 64 }> = (&neg_delta_k.square()).into();
    let neg_delta_k_cubed =
      Uint::<{ (4096 + 2048) / 64 }>::from(&neg_delta_k_squared).saturating_mul(&neg_delta_k);
    let mut quad_root = {
      let a = neg_delta_k_cubed.sqrt_vartime().split();
      assert_eq!(a.0, Uint::ZERO);
      let b = a.1.sqrt_vartime().split();
      assert_eq!(b.0, Uint::ZERO);
      b.1
    };
    dbg!("Calculated sqrts");
    // Make this a ceil quad root instead of a floor quad root with a binary search until overflow
    // TODO: Just use this from the get go, instead of the sqrt calls?
    let mut jump = Uint::<{ ((4096 + 2048) / 4) / 64 }>::ONE.shl(((4096 + 2048) / 4) - 3);
    while jump != Uint::ZERO {
      while quad_root.square().square() < neg_delta_k_cubed {
        quad_root = quad_root.checked_add(&jump).unwrap(); // TODO <- Check safety of this
      }
      jump = jump.shr(1);
      while quad_root.square().square() > neg_delta_k_cubed {
        quad_root = quad_root.checked_sub(&jump).unwrap(); // TODO <- Check safety of this
      }
      jump = jump.shr(1);
    }
    assert!(quad_root.square().square() < neg_delta_k_cubed);
    quad_root = quad_root.checked_add(&Uint::ONE).unwrap();
    assert!(quad_root.square().square() >= neg_delta_k_cubed);
    let B = quad_root;
    dbg!("Calculated ceil quad root of cube");

    fn L(m: Uint<{ 2 * P_LIMBS }>, p: Uint<P_LIMBS>) -> Integer {
      let inverse = DynResidue::new(&m, DynResidueParams::new(&(&p).into()))
        .invert();
    assert!(bool::from(inverse.1));
    let inverse = inverse.0
        .retrieve()
        .split();
      assert_eq!(inverse.0, Uint::ZERO);
      let inverse = inverse.1;
      if bool::from(inverse.is_odd()) {
        Integer(Sign::Positive, inverse)
      } else {
        Integer(Sign::Negative, Integer(Sign::Positive, p.into()).sub_in_bounds(Integer(Sign::Positive, m)).1)
      }
    }

    // N(am) = (L(m)**2 - delta_k) / 4
    // swirl(am) = N(am), -L(m)p

    // (p_square, L(m) * p)
    // g = ([swirl(r**2)] ** p) * (f ** k)
    let L = L(r.square(), original_p);
    let L = L.mul_in_bounds(&Integer(Sign::Positive, p.into()));
    // TODO: How do we handle L is negative?
    let g_init = Element { a: Integer(Sign::Positive, (&p_square).into()), b: L };
    assert!(g_init.c(neg_delta_p).is_some());
    let g = todo!("g_init**p * f**k");

    ClassGroup { B, p: original_p, g, f }
  }
}
