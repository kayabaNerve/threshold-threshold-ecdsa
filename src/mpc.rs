use rand_core::{RngCore, CryptoRng};

use num_traits::One;
use num_bigint::BigUint;

use crate::class_group::*;

pub struct IntegerSecretSharing {}
impl IntegerSecretSharing {
  pub fn new(rng: &mut (impl RngCore + CryptoRng), cg: &ClassGroup, t: u16, n: u16) {
    let mut gen_coefficient = || {
      // TODO: This uses the same size for all coefficients
      // 2022-1437 distinguishes secret size and coefficient size.
      let secret_bits = cg.private_key_bits() - 1;
      let mut secret = vec![0; secret_bits.div_ceil(8).try_into().unwrap()];
      rng.fill_bytes(&mut secret);
      secret[0] &= 0xff >> (8 - (secret_bits % 8));
      BigUint::from_bytes_be(&secret)
    };

    let alpha = gen_coefficient();
    let delta = {
      let mut accum = BigUint::one();
      for i in 2 ..= n {
        accum *= i;
      }
      accum
    };
    let alpha_tilde = &alpha * &delta;

    let mut r = vec![];
    for _ in 1 ..= (t - 1) {
      r.push(gen_coefficient());
    }

    let f = |i: u16| {
      &alpha_tilde +
        r.iter()
          .enumerate()
          .map(|(r_i, r)| r * i.pow((r_i + 1).try_into().unwrap()))
          .sum::<BigUint>()
    };

    let mut y = vec![];
    for i in 1 ..= n {
      y.push(f(i));
    }

    #[allow(non_snake_case)]
    let mut C = vec![];
    C.push(cg.g().mul(&alpha));
    for r in &r {
      C.push(cg.g().mul(&(r * &delta)));
    }
    // TODO: Also create ZK PoKs for all C per 5.2

    for (i, y) in y.iter().enumerate() {
      let i = i + 1;
      let mut eval = C[0].mul(&(&delta * &delta));
      #[allow(non_snake_case)]
      for (C_i, C) in C[1 ..].iter().enumerate() {
        let C_i = C_i + 1;
        eval = eval.add(&C.mul(&i.pow(C_i.try_into().unwrap()).into()));
      }
      assert_eq!(cg.g().mul(&(y * &delta)), eval);
    }
  }
}
