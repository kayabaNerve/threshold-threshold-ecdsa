use rand_core::{RngCore, CryptoRng};

use subtle::{ConstantTimeEq, ConstantTimeGreater};
use crypto_bigint::{
  CheckedAdd, CheckedSub, Random, Uint,
  modular::runtime_mod::{DynResidueParams, DynResidue},
};
use crypto_primes::generate_safe_prime_with_rng;

// This is insufficient in real life yet offers a sufficient message space for ever 512-bit curves
#[cfg(test)]
pub const PRIME_BITS: usize = 768;
#[cfg(not(test))]
pub const PRIME_BITS: usize = 1536;
pub const N_BITS: usize = PRIME_BITS * 2;
pub const N_2_BITS: usize = N_BITS * 2;

// TODO: Assert limb size is 64-bits
pub const PRIME_LIMBS: usize = PRIME_BITS / 64;
pub const N_LIMBS: usize = N_BITS / 64;
pub const N_2_LIMBS: usize = N_2_BITS / 64;

#[derive(Clone)]
pub struct PublicKey {
  pub n: Uint<N_LIMBS>,
  g: Uint<N_LIMBS>,
}

#[derive(Clone)]
pub struct PrivateKey {
  lambda: Uint<N_LIMBS>,
  mu: Uint<N_LIMBS>,
  public_key: PublicKey,
}

impl PrivateKey {
  pub fn new(rng: &mut (impl RngCore + CryptoRng)) -> (PrivateKey, PublicKey) {
    assert_eq!(Uint::<PRIME_LIMBS>::BITS, PRIME_BITS);

    let p: Uint<PRIME_LIMBS> = generate_safe_prime_with_rng(&mut *rng, None);
    let q: Uint<PRIME_LIMBS> = generate_safe_prime_with_rng(rng, None);
    let n = p * q;

    let g = n.checked_add(&Uint::ONE).unwrap();
    let phi = p.checked_sub(&Uint::ONE).unwrap().mul(&q.checked_sub(&Uint::ONE).unwrap());
    let lambda = phi;
    let (mu, mu_valid) = DynResidue::new(&phi, DynResidueParams::new(&n)).invert();
    assert!(bool::from(mu_valid));

    let public = PublicKey { n, g };
    (PrivateKey { lambda, mu: mu.retrieve(), public_key: public.clone() }, public)
  }

  #[allow(clippy::result_unit_err)]
  pub fn decrypt(&self, ciphertext: Uint<N_2_LIMBS>) -> Result<Uint<N_LIMBS>, ()> {
    let n_squared = DynResidueParams::new(&self.public_key.n.square());
    #[allow(non_snake_case)]
    let L_inner =
      DynResidue::new(&ciphertext, n_squared).pow(&self.lambda.mul(&Uint::ONE)).retrieve();
    let Some(x_minus_one) = Option::<Uint<N_2_LIMBS>>::from(L_inner.checked_sub(&Uint::ONE)) else {
      Err(())?
    };
    #[allow(non_snake_case)]
    let L_result_wide = x_minus_one.checked_div(&self.public_key.n.mul(&Uint::ONE)).unwrap();
    #[allow(non_snake_case)]
    let (L_result_high, L_result) = L_result_wide.split();
    assert_eq!(L_result_high, Uint::ZERO);

    let n = DynResidueParams::new(&self.public_key.n);
    Ok(DynResidue::new(&L_result, n).mul(&DynResidue::new(&self.mu, n)).retrieve())
  }
}

impl PublicKey {
  pub fn encrypt(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    message: Uint<N_LIMBS>,
  ) -> Option<Uint<N_2_LIMBS>> {
    if bool::from(message.ct_gt(&self.n) | message.ct_eq(&self.n)) {
      None?;
    }

    let r = loop {
      let candidate = Uint::<N_LIMBS>::random(&mut *rng);
      if bool::from(
        candidate.ct_eq(&Uint::ZERO) | candidate.ct_gt(&self.n) | candidate.ct_eq(&self.n),
      ) {
        continue;
      }
      break candidate;
    };

    let n_squared = DynResidueParams::new(&self.n.square());
    let g_mod_n_squared = DynResidue::new(&self.g.mul(&Uint::ONE), n_squared);
    let r_mod_n_squared = DynResidue::new(&r.mul(&Uint::ONE), n_squared);
    Some(
      g_mod_n_squared
        .pow(&message.mul(&Uint::ONE))
        .mul(&r_mod_n_squared.pow(&self.n.mul(&Uint::ONE)))
        .retrieve(),
    )
  }
}
