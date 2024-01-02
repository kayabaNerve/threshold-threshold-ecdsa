use rand_core::{RngCore, CryptoRng};

use num_bigint::BigUint;

use ciphersuite::{
  group::{ff::PrimeField, Group},
  Ciphersuite, Secp256k1,
};
use elliptic_curve::point::AffineCoordinates;

pub mod class_group;
pub mod proofs;
pub mod mpc;

pub fn sample_number_less_than(rng: &mut (impl RngCore + CryptoRng), bound: &BigUint) -> BigUint {
  loop {
    let mut bytes = vec![0; bound.bits().div_ceil(8).try_into().unwrap()];
    rng.fill_bytes(&mut bytes);
    let x = BigUint::from_bytes_be(&bytes);
    if x >= *bound {
      continue;
    }
    break x;
  }
}

pub fn verify(
  public_key: <Secp256k1 as Ciphersuite>::G,
  m1_hash: <Secp256k1 as Ciphersuite>::F,
  r: <Secp256k1 as Ciphersuite>::F,
  s: <Secp256k1 as Ciphersuite>::F,
) {
  assert_ne!(r, <Secp256k1 as Ciphersuite>::F::ZERO);
  assert_ne!(s, <Secp256k1 as Ciphersuite>::F::ZERO);

  let z = m1_hash;
  let u1 = z * s.invert().unwrap();
  let u2 = r * s.invert().unwrap();
  let point = (Secp256k1::generator() * u1) + (public_key * u2);
  assert!(!bool::from(point.is_identity()));
  assert_eq!(r.to_repr(), point.to_affine().x());

  ecdsa::hazmat::verify_prehashed(
    &public_key,
    &m1_hash.to_repr(),
    &ecdsa::Signature::<k256::Secp256k1>::from_scalars(r, s).unwrap(),
  )
  .unwrap()
}

#[cfg(test)]
mod tests {
  use rand_core::OsRng;
  use crypto_bigint::*;
  use ciphersuite::group::ff::Field;
  use super::*;

  #[test]
  fn non_distributed() {
    let private_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

    let x = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let y = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let z = x * y;
    let d = private_key * y;

    let r = <Secp256k1 as Ciphersuite>::F::from_repr((Secp256k1::generator() * x).to_affine().x())
      .unwrap();

    let m1_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let w = (m1_hash * y) + (r * d);
    let s = w * z.invert().unwrap();

    verify(Secp256k1::generator() * private_key, m1_hash, r, s);
  }

  #[test]
  pub fn protocol() {
    use std::collections::HashMap;

    use transcript::{Transcript, RecommendedTranscript};

    use num_traits::{Zero, One, FromBytes};
    use num_integer::Integer;
    use num_bigint::BigInt;

    use class_group::*;
    use proofs::*;
    use mpc::*;

    const LIMBS: usize = 256 / 64;
    let secp256k1_neg_one = -<Secp256k1 as Ciphersuite>::F::ONE;
    let mut secp256k1_mod = [0; LIMBS * 8];
    secp256k1_mod[((LIMBS * 8) - 32) ..].copy_from_slice(&secp256k1_neg_one.to_repr());
    secp256k1_mod[(LIMBS * 8) - 1] += 1;
    let secp256k1_mod = BigUint::from_be_bytes(&secp256k1_mod);

    let cg = ClassGroup::setup(&mut OsRng, secp256k1_mod.clone());
    let transcript = || RecommendedTranscript::new(b"Protocol Test");
    let mut shares = HashMap::new();
    for i in 1u16 ..= 4u16 {
      shares.insert(i, BigUint::zero());
    }
    let mut delta = None;
    let mut public_key: Option<Element> = None;
    let mut verification_shares = HashMap::new();
    for _ in 1u16 ..= 4u16 {
      let iss = IntegerSecretSharing::new(&mut OsRng, &cg, &mut transcript(), 3, 4);
      if delta.is_none() {
        delta = Some(iss.delta.clone());
      }
      assert_eq!(delta.as_ref(), Some(&iss.delta));
      let contribution = &iss.commitments[0].commitment;
      if let Some(public_key) = &mut public_key {
        for i in 1u16 ..= 4u16 {
          let mut eval = iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta));
          #[allow(non_snake_case)]
          for (C_i, C) in iss.commitments[1 ..].iter().enumerate() {
            let C_i = C_i + 1;
            let i = BigUint::from(i);
            eval = eval.add(&C.commitment.mul(&i.pow(u32::try_from(C_i).unwrap())));
          }
          let existing: &mut Element = verification_shares.get_mut(&i).unwrap();
          let new = existing.add(&eval);
          *existing = new;
        }
        *public_key = public_key.add(contribution);
      } else {
        for i in 1u16 ..= 4u16 {
          let mut eval = iss.commitments[0].commitment.mul(&(&iss.delta * &iss.delta));
          #[allow(non_snake_case)]
          for (C_i, C) in iss.commitments[1 ..].iter().enumerate() {
            let C_i = C_i + 1;
            let i = BigUint::from(i);
            eval = eval.add(&C.commitment.mul(&i.pow(u32::try_from(C_i).unwrap())));
          }
          verification_shares.insert(i, eval);
        }
        public_key = Some(contribution.clone());
      }
      for (i, share) in iss.shares {
        *shares.get_mut(&i).unwrap() += share;
      }
    }
    let delta = delta.unwrap();
    let public_key = public_key.unwrap();

    // TODO: Replace with a proven, decentralized flow
    let ec_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let k_ciphertext =
      cg.encrypt(&mut OsRng, &public_key, &BigUint::from_bytes_be(ec_key.to_repr().as_ref())).1;
    let ec_key = <Secp256k1 as Ciphersuite>::generator() * ec_key;
    dbg!("Shimmed key gen");

    let mut segment_time = std::time::Instant::now();

    // Round 1: Publish additive shares of the nonce
    let mut x_is = vec![];
    #[allow(non_snake_case)]
    let mut X_is = vec![];
    let mut x_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      let mut num_bytes = [0; 32];
      let x_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(x_i.to_repr().as_ref());
      x_is.push(x_i);

      X_is.push(<Secp256k1 as Ciphersuite>::generator() * x_i);

      let r = ZkEncryptionProof::<Secp256k1>::sample_randomness(&mut OsRng, &cg);
      // TODO: We need three of these for a 120-bit security level
      // *with a shared commit phase so they can't be individually re-rolled*
      let (ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key,
        &r,
        &x_i,
      );
      println!(
        "Proved for X_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
      proof
        .verify(&cg, &mut transcript(), &public_key, &ciphertext, *X_is.last().unwrap())
        .unwrap();
      println!(
        "Verified X_i: {}",
        std::time::Instant::now().duration_since(segment_time).as_millis()
      );
      segment_time = std::time::Instant::now();
      x_i_ciphertexts.push(ciphertext);
    }
    #[allow(non_snake_case)]
    let X = X_is.into_iter().sum::<<Secp256k1 as Ciphersuite>::G>();
    let r = <Secp256k1 as Ciphersuite>::F::from_repr(X.to_affine().x()).unwrap();

    // Everyone now calculates the sum nonce
    let mut x_ciphertext = x_i_ciphertexts.pop().unwrap();
    for x_i_ciphertext in &x_i_ciphertexts {
      x_ciphertext = x_ciphertext.add_without_randomness(x_i_ciphertext);
    }

    println!(
      "Calculated X: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Round 2: Perform multiplication of the sum nonce by our shares of y
    let mut y_is = vec![];
    let mut xy_i_ciphertexts = vec![];
    let mut ky_i_ciphertexts = vec![];
    for _ in 0 .. 3 {
      // Decide y
      let mut num_bytes = [0; 32];
      let y_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      num_bytes.copy_from_slice(y_i.to_repr().as_ref());
      y_is.push(y_i);

      let scalar = BigUint::from_bytes_be(&num_bytes);

      let y_randomness = ZkEncryptionProof::<Secp256k1>::sample_randomness(&mut OsRng, &cg);
      // TODO: We need three of these for a 120-bit security level
      // *with a shared commit phase so they can't be individually re-rolled*
      let (y_ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key,
        &y_randomness,
        &y_i,
      );
      proof
        .verify(&cg, &mut transcript(), &public_key, &y_ciphertext, Secp256k1::generator() * y_i)
        .unwrap();

      // Create xy_i_ciphertext and ky_i_ciphertext
      let (xy_randomness, xy_i_ciphertext) =
        cg.mul(&mut OsRng, &public_key, &x_ciphertext, &scalar);
      let (ky_randomness, ky_i_ciphertext) =
        cg.mul(&mut OsRng, &public_key, &k_ciphertext, &scalar);

      // For 2022-1437 5.2, a scaled ciphertext proof can be created with:
      // m=2, ws [a, y]
      // i=2, Ys [(a + by)G, (a + by)K + xyF]
      //      Xs [[G, bG], [K, bK + xF]]
      //
      // For an additionally proven Y_i with ciphertext aG, aK + yF, we need to add 2 is:
      // +Ys [aG, aK + yF]
      // +Xs [[G, Identity], [K, F]]
      //
      // And then finally, since we need to prove both xy and ky, we add:
      // +m for randomness c, padding prior Xs with Identity
      // +Ys [ky_i_ciphertext.0, ky_i_ciphertext.1]
      // +Xs [[Identity, k_ciphertext.0, G], [Identity, k_ciphertext.1, K]]
      //
      // Re-organized, and with distinct randomness for the y_i ciphertext and further usage, we
      // create a m=4, i=6 we organize as follows:
      // a = y randomness
      // b = xy randomness
      // c = ky randomness
      // ws = [a, b, c, y]
      // Ys = [..y_ciphertext, ..xy_ciphertext, ..ky_ciphertext]
      // Xs = [
      //   [G,        Identity, Identity, Identity],
      //   [K,        Identity, Identity, F],
      //   [Identity, G,        Identity, x_ciphertext.0],
      //   [Identity, K,        Identity, x_ciphertext.1],
      //   [Identity, Identity, G,        k_ciphertext.0],
      //   [Identity, Identity, K,        k_ciphertext.1],
      // ]
      #[rustfmt::skip]
      let proof = ZkRelationProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        [
          [cg.g(),        cg.identity(), cg.identity(), cg.identity()],
          [&public_key,   cg.identity(), cg.identity(), cg.f()],
          [cg.identity(), cg.g(),        cg.identity(), &x_ciphertext.0],
          [cg.identity(), &public_key,   cg.identity(), &x_ciphertext.1],
          [cg.identity(), cg.identity(), cg.g(),        &k_ciphertext.0],
          [cg.identity(), cg.identity(), &public_key,   &k_ciphertext.1],
        ],
        [&y_randomness, &xy_randomness, &ky_randomness, &scalar],
      );
      #[rustfmt::skip]
      proof
        .verify(
          &cg,
          &mut transcript(),
          // Assumes the ZkEncryptionProof randomness bound is <= this
          &cg.secret_bound(),
          [
            [cg.g(),        cg.identity(), cg.identity(), cg.identity()],
            [&public_key,   cg.identity(), cg.identity(), cg.f()],
            [cg.identity(), cg.g(),        cg.identity(), &x_ciphertext.0],
            [cg.identity(), &public_key,   cg.identity(), &x_ciphertext.1],
            [cg.identity(), cg.identity(), cg.g(),        &k_ciphertext.0],
            [cg.identity(), cg.identity(), &public_key,   &k_ciphertext.1],
          ],
          [
            &y_ciphertext.0,    &y_ciphertext.1,
            &xy_i_ciphertext.0, &xy_i_ciphertext.1,
            &ky_i_ciphertext.0, &ky_i_ciphertext.1,
          ],
        )
        .unwrap();

      xy_i_ciphertexts.push(xy_i_ciphertext);
      ky_i_ciphertexts.push(ky_i_ciphertext);
    }

    println!(
      "xy and ky multiplications: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Also, for signers i != 1, publish the subtractive shares of d_i and signature shares
    let mut d_is = vec![];
    #[allow(non_snake_case)]
    let mut D_is = vec![];
    let mut d_i_ciphertexts = vec![];
    for _ in 1 .. 3 {
      let mut num_bytes = [0; 32];
      let d_i = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
      #[allow(non_snake_case)]
      let D_i = <Secp256k1 as Ciphersuite>::generator() * d_i;
      num_bytes.copy_from_slice((-d_i).to_repr().as_ref());
      d_is.push(d_i);
      D_is.push(D_i);
      let randomness = ZkEncryptionProof::<Secp256k1>::sample_randomness(&mut OsRng, &cg);
      // TODO: We need three of these for a 120-bit security level
      // *with a shared commit phase so they can't be individually re-rolled*
      let (ciphertext, proof) = ZkEncryptionProof::<Secp256k1>::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        &public_key,
        &randomness,
        &-d_i,
      );
      proof
        .verify(&cg, &mut transcript(), &public_key, &ciphertext, -D_is.last().unwrap())
        .unwrap();
      d_i_ciphertexts.push(ciphertext);
    }

    println!(
      "d_i subtractive shares: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Everyone now calculates xy and the sum of the posted subtractive shares
    let mut z_ciphertext = xy_i_ciphertexts.pop().unwrap();
    for xy_ciphertext in &xy_i_ciphertexts {
      z_ciphertext = z_ciphertext.add_without_randomness(xy_ciphertext);
    }

    let mut d_ciphertext = ky_i_ciphertexts.pop().unwrap();
    for ky_ciphertext in &ky_i_ciphertexts {
      d_ciphertext = d_ciphertext.add_without_randomness(ky_ciphertext);
    }
    for d_i_ciphertext in &d_i_ciphertexts {
      d_ciphertext = d_ciphertext.add_without_randomness(d_i_ciphertext);
    }

    println!(
      "z and d sums: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Round 3: For signers i != 1, publish the decryption share for the remaining ciphertexts, and
    // their signature shares
    let set = [1, 2, 3];
    #[allow(non_snake_case)]
    let mut W_i_zs = vec![];
    #[allow(non_snake_case)]
    let mut W_i_ds = vec![];
    let m1_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
    let mut w = <Secp256k1 as Ciphersuite>::F::ZERO;
    for i in 2u16 ..= 3 {
      #[allow(non_snake_case)]
      let W_i_z = z_ciphertext.0.mul(&(&shares[&i] * &delta));
      #[allow(non_snake_case)]
      let W_i_d = d_ciphertext.0.mul(&(&shares[&i] * &delta));

      let share_max_size =
        BigUint::one() << (IntegerSecretSharing::share_size(&cg, 3, 4) + delta.bits());
      // TODO: Merge these ZkDlogEqualityProofs
      let proof = ZkDlogEqualityProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        cg.g(),
        &z_ciphertext.0,
        &(&shares[&i] * &delta),
      );
      proof
        .verify(
          &cg,
          &mut transcript(),
          &share_max_size,
          cg.g(),
          &z_ciphertext.0,
          verification_shares[&i].clone(),
          W_i_z.clone(),
        )
        .unwrap();
      let proof = ZkDlogEqualityProof::prove(
        &mut OsRng,
        &cg,
        &mut transcript(),
        cg.g(),
        &d_ciphertext.0,
        &(&shares[&i] * &delta),
      );
      proof
        .verify(
          &cg,
          &mut transcript(),
          &share_max_size,
          cg.g(),
          &d_ciphertext.0,
          verification_shares[&i].clone(),
          W_i_d.clone(),
        )
        .unwrap();

      // Technically, the lagrange coefficient can be applied after collecting shares
      // The provided lagrange function inlines the delta multiplication so it can return a single
      // value, so to post-include the lagrange would be to include delta twice (as delta must be
      // included here)
      // While we could rewrite the lagrange function to return a (numerator, denominator), we
      // don't need post-determinism of the lagrange coefficient
      let lagrange = IntegerSecretSharing::lagrange(4, i, &set);
      #[allow(non_snake_case)]
      let W_i_z = if lagrange < BigInt::zero() {
        W_i_z.neg().mul(&(-lagrange.clone()).to_biguint().unwrap())
      } else {
        W_i_z.mul(&lagrange.clone().to_biguint().unwrap())
      };
      W_i_zs.push(W_i_z);

      #[allow(non_snake_case)]
      let W_i_d = if lagrange < BigInt::zero() {
        W_i_d.neg().mul(&(-lagrange).to_biguint().unwrap())
      } else {
        W_i_d.mul(&lagrange.to_biguint().unwrap())
      };
      W_i_ds.push(W_i_d);

      // Technically, a post-round on invalid share could be used for identification
      // Pros: Doesn't require a more expensive proof in the optimistic path
      // Cons: A validator can send an invalid message, then go offline when expected to provide a
      // further proof which would prove their fault, which would be unattributable
      // - 1 to 0-index, - 1 for d_is as signer 0 isn't present in d_is
      w += (m1_hash * y_is[usize::from(i - 1)]) + (r * d_is[usize::from(i - 1) - 1]);
      // TODO: Demo share verification
    }

    // For signer 1, calculate and keep the final decryption share to be the sole decryptor of what
    // remains of z and d
    // Signer 1 will be the only party to end up with the signature and is expected to publish it
    #[allow(non_snake_case)]
    let mut W_z = z_ciphertext.0.mul(
      &(&shares[&1] * &delta * IntegerSecretSharing::lagrange(4, 1, &set).to_biguint().unwrap()),
    );
    #[allow(non_snake_case)]
    for W_i_z in W_i_zs {
      W_z = W_z.add(&W_i_z);
    }
    #[allow(non_snake_case)]
    let mut W_d = d_ciphertext.0.mul(
      &(&shares[&1] * &delta * IntegerSecretSharing::lagrange(4, 1, &set).to_biguint().unwrap()),
    );
    #[allow(non_snake_case)]
    for W_i_d in W_i_ds {
      W_d = W_d.add(&W_i_d);
    }

    println!(
      "i != 1 decryption shares: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    segment_time = std::time::Instant::now();

    // Recover the messages
    let z = {
      #[allow(non_snake_case)]
      let M = z_ciphertext.1.mul(&(&delta * &delta * &delta)).add(&W_z.neg());
      let value_scaled_by = (&delta * &delta * &delta) % cg.p();
      // Invert value_scaled_by over p
      let inverse = value_scaled_by.modpow(&(cg.p() - 2u8), cg.p());
      assert!((&inverse * &value_scaled_by).mod_floor(cg.p()).is_one());
      (cg.solve(M).unwrap() * inverse) % cg.p()
    };

    let d_i_1 = {
      #[allow(non_snake_case)]
      let M = d_ciphertext.1.mul(&(&delta * &delta * &delta)).add(&W_d.neg());
      let value_scaled_by = (&delta * &delta * &delta) % cg.p();
      // Invert value_scaled_by over p
      let inverse = value_scaled_by.modpow(&(cg.p() - 2u8), cg.p());
      assert!((&inverse * &value_scaled_by).mod_floor(cg.p()).is_one());
      (cg.solve(M).unwrap() * inverse) % cg.p()
    };
    d_is.insert(0, {
      let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
      let bytes_ref: &mut [u8] = bytes.as_mut();
      bytes_ref.copy_from_slice(&d_i_1.to_bytes_be());
      <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
    });

    println!(
      "z and d_i decryption: {}",
      std::time::Instant::now().duration_since(segment_time).as_millis()
    );
    // segment_time = std::time::Instant::now();

    // Add the share for signer 1
    // Create and publish the signature
    w += (m1_hash * y_is[0]) + (r * d_is[0]);
    let s = w *
      ({
        let mut bytes = <<Secp256k1 as Ciphersuite>::F as PrimeField>::Repr::default();
        let bytes_ref: &mut [u8] = bytes.as_mut();
        bytes_ref.copy_from_slice(&z.to_bytes_be());
        <Secp256k1 as Ciphersuite>::F::from_repr(bytes).unwrap()
      })
      .invert()
      .unwrap();

    verify(ec_key, m1_hash, r, s);
  }
}
