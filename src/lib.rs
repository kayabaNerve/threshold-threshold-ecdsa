#[cfg(test)]
mod tests {
    use ciphersuite::{
        group::{
            ff::{Field, PrimeField},
            Group,
        },
        Ciphersuite, Secp256k1,
    };
    use elliptic_curve::point::AffineCoordinates;
    use rand_core::OsRng;

    fn verify(
        public_key: <Secp256k1 as Ciphersuite>::G,
        message_hash: <Secp256k1 as Ciphersuite>::F,
        r: <Secp256k1 as Ciphersuite>::F,
        s: <Secp256k1 as Ciphersuite>::F,
    ) {
        assert_ne!(r, <Secp256k1 as Ciphersuite>::F::ZERO);
        assert_ne!(s, <Secp256k1 as Ciphersuite>::F::ZERO);

        let z = message_hash;
        let u1 = z * s.invert().unwrap();
        let u2 = r * s.invert().unwrap();
        let point = (Secp256k1::generator() * u1) + (public_key * u2);
        assert!(!bool::from(point.is_identity()));
        assert_eq!(r.to_repr(), point.to_affine().x());

        ecdsa::hazmat::verify_prehashed(
            &public_key,
            &message_hash.to_repr(),
            &ecdsa::Signature::<k256::Secp256k1>::from_scalars(r, s).unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn non_distributed() {
        let private_key = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);

        let x = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
        let y = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
        let z = x * y;
        let d = private_key * y;

        let r =
            <Secp256k1 as Ciphersuite>::F::from_repr((Secp256k1::generator() * x).to_affine().x())
                .unwrap();

        let message_hash = <Secp256k1 as Ciphersuite>::F::random(&mut OsRng);
        let w = (message_hash * y) + (r * d);
        let s = w * z.invert().unwrap();

        verify(Secp256k1::generator() * private_key, message_hash, r, s);
    }
}
