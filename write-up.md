# 67-of-100 Threshold ECDSA in <3s

Implemented at https://github.com/kayabaNerve/threshold-threshold-ecdsa.

## Background

The protocol relies on [CL15](ttps://eprint.iacr.org/2015/047)'s homormorphic
encryption scheme constructed via class groups of unknown order. In a brief
summary, class groups of unknown order can be created with a subgroup where the
discrete log problem is easy (hereafter solely referred to as the subgroup).

This leads to ElGamal-esque ciphertexts of the form `rG, rK + mH`, where:

- `r` is the ciphertext randomness
- `G` is a generator of the class order
- `K` is the public key
- `m` is the message
- `H` is the generator for the subgroup

Decryption is via multiplying `rG` by the private key, subtracting the result
from the second element, and solving for the discrete logarithm.

The two notable attributes about this scheme are:

1) The message space is configurable to any prime number.

   This removes the need for any range proofs over the message, if properly
   configured to a curve's scalar field (and used for scalars).

2) The class group, and keys for it, can be constructed feasibly and
   trustlessly.

   The class group construction can be done in a linear fashion with a constant
   amount of time. Keys can be created using a secret sharing scheme. Neither
   require secret primes and neither have an error rate (where the protocol may
   fail even with honest participants).

### Proofs

Three ZK proofs are needed.

1) `DLOG(x, G, A)`
    - `x`: An integer
    - `G`: A generator of the class group
    - `A`: An element

    Prove knowledge of `x` and for the relation `A = xG`.

2) `ECC-CT(r, x, E, G, H, K, P, R, M)`
    - `r`: An integer
    - `x`: A scalar for the order of the subgroup
    - `E`: A generator of an elliptic curve whose order is equivalent to the
           order of the subgroup
    - `G`: A generator of the class group
    - `H`: The generator of the subgroup
    - `K`: An element of the class group
    - `P`: A point on the elliptic curve
    - `R, M`: Elements of the class group

    Prove knowledge of `r`, `x` and for the relations
    `P = xE, R = rG, M = rK + xH`.

    This proves that the ciphertext is a valid encryption of the point's
    discrete logarithm to the specified public key.

3) `RELATIONS(G, s, O)`
    - `G`: A matrix of elements of size `m * n`.
    - `s`: A row of integers of length `n`.
    - `O`: A column of elements of length `m`.

    Prove knowledge of `s` and for the relations
    `O_i = sum(G[i] * s) for i in 0 .. m`.

The first proof immediately resolves to the third with a matrix of `[[G]]`. The
second proof is likely a trivial extension over the third proof. If preferable,
more specific proofs (with better performance or better assumptions) may be used
however.

https://eprint.iacr.org/2021/205 provides candidates for `DLOG` and `ECC-CT`.
Their provided proofs seem to be already-specified instantiations of a
`RELATIONS` proof they didn't include. With `RELATIONS` being reconstituted,
all proofs are satisfied. The only assumption introduced is their
"Adaptive Root Assumption", which they compare to the "RSA Assumption".

https://eprint.iacr.org/2022/1437 provides a candidate for `RELATIONS`. Their
proof doesn't offer a proof of knowledge and relies on the
"Rough Order Assumption", which isn't preferred.

## Setup

### Class Group

The class group requires construction. The
[original 2015 paper](https://eprint.iacr.org/2015/047) does describe generation
with solely public parameters.

[Bandwidth-threshold threshold EC-DSA](https://eprint.iacr.org/2020/084)
proposed a distinct mechanism, explicitly in a MPC context, which provides a
uniformly distributed generator (as needed for the "Strong Root Assumption").

While the latter's MPC-aware construction is preferred,
https://eprint.iacr.org/2024/034 non-interactively offers uniformly distributed
generators and should be used for generators as needed.

threshold-threshold-ecdsa currently solely has the original class group
construction from the 2015 paper.

### Threshold Encryption Key

Participants run the integer secret sharing system from
https://eprint.iacr.org/2022/1437. The most expensive part of this is the `t`
`DLOG` proofs. Ideally, a two-round protocol which only uses a single proof for
either the first commitment (as per PedPoP) or a single proof for all
commitments (MuSig-aggregated) is instead used.

This yields a threshold encryption key `K` with each participant having a
interpolatable share `k_i` and verification share `K_i`.

Decryption of a ciphertext is performed by acquiring `t` decryption shares
(each `k_i * rG`) and interpolating them, using the result in place of `krG`
within the standard decryption process.

### Elliptic Curve Key

All participants randomly sample `r, x`. `P_i = xE, R_i = rG, M_i = rK + xH`.

The key the group signs for is `P = sum(P_i)`. The ciphertext for `P`'s discrete
logarithm is `P_ciphertext = (sum(R_i), sum(M_i))`.

## Signing

Signing is described as a robust 3-round protocol with identifiable aborts.
Preprocessing of the first two rounds, or pipelining of the first round, may be
feasible (with caveats) yet this isn't discussed here at this time.

1) A set of size at least equal to `t` perform the following steps.

    1) Sample `r_x, x`.
    2) `X_i = xE, R_x_i = r_x G, M_x_i = r_x K + xH`.
    3) Publish `X_i, (R_x_i, M_x_i)` and the `ECC-CT` proof needed to prove
       knowledge, validity, and consistency.

    This creates the nonce which will be used in the ECDSA signature.

2) A set of size at least equal to `t` perform the following steps once the
   prior round is honestly completed (honesty determined by the proof(s)
   successfully verifying).

    1) `X = sum(X), X_ciphertext = (sum(R_x_i), sum(M_x_i))`.
    2) Sample `r_y, y, r_yx, r_yp`.
    3) `Y_i_ciphertext = (r_y G, r_y K + yH)`.
    4) `yX_i_ciphertext = (y X_ciphertext.0 + r_yx G, y X_ciphertext.1 + r_yx K)`
    5) `yP_i_ciphertext = (y P_ciphertext.0 + r_yp G, y P_ciphertext.1 + r_yp K)`
    6) Publish `Y_i_ciphertext, yX_i_ciphertext, yP_i_ciphertext`, and a
       `RELATIONS` proof for all the ciphertexts, proving their validity and
       consistency (where all sampled secrets are the row of secrets).

    This creates the `y` variable, applied to both the numerator and denominator
    (to cancel out), which blinds the nonce.

3) A set of size at least equal to `t` perform the following steps once the
   prior round is honestly completed (honesty determined by the proof(s)
   successfully verifying).

    1) `Y = sum(Y_i_ciphertext), Z = sum(yX_i_ciphertext), D = sum(yP_i_ciphertext)`.
    2) `r = X.coordinates().x % p`, where `p` is the order of the scalar field.
    3) `mY = message * Y, rD = r * D, W = mY + rD`.

       `W` now holds the numerator of the ECDSA signing equation, multiplied by
       `y`.

       `Z` holds the denominator, also multiplied by `y`.

    4) Publish `k_i Z.0`, `k_i W.0`, the decryption shares for `Z` and `W`,
       with a pair of proofs proving their well-formedness. Specifically,
       `DLEQ(k_i, G, Z.0, K_i, Z_decryption_share)` and
       `DLEQ(k_i, G, W.0, K_i, W_decryption_share)`.

4) Once `t` parties have published valid decryption shares (as determined by the
   proofs verifying successfully), they can be interpolated for anyone to
   perform decryption of `Z` and `W`. The resulting values, `z` and `w`, form a
   valid ECDSA signature of `(r, w / z)`.

threshold-threshold-ecdsa implements the above signing protocol (with an
additional commitment, sacrificing robustness for a notion of additional
security) and achieves 67-of-100 signing in less than 3s per party
(2GHz 12th Gen Intel, single thread).

## Future Work

Obviously, the above composition needs its security formalized and proven. It is
in no way claimed to be currently secure.

I would not be surprised if it ends up needing a commitment, sacrificing
robustness, or if it needs a binomial nonce like FROST. It does have the
advantage of never transmitting/revealing any scalars, solely points/elements,
until the final signature is revealed. Ideally, that ensures all of this is ZK
and helps ensure unforgeability of signatures.

The library itself needs to be moved from being a proof of concept to a proper
production library. With this needs to be compensation for the fact it's
variable time (sufficient masking and/or moving proving to constant time) and
auditing. The currently implemented `RELATIONS` proof must also be corrected
(it relies on the "Rough Order Assumption").

Using the [techniques from BICYCL](https://eprint.iacr.org/2022/1466), and by
moving to GMP, it should be possible to reduce the amount of work by ~4x, at
least. Further work can be done not only on parallelism, yet subcommittees such
that any individual signer only performs a logarithmic amount of computation to
the amount of signers.

If you are interested in this, please feel free to reach out to @kayabaNerve on
Twitter and Discord, or @kayabanerve:matrix.org on Matrix.
