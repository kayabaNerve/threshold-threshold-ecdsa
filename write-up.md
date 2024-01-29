# 2-round Threshold ECDSA

Implemented at
https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/two-round.

## Background

The protocol relies on [CL15](https://eprint.iacr.org/2015/047)'s homormorphic
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

2) `DLEQ(x, F, G, A, B)`
    - `x`: An integer
    - `F`, `G`: Elements of the class group without a known relation to the
                prover
    - `A`, `B`: Elements of the class group

    Prove knowledge of `x` and for the relations `A = xF, B = xG`

3) `ECC-CT(r, x, E, G, H, K, P, R, M)`
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

We additionally discuss a proof `RELATIONS` which proves for a matrix of
elements and a row of secrets, an output column of elements is the result of a
multiexp of each row of elements by the row of secrets. Such a proof naturally
offers `DLOG` (matrix `[[G]]`, secrets `[x]`) and
`DLEQ` (matrix `[[F], [G]]`, secrets `[x]`).

A proof of ciphertext validity (`CT`) would be matrix `[[G, Identity], [K, H]]`
with row of secrets `[r, x]` (producing ciphertext `[rG, rK + xH]`). `ECC-CT` is
presumed to be a trivial extension from there.

https://eprint.iacr.org/2021/205 provides candidates for `DLOG` and `ECC-CT`,
yet not `DLEQ`. Their provided proofs seem to be already-specified
instantiations of a `RELATIONS` proof they didn't include. With `RELATIONS`
being reconstituted and used to derive `DLEQ`, all proofs are satisfied. The
only assumption introduced is their "Adaptive Root Assumption", which they
compare to the "RSA Assumption".

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

### Elliptic Curve Key

Set `A = hash_to_point(K.serialize() || "A")`.

Set `B = hash_to_point(K.serialize() || "B")`.

All participants randomly sample `x`.
`P_i = xE, M_i = k_i.interpolate() A + xH`.

The key the group signs for is `P = sum(P_i)`. The 'ciphertext' for `P`'s
discrete logarithm is `P_ciphertext = sum(M_i)` (despite not being a CL15
ciphertext).

## Signing

This protocol was derived from the 3-round protocol posited
[here](https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/develop/write-up.md).

It was observed the above protocol could have the latter two rounds combined
(decryption and multiplication by `y`) using a new technique,
"threshold scaled decryption". This refers to threshold decryption not of a
value, yet of a value scaled by another value.

Instead of decrypting `xy` and decrypting `my + ryp`, we decrypt `x` scaled by
`y` and `m + rp` scaled by `y` (without revealing `x` or `m + rp`).

Threshold scaled decryption works by:
1) Have a ciphertext `rGmH` (summed from `r_i G m_i H`) and scalar commitment
   `s_i G`.
2) Sum `s_i G` to `S`.
3) Publish `s_i ciphertext` and `r_i S`.
4) Decrypt with `sum(r_i S).`

Signing is described as a 2-round protocol with identifiable aborts.
Preprocessing of the first round may be feasible yet this isn't discussed here
at this time.

1) A set of size at least equal to `t` perform the following steps.

    1) Sample `r_x_i, x_i`.
    2) `X_i = xE, X_i_ciphertext = (r_x_i G, r_x_i B + x_i H)`.
    3) Publish `X_i, X_i_ciphertext` and the `ECC-CT` proof needed to prove
       knowledge, validity, and consistency.

       This forms the nonce for the ECDSA signature.

    4) Sample `y_i`.
    5) `y_A_i = y_i A, y_B_i = y_i B`.
    6) Publish `y_A_i, y_B_i` with a `DLEQ` proof.

2) The same set performs the following steps if all prior proofs verify.

    1) `X = sum(X), X_ciphertext = sum(X_i_ciphertext.1)`.
    2) `r = X.coordinates().x % p`, where `p` is the order of the scalar field.

    3) Set `y_A = sum(y_A_i), y_B = sum(y_B_i)`.

    4) `N_i = y_i (r P_ciphertext + message H)`.

       This is a ciphertext for `m + rd`, where `d` is the private key, which is
       the numerator of the ECDSA signing equation, further multiplied by a
       share of `y`. This causes the sum, `N`, to be the signing equation's
       numerator multiplied by `y`.

    5) Set `R_N_i = k_i.interpolate() r y_A`.

       This, once summed to `R_N`, will be the `A` component of `N`.

    6) `D_i = y_i X_ciphertext`.

       `X_ciphertext` is a ciphertext of the nonce, which is the denominator of
       the ECDSA signing equation. In order to blind it when it's decrypted,
       it's multiplied by `y`.

       This will cancel out when applied to our numerator, also multiplied by
       `y`.

    7) Set `R_D_i = r_x_i y_B`.

       This, once summed to `R_D`, will be the `B` component of `D`.

    8) Publish `N_i, R_N_i, D_i, R_D_i` with `DLEQ` proofs:
        - `DLEQ(y_i, A, r P_ciphertext + message H, y_A_i, N_i)`
        - `DLEQ(k_i.interpolate(), G, r y_A, verification_share.interpolate(), R_N_i)`
        - `DLEQ(y_i, A, X_ciphertext, y_A_i, D_i)`
        - `DLEQ(r_x_i, G, y_B, X_i_ciphertext.0, R_D_i)`

3) If all prior proofs verify, any party may decrypt and calculate the
   signature.

    1) `N = sum(N_i), R_N = sum(R_N_i)`.
    3) Set `n` to the discrete log of `N - R_N`.
    4) `D = sum(D_i), R_D = sum(R_D_i)`.
    5) Set `d` to the discrete log of `D - R_D`.

The valid ECDSA signature is `(r, n / d)`.

Instead of verifying the round two proofs, the resulting ECDSA signature may be
verified. If valid, the proofs may be assumed true. If invalid, the proofs may
be verified to identify the faulty party.

This limits the proofs verified in the success path to solely the `ECC-CT` and
`DLEQ` proofs from round one.

## Future Work

Obviously, the above composition needs its security formalized and proven. It is
in no way claimed to be currently secure.

I would not be surprised if it ends up needing a commitment, or if it needs a
binomial nonce like FROST. It does have the advantage of never
transmitting/revealing any scalars, solely points/elements, until the final
signature is revealed. Ideally, that ensures all of this is ZK and helps ensure
unforgeability of signatures.

The library itself needs to be moved from being a proof of concept to a proper
production library. With this needs to be compensation for the fact it's
variable time (sufficient masking and/or moving proving to constant time) and
auditing. The currently implemented `RELATIONS` proof (used for `DLEQ`) must
also be corrected (it relies on the "Rough Order Assumption").

Using the [techniques from BICYCL](https://eprint.iacr.org/2022/1466), and by
moving to GMP, it should be possible to reduce the amount of work by ~4x, at
least. Further work can be done not only on parallelism, yet subcommittees such
that any individual signer only performs a logarithmic amount of computation to
the amount of signers.

If you are interested in this, please feel free to reach out to @kayabaNerve on
Twitter and Discord, or @kayabanerve:matrix.org on Matrix.
