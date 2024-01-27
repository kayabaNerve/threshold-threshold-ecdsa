# 2-round Threshold ECDSA

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

### Elliptic Curve Key

Set `F = hash_to_point(K.serialize())`.

All participants randomly sample `x`. `P_i = xE, M_i = k_i F + xH`.

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

Threshold scaled decryption works by
1) Have a ciphertext `rGmH` (summed from `r_i G m_i H`) and scalar commitment
   `s_i G`.
2) Sum `s_i G` to `S`.
3) Publish `s_i ciphertext` and `r_i S`.
4) Decrypt with `sum(r_i S).`

Signing is described as a 2-round protocol with identifiable aborts.
Preprocessing of the first round may be feasible yet this isn't discussed here
at this time.

1) A set of size at least equal to `t` perform the following steps.

    1) Sample `r_x, x`.
    2) `X_i = xE, R_x_i = r_x G, M_x_i = r_x K + xH`.
    3) Publish `X_i, (R_x_i, M_x_i)` and the `ECC-CT` proof needed to prove
       knowledge, validity, and consistency.

    4) Sample `y_i`.
    5) `Y_i = y_i K, Y_f_i = y_i F`.
    6) Publish `Y_i, Y_f_i` with a `RELATIONS` proof proving for the shared
       discrete logarithm.

2) The same set performs the following steps if all prior proofs verify.

    1) `X = sum(X), X_ciphertext = (sum(R_x_i), sum(M_x_i))`.
    2) `r = X.coordinates().x % p`, where `p` is the order of the scalar field.

    3) Set `Y = sum(Y_i), Y_f = sum(Y_f_i)`.

    4) `N_i = y_i (r P_ciphertext + message H)`.

       This is a ciphertext for `m + rd`, where `d` is the private key, which is
       a piece of the ECDSA signing equation (yet further multiplied by a share
       of `y`). This causes the sum, `N`, to be the signing equation multiplied
       by `y`.

       In the ECDSA signing equation, this would be divided by `x`, the nonce.
       We divide it by `x * y` to meet expectations and cancel out the `y` term.

    5) Set `R_N_i = k_i.interpolate() r Y_f`.

       This, when summed to `R_N`, will be the `G` component of `N`.

    6) `D_i = y_i X`.
    7) Set `R_D_i = r_x Y`.

    8) Publish `N_i, R_N_i, D_i, R_D_i` with a `RELATIONS` proof.

3) The same set performs the following steps if all prior proofs verify.

    1) `N = sum(N_i), R_N = sum(R_N_i)`.
    3) Set `n` to the discrete log of `N - R_N`.
    4) `D = sum(D_i), R_D = sum(R_D_i)`.
    5) Set `d` to the discrete log of `D - R_D`.

The valid ECDSA signature is `(r, n / d)`.

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
auditing. The currently implemented `RELATIONS` proof must also be corrected
(it relies on the "Rough Order Assumption").

Using the [techniques from BICYCL](https://eprint.iacr.org/2022/1466), and by
moving to GMP, it should be possible to reduce the amount of work by ~4x, at
least. Further work can be done not only on parallelism, yet subcommittees such
that any individual signer only performs a logarithmic amount of computation to
the amount of signers.

If you are interested in this, please feel free to reach out to @kayabaNerve on
Twitter and Discord, or @kayabanerve:matrix.org on Matrix.
