# 2-round Robust Threshold Schnorr with Linear Signing Complexity

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

## Proofs

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

Decryption of a ciphertext is performed by acquiring `t` decryption shares
(each `k_i * rG`) and interpolating them, using the result in place of `krG`
within the standard decryption process.

### Elliptic Curve Key

All participants randomly sample `r, x`. `P_i = xE, R_i = rG, M_i = rK + xH`.

The key the group signs for is `P = sum(P_i)`. The ciphertext for `P`'s discrete
logarithm is `P_ciphertext = (sum(R_i), sum(M_i))`.

## Signing

Signing is described as a 2-round protocol, with round 1 potentially
preprocessable, with one of the following requirements:

1) No preprocessing of round 1. Nonces are only used for a specific message.
2) All signing sessions are part of the public state and the local state can
   synchronize the public state.
3) `t` is set to `2(n / 3) + 1` with `(n / 3) + 1` being able to cause nonce
   reuse and produce unintended signatures after recovering the private key.

It proceeds as follows.

1) A set of size equal to `t` perform the following steps.

    1) Sample `r_a, a, r_b, b`.
    2) `A_i = aE, R_a_i = r_a G, M_a_i = r_a K + aH`.
    3) `B_i = bE, R_b_i = r_b G, M_b_i = r_b K + bH`.
    4) Publish `A_i, B_i, (R_a_i, M_a_i), (R_b_i, M_b_i)` and the two `ECC-CT`
       proofs needed to prove knowledge, validity, and consistency.

2) With the published values from round one and the message, the following
   steps can be performed.

    1) Verify the prior proofs.

    2) Calculate the binding factor `l` by hashing:
       - The group key
       - The message
       - Every contribution to the nonce, both the ECC points and ciphertexts
         *with who contributed it*

    3) `A = sum(A_i), R_a = sum(R_a_i), M_a = sum(M_a_i)`.
    4) `B = sum(B_i), R_b = sum(R_b_i), M_b = sum(M_b_i)`.
    5) `c = H(A + lB, P, message)`.
    6) `S = (R_a, M_a) + (l R_b, l M_b) + (c P_ciphertext)`.

    7) Publish `k_i S.0`, the decryption share for `S`, with a proof
       `DLEQ(k_i, G, S.0, K_i, decryption_share)` proving its well-formedness.

3) Once `t` parties have published decryption shares, they can be interpolated
   for anyone to perform decryption of `S`. The resulting value, `s`, forms a
   Schnorr signature of `(A + lB, s)`. If the signature is invalid, the `DLEQ`
   proofs are verified to identify the faulty party.

## Practical Comments on Security

This section attempts to comment on the security of the composition provided
*in an informal, practical manner*.

This protocol fundamentally relies on [CL15](https://eprint.iacr.org/2015/047)
standing. Additionally, it requires the proofs used be valid.

So far, I've most preferred the "Adaptive Root Assumption" over the
"Strong Root Assumption" or "Rough Order Assumption". The
"Rough Order Assumption" assumes statistical properties of unknown orders and no
proofs relying it serve as proofs of knowledge. The "Strong Root Assumption"
relies on more than the "Adaptive Root Assumption" while simultaneously having
less efficient proofs (due to requiring repetition).

- The security of the ECC nonces.

The ECC nonce creation lines up with [FROST](https://eprint.iacr.org/2020/852).

- The nonce ciphertexts can be decrypted to perform a key recovery.

Only by a malicious threshold.

- Concurrent security.

The signature itself is assumed to have concurrent security as FROST does. There
is a potential concern the ciphertext decryption process doesn't achieve
concurrent security (despite the paper it's from being proven under the UC
model).

Please note the only decrypted ciphertext is the sum of `t` participants
ciphertexts. Accordingly, randomness from every single participant is
incorporated. Another participant cannot choose their randomness to cancel out
someone else's due to the proof of knowledge bound.

While the randomness is presumably able to be biased, it has the same binding
factor process FROST itself had.  The question becomes can the outputs of two
biased DKGs, one weighted by a binding factor, summed, cause problems. The
presumption is not. If it can, a new nonce process would be needed.

In order to avoid bias in the decryption, the following may be possible.

1) Hash the binding factor to an element `B`.
2) Set `decryption_share` to `(S.0 + B) * private_key_share`,
   `B_share` to `B * private_key_share * H(binding_factor)`.
3) Modify `S.1` to `(S.1 * H(binding_factor)) + sum(B_share)`.
4) Perform decryption via solving for `S.1 - sum(decryption_share)`, then
   multiplying the result via the inverse of `H(binding_factor)` modulo `p`.

`decryption_share` cannot be converted to the decryption share for the original
`S` as it'd require subtracting `B * private_key_share`, an unknown value. While
it can be calculated by `B_share * H(binding_factor).invert()`, the inverse is
presumed infeasible to calculate due to the group being of unknown order (and
may require the hash function be a hash to prime). Then the sole question is if
the inclusion of uniform points do successfully erase bias.

This commentary on bias is likely overengineered, yet besides the security of
the class group construction itself, is my biggest concern. Accordingly, I'd
like to be thorough.

- A nonce could be reused.

One of the requirements for the signing protocol prevents this.

If there is no preprocessing, nonces will only be used for a single message.

If the public state throughout history is viewable, any participant can note
when a preprocess was used and not further use it.

If preprocessing is used with `t >= 2(n / 3) + 1`, then up to `n / 3` may not be
aware a preprocess was used. For them to decrypt a signature reusing a nonce,
they'd need a further `(n / 3) + 1` participants. Accordingly, while the protocol's
`t` may be set to `2(n / 3) + 1`, it'd actually be the much weaker
`(n / 3) + 1`. This is here documented, and there is no other way to perform a
decryption (enabling accessing the value incurring nonce reuse).

- The decryption share could have its discrete log recovered.

https://eprint.iacr.org/2022/1437 is the proven protocol from which the
threshold decryption process is from.

## Future Work

Obviously, the above composition needs its security formalized and proven. It is
in no way claimed to be currently secure.

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
