# 2-round Robust Threshold Schnorr with Linear Signing Complexity

## The Protocol

The protocol relies on class groups to offer a homormorphic encryption scheme.
Class groups are notable for having a trustless setup which is error-fee (not
requiring re-attempts, such as protocols which randomly generate numbers until
achieving sums which are prime).

### Proofs

Three ZK proofs, which additionally prove knowledge of the witness, are needed.

1) DLog (`DLOG`).
2) A proof an elliptic point's discrete log is encrypted as the message within a
   well-formed ciphertext (`ECC-CT`).
3) A general relations proof proving that for a matrix of elements and a row of
   secrets, an output row of elements is the result of a multiexp of each row
   row of elements by the row of secrets (`RELATIONS`).

The first proof immediately resolves to the third for a matrix of `[[G]]`. The
second proof is likely a trivial extension over the third proof. If preferable,
more specific proofs (with better performance or better assumptions) may be used
however.

https://eprint.iacr.org/2021/205 provides candidates for `DLOG` and `ECC-CT`,
yet not explicitly `RELATIONS`. Their other proofs seem to be already-specified
instantiations of a `RELATIONS` proof they didn't include. With `RELATIONS`
being reconstituted, the only assumption introduced is their "Root Assumption",
which they compare to the "RSA Assumption".

https://eprint.iacr.org/2022/1437 provides a candidate for `RELATIONS`. It
doesn't offer a proof of knowledge and relies on the "Rough Order Assumption",
which isn't preferred.

### DKG

The class group needs construction. The
[original 2015 paper](https://eprint.iacr.org/2015/047) on a homomorphic
encryption scheme over class groups does describe generation with solely public
parameters. In order to satisfy the strong root assumption,
[Bandwidth-threshold threshold EC-DSA](https://eprint.iacr.org/2020/084)
proposed a distinct mechanism (which is explicitly in a MPC context).

While the latter's MPC-aware construction is preferred,
https://eprint.iacr.org/2024/034 non-interactively offers uniformly distributed
generators and should be used for generators as needed.

threshold-threshold-ecdsa currently solely has the original class group
construction from the 2015 paper.

Participants additionally run the integer secret sharing system from
https://eprint.iacr.org/2022/1437. The most expensive part of this is the `t`
`DLOG` proofs. Ideally, a two-round protocol which only uses a single proof for
either the first commitment (as per PedPoP) or a single proof for all
commitments (MuSig-aggregated) is instead used.

Finally, a ciphertext (encrypted to the group's threshold key, as all
ciphertexts here are) for the private key is created. This can be done by
participants publishing `K_i`, an ECC point, with a ciphertext encrypting its
discrete log (`K_i_ciphertext`, with a `ECC-CT` proof). The group's key is
`sum(K_i)` with the `K_ciphertext` being the sum of the `K_i_ciphertext`s.

### Signing

Signing is described as a 2-round protocol, with round 1 potentially
preprocessable, with one of the following requirements:

1) No preprocessing of round 1. Nonces are only used for a specific message.
2) All signing sessions are part of the public state and the local state can
   synchronize the public state.
3) `t` is set to `2(n / 3) + 1` with `(n / 3) + 1` being able to cause nonce
   reuse and produce unintended signatures after recovering the private key.

This can be performed by a threshold of participants using lagrange
interpolation on their decryption shares, the literal inclusion of is ignored
here.

1) A set of size equal to `t` provide `D_i`, `E_i`, which are ECC points, and
   ciphertexts for their discrete logs with the relevant proofs (`ECC-CT`).

2) A set of size equal to `t` perform the following steps.

  1) Verify the prior proofs.

  2) Calculate the binding factor by hashing:
    - The group key
    - The message
    - Every contribution to the nonce, both the ECC points and ciphertexts
      *with who contributed it*

  3) For `D_i`, `E_i`, sum them to `*_point` and the ciphertexts for their discrete
     logarithm to `*_ciphertext`;

  4) Set
     `S = (D_ciphertext + (binding * E_ciphertext)) + (challenge * K_ciphertext)`.

  5) Set the decryption share for `S` to be `private_key_share * S.0` (the local
     participant's share of the threshold decryption key multiplied by the
     ciphertext's randomness commitment).

  6) Broadcast `S` with a `RELATIONS` proof for `[[G], [S.0]]`,
     `[verification_key, decryption_share]` (proving the well-formedness of the
     share).

4) Sum the decryption shares for `S` and attempt decryption. If `R, s` is a
   valid signature, the protocol completes. Otherwise, the decryption shares'
   proofs are verified to discover which is faulty.

### Practical Comments on Security

This protocol fundamentally relies on [CL15](https://eprint.iacr.org/2015/047)
standing. Additionally, it requires the proofs used be valid. This section
attempts to comment on the security of the composition provided *in an informal,
practical manner*.

- The security of the ECC nonces.

The ECC nonce creation lines up with [FROST](https://eprint.iacr.org/2020/852).

- The nonce ciphertexts can be decrypted to perform a key recovery.

Only by a malicious threshold.

- Concurrent security.

The signature itself is assumed to have concurrent security as FROST does. There
is a potential concern the ciphertext decryption process doesn't achieve
concurrent security.

Please note the only decrypted ciphertext is the sum of `t` participants
ciphertexts. Accordingly, randomness from every single participant is
incorporated. Another participant cannot choose their randomness to cancel out
someone else's due to the proof of knowledge bound.

While the randomness is presumably able to be biased, it has the same binding
factor process FROST itself had.  The question becomes can the outputs of two
biased DKGs, one weighted by a binding factor, summed, cause problems. The
presumption is not. If it can, a new nonce process would be needed.

- A nonce could be reused.

One of the requirements for the signing protocol prevents this.

If there is no preprocessing, nonces will only be used for a signle message.

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

### Future Work

Obviously, the above composition needs its security formalized and proven. It is
in no way claimed to be currently secure.

The library itself needs to be moved from being a proof of concept to a proper
production library. With this needs to be compensation for the fact it's
variable time (sufficient masking and/or moving proving to constant time) and
auditing. The currently implemented `RELATIONS` proof must also be corrected.

Using the [techniques from BICYCL](https://eprint.iacr.org/2022/1466), and by
moving to GMP, it should be possible to reduce the amount of work by ~4x, at
least. Further work can be done not only on parallelism, yet subcommittees such
that any individual signer only performs a logarithmic amount of computation to
the amount of signers.

If you are interested in this, please feel free to reach out to @kayabaNerve on
Twitter and Discord, or @kayabanerve:matrix.org on Matrix.
