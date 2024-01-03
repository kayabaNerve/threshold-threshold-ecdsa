# Threshold Threshold ECDSA

A threshold ECDSA experiment premised on threshold encryption for the MtA.

This achieves a 3-round O(n) signing protocol with identifiable aborts and
without a trusted setup (if correct). The message only needs to be known by the
last round, enabling the first two to be preprocessed.

### Theory

[Low-Bandwidth Threshold ECDSA via Pseudorandom Correlation Generators](https://eprint.iacr.org/2021/1587)
defines ECDSA tuples as a pair of additively-shared multiplication triples. In
our own, only slightly modified, notation,

```
x_i = rand()
y_i = rand()
z = sum(x_i) * sum(y_i)
d = k * y
```

where `k` is the discrete logarithm w.r.t. `G` of the ECDSA public key
(the private key).

These can then form an ECDSA signature as follows, in our own notation:

```
r = (xG).x.to_scalar()
w_i = (H(m) * y) + (r * d)
Publish w_i, z_i
s = w / z
```

The challenge with multiparty ECDSA is the lack of efficient algorithms to
distribute the additive shares of `z` and `d`. The proposal is to use a
threshold-encryption Paillier key as follows, where `x`, `y`, and `z` are used
to represent any arbitrary additive-sharing of the value `z` such that
`z = x * y`:

- `ciphertext_x_i` = `Enc(x_i)` <- 1 round of communication
- `ciphertext_x` = `Product(ciphertext_x_i)`
- `ciphertext_xy_i` = `ciphertext_x ** y_i` <- 1 round of communication
- `ciphertext_z` = `Product(ciphertext_xy_i)`
- `z_i` = `rand()` for i in 2 ..= t
- `ciphertext_z_i` = `Enc(-z_i)` <- 1 round of communication, parallelizable
   with the above round
- `ciphertext_z_1` = `Product(ciphertext_z, ciphertext_z_i)`
- Send decryption share for `ciphertext_z_1` if i in 2 ..= t <- 1 round of
  communication

At this time, this does not describe a verifiable scheme yet a verifiable scheme
is presumed to be possible to build on top.

This achieves a 3-round protocol, so long as no additional rounds are needed for
proofs, which performs a MtA-equivalent in *O(n)* time, not *O(n\*\*2)*,
assuming the decryption process is so linear.

### Difficulties in Using Threshold Paillier (or Similar)

Threshold RSA, which is the focus when discussing threshold discrete-log
solutions, has been an incredibly difficult challenge. Section 1.1 of
[Tiresias: Large Scale, Maliciously Secure Threshold Paillier](https://eprint.iacr.org/2023/998)
provides an extensive overview of various schemes throughout history. They also
cover recent advancements drastically increasing the practicality of threshold
RSA and provide their own innovations (which then are specifically applied to
Paillier, a cryptosystem with similarly formed public keys).

There is also a threshold solution for the Joye-Libert cryptosystem, as
presented in
[Threshold Cryptosystems Based on 2k-th Power Residue Symbols](https://eprint.iacr.org/2023/601).
Joye-Libert was recently noted for its efficiency in threshold ECDSA protocols
in
[Efficient Multiplicative-to-Additive Function from Joye-Libert Cryptosystem and Its Application to Threshold ECDSA](https://eprint.iacr.org/2023/1312).

And then back to the original RSA DKG problem,
[Improved Distributed RSA Key Generation Using the Miller-Rabin Test](https://eprint.iacr.org/2023/644)
was a recent and notable paper (which is a citation in Tiresias).

While all of these show threshold discrete-log solutions are possible, they
still:

- Have an error rate
- Take tens of minutes to generate at large scales
- Take several thousands of lines of code

This work uses class groups, whose keys are any integer in the multiplicative
group for the modulus, and accordingly does not face such difficulties.

### Should I use this?

# No.

### What needs to be done before anyone uses this?

- The protocol implemented needs to be formalized and have its security proven.
- The protocol should be modified to achieve concurrent security.
- The security parameters used (along with other constants) need review.
- The code demonstrates signing. Some parts of the DKG are shimmed. Said shims
  would need removal.
- This demonstration would need to be transformed into a proper library (with
  much cleaner code. Notably, `Element` should implement the standard math
  traits for operator-based usage).
- Secret-involving math operations need to be masked to prevent side-channel
  attacks.
- Secret variables need to be zeroized post-use.
- The multiexp function should have much more liberal usage.
- A batch verifier should be implemented.
- Every public key and generator should be tabled.
- rayon should be used for internal parallelism.

### Will you do this?

I don't currently have the time nor financial incentive.

### Achieving Concurrent Security

I believe it's theoretically possible to apply the techniques of
https://eprint.iacr.org/2018/417 not to produce an unintended signature, yet to
cause decryption of an unintended ciphertext. This is due to how if the sum of
a list of ciphertexts' randomness are equal to a distinct ciphertext's
randomness, decrypting every ciphertext in the list will enable decrypting the
distinct ciphertext.

Preventing this should be possible via pre-committing to the randomness used for
every decrypted ciphertext. While this would add a round, round one's randomness
isn't present in any decrypted ciphertext. It's further permutated in round two,
meaning a commitment in round one to the independent permutations in round two
(along with the randomness used in proofs for round two onwards) should be
sufficient.

### Other Notes

This library uses additive notation, not multiplicative, in contrast with most
literature on class groups. It also denotes `t` as the amount needed to produce
a signature (not the amount allowed to be corrupted).

This library also prefers `BigUint` for its scalar type, not `BigInt`, an
artifact from my experience being based on elliptic curves which needs to be
corrected in order to avoid a halved space.

Ideally, this ends up taking <10s for the prover (it does already, yet
introducing masking would slow it down) and <2s per other party. Across 4
threads, this would enable a t=50 ECDSA in 27.5s.

This library does not implement any of the maps described in
https://eprint.iacr.org/2022/1466, and doesn't have an optimal reduction
algorithm (always using big integers and never native words for parts). Those
should be implemented and would further reduce the time from the above ideal.

### References

- https://eprint.iacr.org/2015/047 defined a homomorphic encryption scheme from
  class groups
- https://eprint.iacr.org/2020/084 for a proof a ciphertext encrypts the
  discrete log of a provided point (also an earlier work on applying class
  groups to achieve threshold ECDSA)
- https://eprint.iacr.org/2021/205 for ZK PoKs not requiring repetition and
  better assumptions
- https://eprint.iacr.org/2021/291 as the most modern application of class
  groups to threshold ECDSA (ignoring partial improvements)
- https://eprint.iacr.org/2021/1587 for the aforementioned ECDSA transformation
- https://eprint.iacr.org/2022/1437 applies class groups to a
  threshold-encryption use-case
