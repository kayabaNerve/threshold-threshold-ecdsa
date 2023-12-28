# Threshold Threshold ECDSA

A threshold ECDSA experiment premised on threshold encryption for the MtA.

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

### References

- https://eprint.iacr.org/2015/047.pdf defined class groups
- https://eprint.iacr.org/2022/1437.pdf applies class groups to a
  threshold-encryption use-case

### TODO:

- Remove reliance on the Strong Root Assumption, if present and possible
- Proofs (literal)
- Clean code with a competent API
- Proofs (theoretical)
- Make constant time, as possible, or mask secret-involving calculations
- Correct various security parameters
- Decentralized calculation of the K ciphertext
- Proven calculation of X
- Share verification
