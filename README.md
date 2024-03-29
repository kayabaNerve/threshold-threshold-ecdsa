# Threshold Threshold ECDSA

A fully-linearly-scaling threshold ECDSA signing experiment premised on
threshold encryption.

This achieves a 3-round O(n) (in bandwidth and computational cost) signing
protocol with identifiable aborts and without a trusted setup (if correct). The
first two rounds may be preprocessable.

Please see the [write-up](./write-up.md) for more info on the protocol.

For a 2-round non-robust protocol, please see
https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/two-round/write-up.md.

For a 2-round robust Schnorr protocol, please see
https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/schnorr/write-up.md.

Prior work on fully-linear schemes include
[Threshold-optimal DSA/ECDSA signatures and an application to Bitcoin wallet security](https://eprint.iacr.org/2016/013),
a paper the author of this work was informed of the day after publication. GGN
achieved linearity yet use a proof which requires an RSA modulus, one the
product of two safe primes. While that can be generated by a trustless setup,
this work benefits from significantly reduced complexity in its setup (a couple
orders of magnitude).

### Should I use this?

# No.

### What needs to be done before anyone uses this?

- The protocol implemented needs to be formalized and have its security proven.
- The security parameters used (along with other constants) need review.
- The code demonstrates signing. Some parts of the DKG are shimmed. Said shims
  would need removal.
- This demonstration would need to be transformed into a proper library (with
  much cleaner code. Notably, `Element` should implement the standard math
  traits for operator-based usage).
- Secret-involving math operations need to be masked to prevent side-channel
  attacks.
- Secret variables need to be zeroized post-use.
- rayon should be used for internal parallelism.
- gmp should be moved to.

### Will you do this?

Possibly. I am interested, yet am busy with other tasks and do not have the
financial means necessary to do this entirely on my own.

### Other Notes

This library uses additive notation, not multiplicative, in contrast with most
literature on class groups. It also denotes `t` as the amount needed to produce
a signature (not the amount allowed to be corrupted).

This library also prefers `Natural` for its scalar type, not `Integer`, an
artifact from my experience being based on elliptic curves which needs to be
corrected in order to avoid a halved space.

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
