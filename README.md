# Threshold Threshold Schnorr

Please see the [develop branch](https://github.com/kayabaNerve/threshold-threshold-ecdsa)
for the write-up and why you shouldn't use this. This is a modification to that
protocol for Schnorr signatures, with the advantage of being *robust* with a
fixed complexity.

The ECDSA protocol write-up describes a commitment to achieve concurrent
security. I don't currently believe that commitment necessary, due to believing
solutions being a break to the discrete log problem. If that commitment is
necessary, then private state is shared between rounds and this loses its
robustness.

For the actual Schnorr protocol underlying this, FROST is used to achieve a
2-round protocol.


Without the commitment, the randomness used during decryption is would
presumably equivalent to a biased DKG. This is except for the fact the
randomness is the result of two biased DKGs, one multiplied by the binding
factor before summation. Accordingly, having the binding factor be inclusive of
this larger scheme may resolve concerns there.

### Should I use this?

# No.

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
- https://eprint.iacr.org/2020/852 for FROST.
