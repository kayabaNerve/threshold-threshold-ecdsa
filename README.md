# Threshold Threshold Schnorr

So long as a set of `t` signers is online for each of the two rounds, this will
produce a Schnorr signature *with fully linear signing complexity*. There is no
requirement the signers online for each round are consistent.

Please see the
[develop branch](https://github.com/kayabaNerve/threshold-threshold-ecdsa) for
its
[README](https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/develop/README.md)
and
[write-up](https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/develop/write-up.md)
on the theory for this protocol and caveats for this library.

Additionally, please the write-up present on this branch for the Schnorr variant
specifically. Its immediately describable as FROST implemented within the
context of [CL15](https://eprint.iacr.org/2015/047) by a threshold decryption
key.

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
- https://eprint.iacr.org/2022/1437 applies class groups to a
  threshold-encryption use-case
- https://eprint.iacr.org/2020/852 for FROST.
