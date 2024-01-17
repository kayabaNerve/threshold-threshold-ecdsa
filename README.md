# Threshold Threshold Schnorr

So long as a set of `t` signers is online for each of the two rounds, this will
produce a Schnorr signature *with fully linear signing complexity*. There is no
requirement the signers online for each round are consistent.

Please see the
[write-up](https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/schnorr/write-up.md)
for more information. Its immediately describable as FROST implemented within
the context of [CL15](https://eprint.iacr.org/2015/047) by a threshold
decryption key.

Please see the
[develop branch](https://github.com/kayabaNerve/threshold-threshold-ecdsa) for
a rougher protocol targeting ECDSA and its
[README](https://github.com/kayabaNerve/threshold-threshold-ecdsa/tree/develop/README.md)
which provides more context on the state of this library.

### Should I use this?

# No.

### References

- https://eprint.iacr.org/2015/047 defined a homomorphic encryption scheme from
  class groups
- https://eprint.iacr.org/2020/084 for a proof a ciphertext encrypts the
  discrete log of a provided point
- https://eprint.iacr.org/2021/205 for ZK PoKs not requiring repetition and
  better assumptions
- https://eprint.iacr.org/2022/1437 applies class groups to a
  threshold-encryption use-case
- https://eprint.iacr.org/2020/852 for FROST.
