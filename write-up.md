# 67-of-100 Threshold ECDSA in <3s

Implemented at https://github.com/kayabaNerve/threshold-threshold-ecdsa.

That implementation probably isn't secure. It probably has a constant or two
wrong. It runs in variable time.

... but I don't believe it's fundamentally broken.

## The Protocol

The protocol relies on class groups to offer homormorphic encryption which offer
a trustless setup which is error-free (not requiring re-attempts, such as
protocols which randomly generate numbers until achieiving sums which are
prime).

### Proofs

Three ZK proofs are needed.

1) A DLog PoK.
2) A proof an elliptic point's discrete log is encrypted as the message within a
   ciphertext.
3) A general relations proof proving that for a matrix of elements and a row of
   secrets, an output row of elements is the result of a multiexp of each row of
   elements by the row of secrets.

The first proof immediately resolves to the third for a matrix of `[[G]]`. The
second proof is likely a trivial extension over the third proof. If preferable,
more specific proofs (with better performance or better assumptions) may be used
however.

https://eprint.iacr.org/2021/205 provides the first two proofs, yet not
explicitly the third proof (though one is realizable). Its proofs rely on a
weaker assumption and are generally preferred.

### DKG

The class group needs construction. The
[original 2015 paper](https://eprint.iacr.org/2015/047) on a homomorphic
encryption scheme over class groups does describe generation with solely public
parameters. In order to satisfy the strong root assumption,
[Bandwidth-threshold threshold EC-DSA](https://eprint.iacr.org/2020/084)
proposed a distinct mechanism. Accordingly, it is preferred (though not required
and not currently implemented into threshold-threshold-ecdsa).

Generators should be chosen via one of the methods in
https://eprint.iacr.org/2024/034, which offers a hash to class group element.

Participants additionally run the integer secret sharing system from
https://eprint.iacr.org/2022/1437, which also provides a general relations proof
satisfying the above definition. The most expensive part of this is the `t` DLog
proofs. Ideally, a two-round protocol which only uses a single proof for either
the first commitment (as per PedPoP) or a single proof for all commitments
(MuSig-aggregated) is instead used.

Finally, a ciphertext (encrypted to the group's threshold key, as all
ciphertexts here are) for the private key is created. This can be done by
participants publishing `K_i`, an ECC point, with a ciphertext encrypting its
discrete log (with the relevant proof). The group's key is `sum(K_i)` with the
ciphertext similarly defined.

### Signing

Signing is described as a 3-round protocol either without concurrent security or
without preprocessing, with identifiable aborts. This can be performed by a
threshold of participants using lagrange interpolation on their decryption
shares, the literal inclusion of is ignored here.

1) All participants provide `X_i`, an ECC point, and a ciphertext for its
   discrete log with the relevant proof.

2) Verify the prior proof. All participants provide a ciphertext for `y_i`,
   along with the ciphertexts for `x_ciphertext` (sum `x_i_ciphertexts`) and
   `k_ciphertext` scaled by `y_i`. The relations proof is used to demonstrate
   consistency.

3) Verify the prior proof. Set `y = sum(y_i_ciphertexts)`,
   `z = xy_i_ciphertexts`, `d = ky_i_ciphertexts`. Set `dr` as `d` scaled by the
   x coordinate of `X` (reduced into the scalar field). Set `my` as `y` scaled
   by the message (hashed into the scalar field). Set `w = my + dr`. All
   participants publish `w` and `z` scaled by their key shares (the decryption
   shares) with a relations proof proving consistency.

4) Sum the decryption shares for `w` and attempt decryption. Do the same for
   `z`. If `w / z` is a valid signature, the protocol completes. Otherwise, the
   decryption shares' proofs are verified to discover which is faulty.

Concurrent security may not be present in the above protocol if it's possible to
apply Wagner's algorithm to find a list of ciphertexts whose randomnesses sum to
equal to a targeted ciphertext. This would allow decrypting a private key or
nonce, leaking the private key. By deciding on the message before the protocol
starts, and committing to `y_i_ciphertext`, `ky_i_ciphertext`, and the
randomness which will be used in `xy_i_ciphertext` in round 1, concurrent
security is assumed.

threshold-threshold-ecdsa implements the above signing protocol, with the
commitment to the randomness, and achieves 67-of-100 signing in less than 3s per
party (2GHz 12th Gen Intel, single thread).

### Future Work

Obviously, the above composition needs its security formalized and proven. It is
no way claimed to be currently secure.

The library itself needs to be moved from being a proof of concept to a proper
production library. With this needs to be compensation for the fact it's
variable time (sufficient masking and/or moving proving to constant time) and
auditing. Ideally, the relations proof is moved to the best possible assumption
available (likely the adaptive root assumption).

Using the [techniques from BICYCL](https://eprint.iacr.org/2022/1466), and by
moving to GMP, it should be possible to reduce from 3s to less than 1s per
party. Further work can be done not only on parallelism, yet subcommittees such
that any individual signer only performs a logarithmic amount of computation to
the amount of signers.

The signing protocol itself can be further optimized if a hash-to-ciphertext
exists. `y_i` could be generated via a hash-to-ciphertext, removing the need to
broadcast it and prove knowledge of its discrete log. Instead of scaling
`k_ciphertext` and `x_ciphertext` by `y_i`, `y_ciphertext` would be scaled by
`k_i` (obtained during the DKG) and `x_i`.

If you are interested in this, please feel free to reach out to @kayabaNerve on
Twitter and Discord, or @kayabanerve:matrix.org on Matrix.
