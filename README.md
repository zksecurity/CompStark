# CompStark

Fast, formally verified components of a STARK prover and verifier in Lean 4, benchmarked against [Plonky3](https://github.com/Plonky3/Plonky3).

CompStark builds on [CompPoly](https://github.com/Verified-zkEVM/CompPoly), which provides the fields, packed storage and transforms: KoalaBear in Montgomery form, its quartic extension, parallel NTTs and the batched coset low-degree extension. CompStark adds the protocol layers on top: hashing, Merkle commitments, FRI and the prover and verifier. Every fast implementation comes with a proof that it computes its specification, and with a benchmark against the corresponding Plonky3 component.

## Status

- Poseidon2 over KoalaBear, widths 16 and 24, with Plonky3's default constants (`CompStark/Poseidon2`). The specification runs on any field of characteristic `p`; tests check Plonky3's outputs. `permute_map` transports a run along any ring homomorphism, so the permutation on CompPoly's Montgomery field is the specification (`fast_width16`, `fast_width24`).

- Packed Poseidon2 (`CompStark/Poseidon2/Packed.lean`): eight states at a time, one per vector lane, with macro-generated round kernels on Montgomery words. `permute16_width16` and `permute24_width24` (`PackedCorrectness.lean`, `PackedCorrectness24.lean`, on the width-generic `PackedLanes.lean`) prove that on every group of eight states they compute Plonky3's width-16 and width-24 permutations, read in the spec field, and leave the rest of the buffer unchanged. The S-box cube leaves its square unreduced and reduces the product by sign, and the sum of a partial round is a tree beside its S-box. Single thread, on an 8-core Ryzen 7 3700X: about 189 ns per width-16 permutation and 289 ns per width-24 one, against 108 ns and 179 ns for Plonky3's AVX2-packed `Poseidon2KoalaBear` and 624 ns for its scalar width-16 one (`CompStarkBench poseidon2-packed 14`, `CompStarkBench perm24 14`, `bench/rust: compstark-bench bench 14`).
- Hashing and Merkle commitments (`CompStark/Hash/Sponge.lean`, `CompStark/Merkle/Tree.lean`): Plonky3's `PaddingFreeSponge` and `TruncatedPermutation`, and `MerkleTree::new` over lists of matrices of mixed heights, with the Poseidon2 instances of Plonky3's `Poseidon2MerkleMmcs` (width-24 sponge for leaves, width-16 compression). Tests check digests and roots against Plonky3, including odd heights and injected smaller matrices.
- Packed Merkle commitment (`CompStark/Merkle/Packed.lean`): the root of one matrix given as chunks of rows, leaves hashed eight rows at a time by the packed width-24 sponge in parallel chunk tasks, layers compressed eight pairs at a time by the packed width-16 permutation in parallel range tasks. `root_eq` (`RootCorrectness.lean`, on `PackedCorrectness.lean`) proves it is `Merkle.KoalaBear.root` of that matrix. For $2^{14}$ rows of 64 elements: about 3.8 ms on 16 chunks and 25.6 ms on one core, against 2.1 ms and 15.6 ms for Plonky3's `MerkleTreeMmcs::commit` on its default rayon pool and on one thread (`CompStarkBench merkle 14 64 16`, `taskset -c 5 CompStarkBench merkle 14 64 1`, `bench/rust: compstark-bench merkle 14 64`, `RAYON_NUM_THREADS=1`).

## Building

```bash
lake exe cache get   # Mathlib's prebuilt oleans
lake build
lake test
```

The Rust side lives in `bench/rust`; `cargo run --release` prints the Poseidon2 known answers used by the tests.
