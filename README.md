# CompStark

Fast, formally verified components of a STARK prover and verifier in Lean 4, benchmarked against [Plonky3](https://github.com/Plonky3/Plonky3).

CompStark builds on [CompPoly](https://github.com/Verified-zkEVM/CompPoly), which provides the fields, packed storage and transforms: KoalaBear in Montgomery form, its quartic extension, parallel NTTs and the batched coset low-degree extension. CompStark adds the protocol layers on top: hashing, Merkle commitments, FRI and the prover and verifier. Every fast implementation comes with a proof that it computes its specification, and with a benchmark against the corresponding Plonky3 component.

## Status

- Poseidon2 over KoalaBear, widths 16 and 24, with Plonky3's default constants (`CompStark/Poseidon2`). The specification runs on any field of characteristic `p`; tests check Plonky3's outputs. `permute_map` transports a run along any ring homomorphism, so the permutation on CompPoly's Montgomery field is the specification (`fast_width16`, `fast_width24`).

- Packed Poseidon2 (`CompStark/Poseidon2/Packed.lean`): eight states at a time, one per vector lane, with macro-generated round kernels on Montgomery words. `permute16_width16` (`PackedCorrectness.lean`) proves that on every group of eight states it computes Plonky3's width-16 permutation, read in the spec field, and leaves the rest of the buffer unchanged. Single thread, on a loaded 8-core Ryzen 7 3700X: about 370 ns per permutation, against 140 ns for Plonky3's AVX2-packed `Poseidon2KoalaBear<16>` and 730 ns for its scalar one (`CompStarkBench poseidon2-packed 14`, `bench/rust: compstark-bench bench 14`).
- Hashing and Merkle commitments (`CompStark/Hash/Sponge.lean`, `CompStark/Merkle/Tree.lean`): Plonky3's `PaddingFreeSponge` and `TruncatedPermutation`, and `MerkleTree::new` over lists of matrices of mixed heights, with the Poseidon2 instances of Plonky3's `Poseidon2MerkleMmcs` (width-24 sponge for leaves, width-16 compression). Tests check digests and roots against Plonky3, including odd heights and injected smaller matrices.

## Building

```bash
lake exe cache get   # Mathlib's prebuilt oleans
lake build
lake test
```

The Rust side lives in `bench/rust`; `cargo run --release` prints the Poseidon2 known answers used by the tests.
