# CompStark

Fast, formally verified components of a STARK prover and verifier in Lean 4, benchmarked against [Plonky3](https://github.com/Plonky3/Plonky3).

CompStark builds on [CompPoly](https://github.com/Verified-zkEVM/CompPoly), which provides the fields, packed storage and transforms: KoalaBear in Montgomery form, its quartic extension, parallel NTTs and the batched coset low-degree extension. CompStark adds the protocol layers on top: hashing, Merkle commitments, FRI and the prover and verifier. Every fast implementation comes with a proof that it computes its specification, and with a benchmark against the corresponding Plonky3 component.

## Status

- Poseidon2 over KoalaBear, widths 16 and 24, with Plonky3's default constants (`CompStark/Poseidon2`). The specification runs on any field of characteristic `p`; tests check Plonky3's outputs.

## Building

```bash
lake exe cache get   # Mathlib's prebuilt oleans
lake build
lake test
```

The Rust side lives in `bench/rust`; `cargo run --release` prints the Poseidon2 known answers used by the tests.
