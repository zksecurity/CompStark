# CompStark

Fast, formally verified STARK provers and verifiers in Lean 4. CompStark implements Plonky3's STARK and batch STARK, proves them complete and knowledge-sound with concrete security bounds, and runs them at speeds comparable to Plonky3.

The goal is a Lean library with state-of-the-art prover and verifier performance and state-of-the-art security analysis for every configuration people use, over prime and binary fields, adopting new protocols as they appear: see [VISION.md](VISION.md).

## What is proven

The protocols are Plonky3's `uni-stark` and `batch-stark` at revision `a4982ec`: AIRs with preprocessed and periodic columns, LogUp lookups over buses, two-adic FRI of any folding arity, Poseidon2 Merkle commitments with caps, and Plonky3's Fiat–Shamir transcript with grinding. They run over any prime field with two-adic domains (KoalaBear and BabyBear are instances) and any extension of it (the quartic and quintic extensions of KoalaBear). Tests check that the verifier accepts Plonky3's proofs and that both provers reproduce them byte for byte.

| Theorem | Statement | Assumptions |
|---|---|---|
| Completeness (`Stark.completeness`, `Batch.completeness`, interactive `Iop.Setup.completeness`) | An honest proof of a satisfying trace verifies; the honest prover of the oracle protocol is accepted. | A valid configuration; the out-of-domain point avoids the base field, grinding finds a witness, and no lookup denominator vanishes. |
| Knowledge soundness, interactive (`Iop.knowledgeSoundness`, `Iop.batchKnowledgeSoundness`) | The STARK and the batch STARK as oracle protocols on ArkLib's interaction layer, the trace length the prover's first message: against any prover, the verifier accepts while no trace of the claimed length close to the committed one satisfies the AIR with probability at most the knowledge error, the largest over the lengths the verifier admits. The proof is a round-by-round knowledge certificate, CompStark's DEEP-ALI rounds appended to ArkLib's FRI certificate. | The extractor's decoding radius is below `1 - rate`. |
| Knowledge soundness, non-interactive (`Iop.knowledgeSoundness_ro`, `Iop.Batch.batchKnowledgeSoundness_ro`) | The same for Plonky3's verifier as it runs, at the trace length the proof claims, with Merkle commitments, Fiat–Shamir and grinding, against a prover making `Q` hash queries. | Poseidon2's roles (challenger, leaf hash, compression) are random oracles; for `uni-stark`, the field has at least `2 ^ 8` elements and two-adicity below `2 ^ 64`. |
| Fast prover (`KoalaBear.prove_fast`, `KoalaBear.proveBatch_fast`) | The fast prover outputs exactly the specification prover's proof. | Well-shaped inputs; the out-of-domain point avoids the base field. |
| Fast verifier (`verifyFast_eq`) | The fast verifier is the specification verifier. | None. |

The knowledge errors are explicit sums of one term per challenge, proved from correlated agreement up to the unique-decoding radius and, using ArkLib's Johnson-regime bounds, up to the Johnson radius `1 - √rate`. A security calculator turns them into a kernel-checked number of bits for any AIR and configuration (below). Every theorem is checked by Lean's kernel: no `sorry`, no `native_decide`.

## How it is built

- **[CompPoly](https://github.com/Verified-zkEVM/CompPoly)** provides the fields and transforms: 32-bit Montgomery fields, their extensions, parallel NTTs and the batched coset low-degree extension.
- **Hashing and commitments** (`CompStark/Poseidon2`, `CompStark/Hash`, `CompStark/Merkle`): Poseidon2 on any field, equal to ArkLib's specification, vectorized kernels for KoalaBear, Plonky3's sponge, compression and Merkle trees of mixed heights, bridged to [VCVio](https://github.com/Verified-zkEVM/VCVio)'s verified Merkle tree.
- **Protocols** (`CompStark/Fri`, `CompStark/Stark`, `CompStark/Batch`, `CompStark/Lookup`): specification provers and verifiers, written once over their hash functions so that the same verifier runs on Poseidon2 and on random oracles.
- **Fast backend** (`CompStark/Stark/Fast`): the prover over packed Montgomery words, with constraints compiled to vectorized straight-line code, each kernel proved against its specification.
- **Analysis** (`CompStark/Interaction`, `CompStark/Sound`, `CompStark/Complete`): the STARK and the batch STARK as oracle protocols on [ArkLib](https://github.com/Verified-zkEVM/ArkLib)'s interaction layer with their round-by-round knowledge certificates, completeness, knowledge soundness and the error terms, on ArkLib's coding theory and FRI.

CompPoly and ArkLib are pinned to branches of forks that carry the results CompStark needs before they are upstream.

[docs/components.md](docs/components.md) describes every component with its files, theorems, assumptions and benchmarks.

## Performance

Proving time on an 8-core Ryzen 7 3700X, against Plonky3 built for the native CPU (16 threads / 1 thread):

| Workload | CompStark | Plonky3 |
|---|---|---|
| `wide 64` AIR (64 columns, degree 3), $2^{16}$ rows, blowup 2, 100 queries | 0.33 s / 1.32 s | 0.35 s / 1.96 s |
| `wide 64` AIR, $2^{18}$ rows | 1.14 s / 4.8 s | 1.20 s / 7.9 s |
| Batch of three `wide 64` tables, $2^{20}$, $2^{19}$ and $2^{16}$ rows | 6.0 s / 26.7 s | 6.3 s / 42.0 s |
| Plonky3's Keccak-f example, $2^{16}$ rows | 1.96 s | 1.82 s |
| Plonky3's Keccak-f example, $2^{18}$ rows | 8.2 s | 10.9 s |

Verifying the Keccak proof takes about 50 ms, against 11 ms for Plonky3. [docs/components.md](docs/components.md) has the configurations, the commands and per-phase breakdowns.

## Security of your own AIR

1. Build a `Statement` (or `Batch.Statement`) for your AIR and FRI parameters, at any folding arity: `⟨params, air, colsInWidth⟩`. The verifier takes the trace length from the proof, so the statement covers every length it admits (`Statement.Admits`, decided by `C.admits n`); `C.setupOf EF n h` is the setup at an admitted length `n`.
2. Let the calculator search the analysis at a length, the longest admitted one usually being the worst, and read the bits of each term:

   ```lean
   #eval (myStatement.setupOf EF 22 (by decide)).knowledgeErrorReport 2130706433 .uniqueDecoding
     ((myStatement.setupOf EF 22 (by decide)).bestAnalysis 2130706433 .uniqueDecoding)
   #eval (myStatement.setupOf EF 22 (by decide)).roundErrorReport 2130706433 .uniqueDecoding
     ((myStatement.setupOf EF 22 (by decide)).bestAnalysisRo 2130706433 .uniqueDecoding)
   ```

   The report shows the analysis it found: FRI's radius `δ`, the extractor's `δ'` and the loss. Change the FRI parameters until the total reaches your target, or pick an analysis by hand: `δ` where the MCA bound admits batching and every fold (`δ ≤ (1 - rate) / 2` for `.uniqueDecoding`, below `1 - √rate` for `.uniqueOrJohnson`), `δ ≤ δ'`, `δ'` below the Johnson radius `1 - √rate`, and a positive loss (`fits: false` otherwise).
3. Check it in the kernel at every admitted length at once and apply the theorem (`KoalaBear.card_eq : Nat.card F = 2130706433`), with the analysis written out:

   ```lean
   def myAnalysis : Analysis := ⟨3/8 - 1/2^14, 3/8 - 1/2^17, 1/2^19⟩
   theorem my_secure : myStatement.Secure EF 2130706433 .uniqueDecoding myAnalysis 128 := by
     decide +kernel
   theorem my_knowledgeSoundness (publicValues : List F)
       {OutP : (myStatement.protocol EF).tree.ExecutionPath → Type}
       (prover : Interaction.Oracle.Prover.Strategy unifSpec (myStatement.protocol EF).tree
         (myStatement.protocol EF).roles OutP) :
       myStatement.farAcceptance EF publicValues (fun _ ↦ (49151 / 131072 : NNReal)) prover ≤
         (2 ^ 128)⁻¹ :=
     knowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ my_secure _
       (by norm_num [myAnalysis]) publicValues prover
   ```

   Per oracle answer, `myStatement.SecureRo` and `knowledgeSoundness_ro_of_secureRo` bound the verifier's acceptance at the length the proof claims, given `2 ^ 8 ≤ Nat.card F` and `twoAdicity F < 2 ^ 64` (the STARK's domain separator then fixes the length). For a large AIR, prove its shape at every length once (`shape_eq_of_profileFits`) and certify each length with `secure_of_shape`, as `secureRo_of_lengths` in `tests/CompStarkTests/KeccakSecurity.lean` does for Keccak.

   The kernel evaluates the AIR's structure but never a field operation; keep every number of the check in `Nat` and `ℚ`.

## Building

```bash
lake exe cache get   # Mathlib's prebuilt oleans
lake build
lake test
```

`lake test` runs the known-answer tests and checks Plonky3's proofs. The Rust side in `bench/rust` produces the reference data and runs Plonky3's benchmarks; [docs/components.md](docs/components.md) lists its commands.

## Roadmap

1. Binary fields, following [leanVM](https://github.com/leanEthereum/leanMultisig): a binary tower field, WHIR, and Binius-style ring switching.
2. Multilinear proving, following [SP1 Hypercube](https://blog.succinct.xyz/sp1-hypercube/): zerocheck by sumcheck, LogUp-GKR, and Basefold behind the jagged commitment.
3. Newer polynomial commitments and their analyses as they appear.
4. Zero knowledge.
