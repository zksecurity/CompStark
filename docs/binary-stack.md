# Binary-field multilinear stack

The components of a multilinear proof system over the binary field `BF64` and its cubic extension, as leanMultisig's leanVM uses them: the Keccak overwrite-duplex transcript and Keccak-256 Merkle commitment, a polynomial commitment from stacked additive Reed–Solomon codewords, ring switching and a WHIR opening, and the Keccak-f GKR argument. Each has a specification, a prover, a verifier and a soundness analysis; each fast implementation is proved equal to its specification. The tests compare them with leanMultisig `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`.

None of these components is at parity with the Rust reference. The table gives the measured gap where the Lean code and the workload match a Rust measurement, and says where a component is unmeasured.

| Component | Workload | Lean / Rust, single-thread instructions |
| --- | --- | --- |
| Keccak-f GKR prover (`Keccak.GkrProver.prove`) | The reduction on 512 permutations (`tests/data/keccak-gkr/active`), output claims bound before the phase | 7.9× against leanMultisig's standalone reduction (291 million instructions), 10.5× against the same reduction inside its full Fibonacci proof (218 million) |
| Merkle commitment (`Keccak.Merkle`) | 4,096 rows of 64 words; 100 queries ([components](components.md#streaming-keccak-merkle-commitments-and-overwrite-duplex)) | 4.03× commit, 0.72× open |
| Duplex writer (`Keccak.Duplex`) | 10,000 messages written and sampled; an eight-bit grind ([components](components.md#streaming-keccak-merkle-commitments-and-overwrite-duplex)) | 2.88× write and sample, 2.99× grind |
| PCS prover kernels (`Pcs.RingSwitch`, `Pcs.Tensor`) | Six-map coordinates, 64 packed bit folds, 256 mapped weights ([binary PCS](binary-pcs.md#kernel-measurements)) | 8.58×, 3.84×, 7.27× |
| Honest PCS prover (`Pcs.Honest`) | — | Unmeasured; a specification prover, not the fast opening |
| PCS verifier and extractor (`Pcs.Verifier`, `Pcs.Extraction`, `Pcs.ExtractorCache`) | — | Unmeasured as components |
| Keccak-f GKR verifier (`Keccak.Gkr.Executable`) | — | Unmeasured as a component |

The Keccak-f GKR count is the `keccak-gkr` performance-gate workload, 2.31 billion instructions; the Rust counts are leanvm-security's single-thread measurements of leanMultisig at the same revision on the same host (an AMD Ryzen 7 3700X), the standalone one from its `docs/keccak-gkr-benchmark.md` and the in-proof one from its `docs/gkr-packed-performance.md`, not re-measured here.

The last leanvm-security measurements of the complete leanVM proof system put its PCS opening at 22× Rust and its whole verifier at 4.6–4.9×; the opening driver and the verifier as measured there are leanVM's composition and are not part of this library.

## Fields

`CompStark/BinaryFields` fixes `K = BF64` and `E = BF64.Ext3` from CompPoly, the extension's limbs, and a kernel-checked certificate that `g` generates `K`'s multiplicative group (`Generator`). `Native` and `WordProduct` replace the field operations in compiled code with CompPoly's word arithmetic and the five-product cubic multiplication, each by a `csimp` theorem equating them with the specification instances.

## Keccak transcript and Merkle commitment

The specifications are `Keccak.Transcript` (`Keccak/Transcript/Duplex.lean`): a sixteen-lane overwrite duplex absorbing tagged extension scalars and nonces, squeezing one extension element per permutation, seeding from two digests and grinding by a discarded squeeze; and `Keccak.Commit` (`Keccak/Commit`): binary Keccak-256 trees over leaf images of field words, pruned multi-openings, their masked extraction and node-level binding (`disagreement_bound`), and the random-oracle trace of commitment and challenge queries with its exception bound (`RandomOracleTrace.bad_probability_le`). `Correspondence` proves the transcript's framing and replay, and `Lanes` maps lanes to field words.

The fast implementations are CompStark's lane-level `Keccak.Duplex` and streaming `Keccak.Merkle`. `Keccak.TranscriptDuplex` (`Keccak/Transcript/Native.lean`) proves the writer equal to the specification: `absorb_spec`, `absorbAll_spec` and `sample_spec` at every item, including full-rate flushes, and `grind_refines` and `grind_min` for smallest-nonce grinding. `Keccak.MerkleLeaves.merkleRow_hash` identifies the streaming tree's leaf hash with the commitment's leaf digest.

`tests/CompStarkTests/KeccakTranscript.lean` checks 48 Rust vectors: seeds, squeezes across rate boundaries, repeated empty squeezes, digest absorption, grinding checks and pruned openings. `tests/CompStarkTests/KeccakTransport.lean` checks smallest-nonce grinding at 0, 5 and 9 bits and Merkle roots, rows and hints on field-word leaves.

## Polynomial commitment

`Pcs.BinaryDomain` fixes the basis `1, g, …, g^63` and the binary additive domain; `Pcs.AdditiveEncoding` proves ArkLib's `Whir.EncodingContract` for the novel-basis additive encoding over `K` and `E` for `vars + rate ≤ 64` (`encodingContract`, `extensionEncodingContract`), and `computableAdditiveNTT_eq_encode` its agreement with CompPoly's executable additive NTT below 64. `Pcs.Prover.Encoding.encode` runs the native bit-plane encoder on extension rows.

Ring switching (`Pcs.RingSwitch.Protocol`) reduces 64 bit-slice claims at an extension point to one weighted claim on the base-field stack through six Frobenius maps, with its knowledge certificate, local bounds and terminal identity (`terminal_iff`); `Pcs.RingSwitch.Prover` computes the honest slices and target. `Pcs.Honest.prove` commits a base-field table and opens it with ArkLib's WHIR against explicit verifier coins, and `proveRing` batches the ring-switched claim into the same opening; `prove_accepts` and `proveRing_accepts` prove completeness for every schedule and every true claim. `Pcs.Verifier` gives cached refinements of WHIR's inner products, evaluations and acceptance.

The extractor decodes with CompPoly's Guruswami–Sudan decoder at exact integer Johnson cutoffs: `Pcs.Radius` computes the cutoff (`agreementCutoff_le_iff`), `Pcs.Parameters` selects multiplicities, and `Pcs.Decoder.gsListDecoder_correct` proves the interleaved list decoder correct with the real Johnson list bound. `Pcs.Extraction` and `Pcs.ExtractorCache` prove the cached extractor equal to ArkLib's WHIR extractor at every level (`openingExtractorCached_eq`, `levelExtractorCached_eq`).

`Pcs.Errors` lists WHIR's error per verifier message. `Pcs.Levels` reads a schedule's levels as natural numbers and decides rational bounds on every row in the kernel: `whirErrorRows_le` turns `levelsCheck κ κq` into `2^-κ` on every algebraic row and `2^-κq` on every column-query row, for any schedule, rate and dimension, the Johnson radius and MCA slack measured at the reduced rate. `Pcs.Schedule` is leanMultisig's ladder (initial fold 6, then 4, rate exponents `r, r + 3, …`, its query table and grinding), and `Pcs.ProductionLevels.productionLevels_check` certifies all 56 of its configurations at `2^-128` algebraic and `2^-111` per column query, `2^-128` after 17 bits of query grinding.

`tests/CompStarkTests/BinaryPcs.lean` checks cube indexing, the Johnson cutoffs and basis conversion. `tests/CompStarkTests/BinaryPcsNative.lean` checks that the honest opening is accepted and an inconsistent claim rejected, and compares the native extension encoding (98,304 bytes) and the six-map ring-switching target with Rust.

## Keccak-f GKR

`Keccak.Gkr` is a public-coin reduction from claims on the outputs of `2^(p+4)` Keccak-f permutations to claims on their inputs and committed middle states: twelve layers per segment of two twelve-round segments, the nonlinear layer through the sixteen-coordinate reverse multiplication-friendly embedding of `Keccak.Embedding` (injectivity and the CRT correspondence kernel-checked), pack and position sumchecks and the linear layer by its transpose. `Gkr.soundness` bounds acceptance for a wrong input table by `(37 (p + 4) + 902) / |E|` over any characteristic-two field `E`; `Gkr.certificate` is its knowledge certificate on ArkLib's interaction layer.

`Keccak.GkrProver.prove` is the word-level prover. `specificationTranscript_complete` proves the specification prover accepted for every challenge sequence; `prove_eq_specificationTranscript` and `prove_buildWitness_eq_specificationTranscript` prove the fast prover equal to it, and `prove_complete` and `prove_buildWitness_complete` transfer completeness. `tests/CompStarkTests/KeccakGkr.lean` compares every witness layer, transmitted scalar, challenge, batch claim and opening with Rust on 512 permutations, and the `keccak-gkr` performance-gate workload counts the reduction.

## Multilinear algebra and composition

`Multilinear.Basic` defines low-bit-first multilinear extensions over `E` with their word-level evaluators; `Multilinear.Algebra` holds their linearity and interpolation, stacking, fingerprints, product trees and fixed-polynomial sumcheck bounds. `Multilinear.Retained` gives identity backward maps on concrete transcript trees. `Compose.ListLift` lifts a family of knowledge certificates over a candidate list fixed before any challenge, multiplying each error by the real list bound, and `Compose.Reduction` composes such reductions sequentially and appends an opening.
