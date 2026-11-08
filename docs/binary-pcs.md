# Binary-field PCS prover components

`CompStark.Pcs.RingSwitch` applies ordered two-term Frobenius maps on the three-word cubic extension and proves equality with their specification composition. `binary64Stages` uses shifts 32, 16, 8, 4, 2, 1. `coordinateWeights` evaluates the shared map on all 192 binary basis vectors in constant, linear, quadratic limb order. `powersFrom` produces consecutive powers by multiplication; its append theorem identifies the disjoint ring and point claim ranges of one batching challenge.

`CompStark.Pcs.Tensor` stores low and high equality factors on the executable word field. A split into `lo` and `hi` coordinates stores `2^lo + 2^hi` field elements and reconstructs one entry with one product. `wordFactoredEq_eval` proves agreement with ArkLib’s full equality tensor. `foldBits` computes all 64 Boolean slice inner products of packed base-field words and proves their weighted-sum interpretation.

`CompStark.Pcs.HonestRound` computes the constant and quadratic coefficients of a product of affine slices over any commutative ring. `honestRound_eval` proves that reconstruction at the running claim equals the next restricted inner product. `honestRounds` constructs a block of actual compressed protocol messages; `read_honestRounds` proves the verifier reads the restricted inner product, the exact supplied challenges, successful checks, and the intended continuation.

`CompStark.Pcs.HonestWhir` constructs a complete ArkLib WHIR opening from a table, weighted claims and explicit verifier coins. The transcript includes each complete extension-field encoded word, its OOD answer, ordered query claims and terminal plaintext. Residual, OOD and query claims use ArkLib’s ordering. `honestWhir_accepts` proves completeness for all true input claims, schedules and verifier coins, including empty coordinate blocks and repeated queries. Merkle transport, grinding, Fiat–Shamir sampling, optimized encodings and production-specific lookahead messages are responsibilities of the caller.

`tests/CompStarkTests/Pcs.lean` checks honest openings over an odd-characteristic ring, an empty terminal schedule, shared power ordering, split tensor boundaries, and exact Rust bytes for 192 coordinate weights, 256 tensor entries, 64 slice folds and 256 mapped weights. The Rust driver uses unchanged leanMultisig arithmetic at `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`. To regenerate these fixtures, run `scripts/pcs-reference /path/to/leanMultisig /tmp/pcs-reference-target`, then `/tmp/pcs-reference-target/release/pcs-reference fixture tests/data/pcs`. The driver checks the pinned revision and rejects tracked source modifications.

`CompStarkBench pcs` verifies the same Rust bytes. `scripts/perf-gate` measures its coordinate-map, bit-fold and basis phases with single-thread user instruction counters. The reference driver accepts `gate pcs DIRECTORY` with the same counter-mark FIFO protocol, so Rust arithmetic and Lean kernels can be measured on identical inputs.

## Kernel measurements

Run `scripts/bench-pcs /path/to/leanMultisig` to rebuild the unchanged Rust dependency, compare all binary fixtures with one and sixteen Rust threads, and record interleaved instruction and loaded-host wall measurements in `bench/pcs.json`. Counters exclude process startup; direct phase clocks exclude the FIFO handshake. Each wall run holds `/tmp/compstark-bench.lock`. The fixed workload has 192 coordinates, 256 packed words, 64 slice outputs and 256 mapped weights. Each process starts cold; preparation for a shared tensor occurs before the bit-fold and basis phase.

| Kernel | Lean instructions | Rust instructions | Lean/Rust |
| --- | ---: | ---: | ---: |
| Six-map coordinate preparation | 6,514,141 | 759,411 | 8.58× |
| Packed bit folds | 321,240 | 83,569 | 3.84× |
| Mapped tensor entries | 1,974,207 | 271,470 | 7.27× |

These are three-run median user instruction counts on AMD Ryzen 7 3700X, Lean 4.35.0, with Rust built using `-C target-cpu=native`. The recorded load averages are in `bench/pcs.json`. The Rust mapped-weight comparison is a scalar coordinate-XOR reference using the public coordinate weights; it does not measure the production prepared bit-fold `Basis` span. The Lean bit fold uses descending numeric cursors and three scalar XOR accumulators; each visited bit uses a proved machine shift/mask test.

The PCS workload baseline adds three entries. Updating CompPoly, ArkLib and VCVio to the pins consumed by LeanVM also improves the existing sumcheck prepare and packed-fold workloads; those two baselines are measured afresh across three runs. Other baseline entries are retained.

| Loaded-host phase clock (median µs) | Lean, 1 thread | Rust, 1 thread | Lean, 16 threads | Rust, 16 threads |
| --- | ---: | ---: | ---: | ---: |
| Coordinates | 715.00 | 2,953.95 | 501.95 | 2,596.09 |
| Bit folds | 48.51 | 15.24 | 38.56 | 3,478.49 |
| Mapped tensor entries | 877.30 | 44.33 | 671.02 | 33.91 |

Load averages were 11.29 / 13.03 / 16.88 during these runs. Peak process RSS was 90,700 KiB for Lean and 2,304 KiB for Rust, including runtime/module startup. The Lean kernels themselves execute sequentially at both thread settings. Rust’s cold coordinate preparation and first parallel bit-fold include their library initialization costs; these tiny loaded-host timings are diagnostic, not release-speed or end-to-end PCS measurements. Production `PCS open`, `Ring switch`, `Basis` and WHIR subphase timings require the complete native wire driver.

## Native extension encoding

`CompStark.Pcs.Encoding.encodeExtensionRows` encodes consecutive constant, linear and quadratic extension limbs using CompPoly’s native bit-plane additive NTT. Rows contain at most 21 extension lanes; padding to 64 base-field lanes and compaction preserve each retained coordinate. `encodeExtensionRows_refines` identifies every output extension lane with the generic additive encoder. The plan is reusable across messages with the same domain dimension.

The Rust fixture contains all 98,304 bytes of a six-variable message encoded at rate exponent two with 16 extension lanes. Both one-thread and sixteen-thread Rust runs produce the same bytes. The performance gate counts plan preparation separately from encoding. For this small shape, median Lean/Rust user instructions are 2,228,467 / 94,820 for plan preparation and 35,153,729 / 397,035 for encoding. These measurements include padding, bit-plane conversion and compaction; they do not establish production-size performance. Full phase counters and load averages are recorded in `bench/pcs.json`.

## Shared coordinate application

`CompStark.Pcs.CoordinateMap.applyCoordinates` applies the 192 shared binary coordinate images with a descending numeric cursor and three machine-word XOR accumulators. `coordinateExpansion` proves the exact limb-and-bit decomposition of every extension word; `applyCoordinates_refines` proves equality with the complete six-stage Frobenius composition for arbitrary challenges and inputs. The preparation is shared with the ring-switch coordinate weights.

For the fixed 256-entry mapped tensor, the three-run median is 1,974,207 Lean instructions versus 271,463 Rust instructions, a 7.27× ratio. This is a 4.39× reduction in Lean instructions relative to applying the Frobenius composition separately at every entry. The gate records the intended decrease in `pcs/basis`; all other phase baselines remain fixed.

## Query induction and accumulated weights

`CompStark.Pcs.Induction` scatters ordered queries, adds duplicate positions, runs the additive transform in transposed stage order, and sums the encoder's replicas. `induceRows_adjoint` proves the complete output has exactly the dense encoded-query pairing for every message. The sparse sweep skips zero pairs; `induceDenseRows_eq` proves the unconditional dense sweep gives the same output. Both kernels reuse the encoder's prepared twiddles. They sweep the complete domain; they do not implement the Rust window/strip decomposition or its split-tensor dense dot kernel.

The induction fixture has six message variables, inverse-rate exponent two, three physical extension limbs and seven ordered queries including a duplicate. All 64 induced extension values match both unchanged Rust production kernels and an independent impulse-encoder reference. The external harness copies the pinned PCS modules verbatim into a disposable crate and appends diagnostic children that expose private entry points; the original source remains clean.

`CompStark.Pcs.Accumulated.addScaled` prepares one extension multiplier outside the table update. `addScaled_refines` proves the exact pointwise accumulated linear combination. All 256 extension outputs match Rust's production `add_scaled`.

| Kernel | Lean instructions | Rust instructions | Lean/Rust |
| --- | ---: | ---: | ---: |
| Sparse induction | 1,870,570 | 32,264 | 57.98× |
| Dense induction | 2,223,074 | 27,875 | 79.75× |
| Shared accumulation preparation | 1,182,524 | — | — |
| Accumulation of 256 weights | 190,261 | 11,980 | 15.88× |

These three-run medians measure identical fixture inputs. Preparation is separate and must be amortized across a production table; the Rust update prepares no byte maps. `bench/pcs.json` records phase clocks, thread settings, load averages and peak RSS. The performance gate adds four entries without changing unrelated baselines. Production-size optimization and the full `PCS open` comparison require the integrated driver.

## Native quadratic messages

`Pcs.NativeRound.roundCoefficients` computes the constant and quadratic coefficients of a weighted pair interpolation, supporting adjacent pairs and blocked lane pairs. `roundCoefficients_constant` and `roundCoefficients_quadratic` prove the exact endpoint product sums over the extension field. All coefficients match Rust’s unchanged `round_msg_lsb` on the accumulated-weight fixture. The 256-entry phase uses 525293 Lean instructions against 18632 Rust instructions (three-run medians); the performance baseline adds only this phase.

## Projected lane Basis

`Pcs.Basis` represents a weight as a sum of lane coefficients times shared column factors. `basis_dot` replaces each full witness lane with its projections onto those factors. `basis_honestRound` proves that both compressed coefficients are contractions of the two small lane matrices; projection and weight factorization commute with lane restriction. `basis_mapped_product` decomposes a binary-linear ring map into its 192 shared coordinate columns.

`Pcs.NativeBasis` supplies row-major projection matrices, compressed messages, prepared lane folds and the final weight lift. `basisRound_projected` identifies the native message with the honest full-table quadratic. `Pcs.BasisWindow` retains only an occupied point interval, and `Pcs.BasisColumn` projects point windows and binary coordinates without expanding their complete column tables. `projectColumns_eq` proves equality with the full-kernel projection. These modules use the same kernel-only axiom audit as the other PCS components.

The conformance workload has 64 lanes, 64 base-field columns per lane and three independent full point claims. A diagnostic child of the unchanged Rust production `initial_basis` exposes its projection and lane-factor matrices; every byte matches Lean. Regression tests compare all six native projected rounds and the final lift against dense witness/weight restrictions, and cover empty windows, interior windows and the six boundary coordinates of the cubic binary representation.

The `pcs/basis-project` phase constructs the two matrices, including tensor preparation. The three-run medians are 93,833,312 Lean instructions and 310,217 Rust instructions (302.48×), with loaded-host phase clocks of 8.683 ms and 0.108 ms at load 7.61. This small full-point workload uses the cached equality-factor constructor; it does not measure a production combined PCS opening. The measured inputs, counters and clocks are in `bench/pcs.json`. The gate records this additional phase and retains all unrelated baselines.

## Shared production Basis columns

`BasisColumnPrepared` prepares each binary column's selected coordinates once, shares equal point windows across the lane matrix, and fixes each witness row offset before entering its projection loop. `projectColumns_code` proves word-for-word equality with `projectColumns`; the existing `projectColumns_eq` then identifies the result with the complete mathematical projection matrix. The PCS namespace axiom audit includes both refinements.

The `pcs/basis-columns` instruction gate projects eight lanes onto 192 binary columns and eight repeated point windows over 1,024 columns, and compares the complete output with `projectBasis` outside the counters. `lake exe basisProjectionBench` runs the corresponding production-sized 64-lane, 8,192-column kernel and checks its retained sink. A single-worker screening comparison on CPU 5 counted 4,069,084,186 instructions for shared preparation and projection versus 20,591,966,133 for direct projection, with the same sink `10364763122551214041`. The respective process times were 0.779 s and 1.828 s at load `6.16/5.60/6.35` to `6.15/5.61/6.35`; these are loaded-host diagnostics, not Rust ratios.

Binary projections retain their selected coordinates in contiguous arrays shared across witness lanes. `projectionXorArrayNative` uses machine-size addresses when the witness fits that address space, with `projectionXorArray_code` proving exact agreement with the total array definition. `BasisProjection.contiguous_projectFrom` identifies each retained factor and `projectColumnsContiguous_eq` identifies the complete projection matrix with the shared-window implementation. The `pcs/basis-columns` gate includes selection preparation and compares every output with `projectBasis`.
