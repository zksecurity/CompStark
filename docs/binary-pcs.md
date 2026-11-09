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

`CompStark.Pcs.Induction` scatters ordered queries, adds duplicate positions, runs the additive transform in transposed stage order, and sums the encoder's replicas. `induceRows_adjoint` proves the complete output has exactly the dense encoded-query pairing for every message. The sparse sweep skips zero pairs; `induceDenseRows_eq` proves the unconditional dense sweep gives the same output. Both kernels reuse the encoder's prepared twiddles. The complete-domain sweeps provide the coordinate specification for the occupied window and strip implementation.

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

`liftPointBinary` reconstructs compact point-window columns and binary coordinate columns with one shared binary map. Its compiler refinement prepares the 256 images at each of the 24 physical byte positions, then reads 24 images per output element. `coordinateByte_bit`, `applyCoordinateBytes_eq`, and `liftPointBinary_eq` identify every selected bit, prepared image, and complete output with `liftColumns`. The `pcs/basis-lift` gate includes preparation and reconstructs 4,096 outputs from eight point windows and 192 coordinate columns; `pcs/basis-lift-reference` counts the complete reference on the same inputs and checks equality outside both regions.

The three-run medians are 69,446,904 instructions for byte-prepared reconstruction, including its tables, and 441,759,604 for the complete reference: 6.36× fewer instructions. These are Lean-to-Lean kernel counts. The production initial-lane span includes the reconstruction as well as the six sumcheck rounds.


## Query-local sparse induction

`induceOccupiedCompactRows` prepares twiddles only for occupied blocks at each transpose stage. It retains the compact normalized subspace row while preparing that stage, caches one certified multiplier per occupied block, traverses its columns in an inner loop with a fixed base address, and releases the stage before advancing. `occupiedStageCompact_eq` and `occupiedRunCompact_eq` identify the complete buffers with every certified full-domain plan; `induceOccupiedCompactRows_refines` transfers the encoder-transpose coordinate theorem. The `pcs/induction-large-compact` gate includes all query-local preparation and compares every output byte with the unchanged Rust sparse/dense fixture. Shape regressions include empty queries, zero lanes, duplicate positions and all three extension limbs.


`foldPairChallenge` shares one prepared challenge across witness and weight above 256 output elements; shorter rounds interpolate with direct scalar products. `foldScalar_eq` and `foldPairChallenge_eq` prove complete vector equality with the prepared restriction. The PCS gate compares direct, prepared and selected folds at 16, 256 and 1,024 outputs, including preparation inside the counters; the native shape regressions cover both sides of the selection boundary, blocked rows and empty dimensions.

`CompactRows` retains normalized subspace rows and three 256-entry byte subset-sum tables per row. `TwiddleRow.lookup_eq` covers both the three-load path below 24 block bits and the direct subset sum above that range. `subsetTable_eq` certifies the shared-prefix table constructor. `occupiedStageRows_eq`, `occupiedRunRows_eq`, and `induceOccupiedByteRows_refines` identify the resulting stages and induction coordinates with the certified transform. The gate measures row preparation separately from the occupied transform, and compares the complete packed output with the Rust fixture.

## Window and strip induction storage

`induceSparseStripRows` retains only occupied 1,024-element low windows and processes the continuation in 16-column strips. `windowSparseRun_read` and `stripRun_read` identify each local stage with its complete-domain projection; `tiledInduceCore_refines` and `induceWindowStripRows_refines` identify the kept output with the certified encoder transpose, including repeated positions. `occupiedWindows_code` shares occupied-block discovery across windows, and `tiledInduceSparse_eq` shares an occupied high-stage block and multiplier plan across strips. `subsetTable_code` builds each byte table by appending its upper half with one retained row entry. The `pcs/induction-large-tiled` phase includes row preparation, window scattering, both transpose passes, replica collapse and output materialization, and checks every output byte against the unchanged Rust fixture.

The 12-bit, 137-query, three-limb fixture measures full-domain compact storage, compact byte rows and occupied window/strip storage separately, including preparation and complete comparison with Rust. Their instruction medians are retained in `bench/perf-baseline.json` under `pcs/induction-large-compact`, `pcs/induction-large-byte-rows` and `pcs/induction-large-tiled`. Production opener fixtures also include their actual query occupancy and replica-collapse costs.

## Shared byte-fold tensor projections

`Pcs.BitFold` prepares the 256 subset sums of each group of eight extension weights, transposes padded 64-word witness blocks, and folds all 64 physical bit rows through those tables. `foldBytePlan_eq` proves equality with `foldBits`, including partial and empty blocks. `dotBytePlan_refines` reconstructs the mixed base/extension inner product; its native reconstruction uses three polynomial shift/XOR accumulators. `transposeFoldBits` identifies the rectangular transpose of those rows with all 192 separate binary-coordinate projections.

`Pcs.Projected` retains byte-fold plans in explicit `WindowProjection` records shared across witness lanes. `projectPointBinary_eq` proves the joint point/ring result equals `projectColumns`. Equal occupied windows share a projection cache. Point coefficients and binary-coordinate maps are prepared once for final lifting.

`Pcs.TensorProjection` projects shared low windows across high blocks and contracts their claim-specific high coefficients. `projectTensorPointBinary_eq` and `liftTensorPointBinary_eq` prove exact agreement with the complete compact columns whenever each column factors into the supplied low window and high coefficients. The lift first groups equal low patterns, sums their high-block coefficients, and scales each retained low pattern once. Tensor dimensions are arbitrary, including empty axes; the production caller chooses the low ten-bit split and proves its physical point selectors factor at that boundary.

The instruction gate includes `pcs/basis-byte-columns`, `pcs/basis-tensor-columns` and `pcs/basis-tensor-lift`. Complete reference results are compared outside their measured regions. Compiled regression tests cover partial 64-word blocks, duplicate and empty point patterns, zero high coefficients, empty tensor axes, and equality of every projected and lifted coordinate. These are component measurements; production Basis and initial-lane ratios are measured by the LeanVM opener. The gate also includes `pcs/basis-window-ring` and `pcs/basis-packed-dot`, with table preparation inside their counters.

`Pcs.TensorProjectionActive` retains numeric representatives for equal low windows. Projection caches only the high blocks where a claim in that pattern has a nonzero coefficient. Reconstruction contracts claim coefficients by those numeric keys, scales each occupied low window once per high block, and reads individual compact-window values through `BasisColumn.valueAt`. The compiler refinements preserve every projected term and reconstructed coordinate.

`Pcs.ByteFoldRows` groups eight byte-table lookups for each transposed scalar plane and accumulates their three coordinates directly. `foldBitTablesArray_code` and `foldBytePlan_code` certify the grouped loop and its arbitrary-length wrapper. `Pcs.MixedDot` stores eight extension weights in Rust's paired first/second-limb layout with consecutive third limbs, and accumulates six unreduced polynomial words before reducing the three output coordinates; `dotMixedPlan_refines` covers all input lengths and the zero-padded final group. The mixed-dot kernels use CompPoly’s inline carry-less primitive, retain unreduced products through accumulation, and reduce each output coordinate once. Shared sumcheck challenges compile to direct scalar multiplication with mixed products for base-field inputs.

`Pcs.TensorProjectionPacked` applies retained mixed weights to occupied point blocks. `Pcs.WindowBitFold` prepares ring byte tables only for the certified occupied interval, and `windowBits_eq` identifies its result with the complete zero-extended fold. `Pcs.WindowScatter` reconstructs point contributions by adding each retained coefficient directly to its physical coordinate. Its prefix and complete-window invariants prove that each occupied coefficient contributes exactly once.

The [CLMUL shared-kernel measurements](clmul-kernels.md) record the native primitive pin, certified compiled paths and the instruction-gate reductions for folds, packed dots and Basis lifting.


## Fused tensor survivors and messages

`Pcs.FusedTensor` retains each low pattern, its contracted high-block coefficients, the nonzero pattern indices for each block, and the shared coordinate-byte map. `TensorLiftPlan.pointAt_refines` proves that deferred reconstruction over live patterns equals the complete point sum, and `prepareTensorLift_weightAt` identifies each combined point/ring coordinate with `liftTensorPointBinary`. Filtering consumes materialized coefficient rows through `liveTensorPatterns`.

`Pcs.FusedPairs` materializes the restricted witness and reconstructed weight together, retaining twelve scalar unreduced message words in its adjacent-pair loop. `materializePairs_table`, `materializePairs_weights` and `materializePairs_message` identify both survivor arrays and the complete residual quadratic with the reference round. `materializeTensorPairs` takes the physical witness stride as a materialized argument, so the contraction loop reuses that stride for every lane product. The `pcs/basis-tensor-prepare` and `pcs/basis-fused-survivors` gate phases include plan preparation and fused construction, with complete weight and message comparisons outside their counters.

`dotExtWide_refines` proves that extension dots reduce once after accumulating every product. `roundCoefficientsDirect_code` uses that implementation for both quadratic message coefficients at arbitrary row and block widths. The PCS axiom audit covers these declarations together with the survivor and tensor refinements.

## Scalar projection and factored ring rows

`Pcs.TensorProjectionPacked.windowDot` reads a contiguous occupied witness interval through proved `uget` indices and retains six unreduced `UInt64` accumulators. `tensorWindowMatrixScalar` shares active low-pattern results across point claims and defers the high-block dot's polynomial reduction to its output. Its compiler refinement preserves every packed projection coordinate.

`Pcs.TensorRing` shares one low-window subset-sum plan across lanes and high blocks. Each occupied block is bit-transposed and folded through those tables; the high factors are contracted with deferred extension products before the 64 extension rows are transposed into 192 binary columns. `projectTensorFactoredRing_eq` identifies the complete result with the point/binary projection for any certified low/high factorization. `WindowFold` transposes occupied physical intervals directly without allocating an intermediate word vector; incomplete final blocks are zero-padded. Complete transposition blocks retain their source buffer through `bitFoldPadShared`.

`roundCoefficientsWith` visits each blocked pair once, reads both endpoints from retained getters, and accumulates both quadratic-message coefficients in twelve scalar words. Its refinement identifies both outputs with the complete two-pass message. The instruction gate measures scalar mixed dots, factored ring projection and direct blocked messages separately; native tests cover empty dimensions and partial low blocks.

## Contiguous scalar encoding and generated Merkle rows

`encodeExtensionRowsScalar` transforms the physical cubic-extension limbs directly with CompPoly's scalar CLMUL encoder. `encodeExtensionRows_code` proves complete buffer equality with the certified padded encoder, including zero lanes. The compiled path replicates the row-major message with machine addresses and retains its exact physical width throughout the transform.

`Keccak.Merkle.commitOfFn` consumes generated rows without an intermediate row array. Its refinement preserves the complete private tree, including all payloads and cached digests. Leaf generation and hashing run in contiguous batches of at most 1,024 rows, split into parallel tasks; the binary-carry merge retains input order. `Builder.absorb_code` and `Builder.absorbOfFn_code` prove equality with the scalar streaming builder for arbitrary row counts.

## Native occupied induction and scalar survivor messages

`CompactInduction.scalarBlockSweepMachine` retains the byte-array state throughout each occupied block, hoists its native base and span, and uses bounded word loads and stores. `scalarBlockSweep_code` proves equality with the generic byte-addressed sweep. `collapseRowsNative` uses the same approved packed accessors for replica collapse; `collapseRows_code` proves complete output equality. `inductionMultiplier_code` and `occupiedSweepRowsNative_code` select scalar CLMUL instead of preparing byte tables for these short butterflies. The generated butterfly loop has no boxed words, constructors or indirect calls, and two natural-number sites for its index and bound.

`FusedTensor.patternCoefficientsScatter` groups each point contribution by its retained low-pattern key in one pass. `patternCoefficients_code` proves equality with all filtered coefficient sums, including duplicated keys. `FusedRound.foldMessageSurvivors` folds both endpoint getters and authors their quadratic message through the existing twelve scalar survivor accumulators. `foldMessageNative_code` identifies both complete arrays and the message with the certified reference.
