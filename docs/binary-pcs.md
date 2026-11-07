# Binary-field PCS prover components

`CompStark.Pcs.RingSwitch` applies ordered two-term Frobenius maps on the three-word cubic extension and proves equality with their specification composition. `binary64Stages` uses shifts 32, 16, 8, 4, 2, 1. `coordinateWeights` evaluates the shared map on all 192 binary basis vectors in constant, linear, quadratic limb order. `powersFrom` produces consecutive powers by multiplication; its append theorem identifies the disjoint ring and point claim ranges of one batching challenge.

`CompStark.Pcs.Tensor` stores low and high equality factors on the executable word field. A split into `lo` and `hi` coordinates stores `2^lo + 2^hi` field elements and reconstructs one entry with one product. `wordFactoredEq_eval` proves agreement with ArkLib’s full equality tensor. `foldBits` computes all 64 Boolean slice inner products of packed base-field words and proves their weighted-sum interpretation.

`CompStark.Pcs.HonestRound` computes the constant and quadratic coefficients of a product of affine slices over any commutative ring. `honestRound_eval` proves that reconstruction at the running claim equals the next restricted inner product. `honestRounds` constructs a block of actual compressed protocol messages; `read_honestRounds` proves the verifier reads the restricted inner product, the exact supplied challenges, successful checks, and the intended continuation.

`CompStark.Pcs.HonestWhir` constructs a complete ArkLib WHIR opening from a table, weighted claims and explicit verifier coins. The transcript includes each complete extension-field encoded word, its OOD answer, ordered query claims and terminal plaintext. Residual, OOD and query claims use ArkLib’s ordering. `honestWhir_accepts` proves completeness for all true input claims, schedules and verifier coins, including empty coordinate blocks and repeated queries. Merkle transport, grinding, Fiat–Shamir sampling, optimized encodings and production-specific lookahead messages are responsibilities of the caller.

`tests/CompStarkTests/Pcs.lean` checks honest openings over an odd-characteristic ring, an empty terminal schedule, shared power ordering, split tensor boundaries, and exact Rust bytes for 192 coordinate weights, 256 tensor entries, 64 slice folds and 256 mapped weights. The Rust driver uses unchanged leanMultisig arithmetic at `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`. To regenerate these fixtures, run `scripts/pcs-reference /path/to/leanMultisig /tmp/pcs-reference-target`, then `/tmp/pcs-reference-target/release/pcs-reference fixture tests/data/pcs`. The driver checks the pinned revision and rejects tracked source modifications.

`CompStarkBench pcs` verifies the same Rust bytes. `scripts/perf-gate` measures its coordinate-map, bit-fold and basis phases with single-thread user instruction counters. The reference driver accepts `gate pcs DIRECTORY` with the same counter-mark FIFO protocol, so Rust arithmetic and Lean kernels can be measured on identical inputs.

## Kernel measurements

Run `scripts/bench-pcs /path/to/leanMultisig` to rebuild the unchanged Rust dependency, compare all five binary fixtures with one and sixteen Rust threads, and record interleaved instruction and loaded-host wall measurements in `bench/pcs.json`. Counters exclude process startup; direct phase clocks exclude the FIFO handshake. Each wall run holds `/tmp/compstark-bench.lock`. The fixed workload has 192 coordinates, 256 packed words, 64 slice outputs and 256 mapped weights. Each process starts cold; preparation for a shared tensor occurs before the bit-fold and basis phase.

| Kernel | Lean instructions | Rust instructions | Lean/Rust |
| --- | ---: | ---: | ---: |
| Six-map coordinate preparation | 6,514,141 | 759,411 | 8.58× |
| Packed bit folds | 321,240 | 83,569 | 3.84× |
| Mapped tensor entries | 8,661,401 | 271,463 | 31.91× |

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
