# Keccak kernel measurements

The single-thread user-instruction comparison uses CompStark main `8772ae76` and unchanged leanMultisig revision `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`, built with `target-cpu=native`. The Ryzen 7 3700X host selects Rust's scalar single-state permutation and AVX2 batched hashing and nonce probes. The additional scalar reference uses the portable `u64` implementation from the same revision. FIFO phase markers acknowledge hardware-counter boundaries; allocation and result materialization belong to the measured operation. Wall times require the shared `/tmp/compstark-bench.lock`.

| Kernel | Main instructions/op | Rust native instructions/op | Main/native |
| --- | ---: | ---: | ---: |
| Keccak-f1600, dependent chain | 7,742 | 4,709 | 1.64× |
| Eight-bit grinding, 74 probes and success binding | 1,070,464 | 357,761 | 2.99× |

Rust's portable scalar permutation takes 4,723 instructions/op, so main/scalar is 1.64×. Each permutation-chain measurement executes 10,000 permutations and checks lane zero against `0x03d0008026579d6c`. The grinding fixture chooses nonce 73 on both implementations.

| Phase | Main instructions | Rust native instructions | Main/native |
| --- | ---: | ---: | ---: |
| Merkle commit, 4096 × 64 words | 134,280,422 | 32,077,388 | 4.19× |
| Merkle open, 100 queries | 9,331,792 | 12,467,628 | 0.75× |
| Duplex, 10,000 writes and samples | 137,602,649 | 47,820,308 | 2.88× |
| Eight-bit grind | 1,070,468 | 357,761 | 2.99× |

The main column uses committed performance-gate baselines for the phases, which include generated leaf batching. The permutation loop's generated C contains no lane boxing or allocation between rounds. Arrays at its input and output box their lanes. The packed-load sponge already retains scalar state across absorption, whereas leanvm main `14805db` uses array-based absorption for its public program-image hash.

## Prepared grinding and unboxed counters

The fast permutation retains its scalar state and uses `UInt32` round counters. `f1600_word_code` proves equality to the existing permutation. `f1600FirstOverwrite_eq` certifies a lane-zero-only result with a scalar nonce overwrite; its rounds allocate neither arrays nor boxed lanes. `grindNonce_eq` proves the entire prepared search equal to `grind`, including the accepted state and every observer event. `findNonceParallel_eq` proves ordered sixteen-way waves of 512-candidate chunks return the sequential search's smallest nonce. Searches below thirteen work bits run sequentially.

| Kernel or phase | Main instructions | Prepared instructions | Native Rust instructions | Prepared/main | Prepared/Rust |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10,000 dependent permutations | 77,421,611 | 75,891,615 | 47,560,929 | 0.980× | 1.60× |
| Merkle commit, 4096 × 64 words | 134,280,222 | 134,285,248 | 32,077,388 | 1.000× | 4.19× |
| Generated Merkle commit | 132,084,961 | 132,085,358 | 32,077,388 | 1.000× | 4.12× |
| Merkle open, 100 queries | 9,331,792 | 9,337,689 | 12,474,242 | 1.001× | 0.75× |
| 10,000 writes and samples | 137,593,270 | 136,068,915 | 47,820,308 | 0.989× | 2.85× |
| Eight-bit grind, 74 probes | 1,070,466 | 545,590 | 357,761 | 0.510× | 1.53× |

The dependent permutation costs 7,589.2 instructions including its array boundary, versus 4,756.1 for native Rust and 4,723 for the pinned portable Rust scalar. The 1.5× scalar target remains unmet. The eight-bit prepared fixture uses 7,372.8 instructions per probe including success binding, versus 4,834.6 for Rust.

At twenty work bits both implementations choose nonce 124138 and next challenge `[5366933390071687144, 3650987668691482591, 2331228947711704332]`. The recorded Lean search uses 973,110,720 instructions. The [audited full-native Rust search](keccak-reference-audit.json), explicitly one worker with native Cargo dependencies, uses a three-run median of 197,268,886: 7,838.9 versus 1,589.1 instructions per candidate, a **4.93×** ratio. This retains the recorded Lean count and remeasures the native Rust denominator. Lean's ordered chunks also execute candidates later in their final wave; those instructions are included. `CompStarkBench gate keccak-grind DIR` and the Rust harness's matching gate measure this workload without adding it to the recurring gate.

| Twenty-bit search | One worker | Sixteen workers | Speedup |
| --- | ---: | ---: | ---: |
| Lean | 13.167 s | 4.497 s | 2.93× |
| Rust, archived build | 1.384 s | 1.244 s | 1.11× |

These single observations took the shared benchmark lock with host load averages between 116 and 128 on sixteen CPUs. They demonstrate deterministic parallel execution; they do not estimate quiet-host latency. `LEAN_NUM_THREADS` and `LEANVM_NUM_THREADS` select the worker counts. The Rust harness links the unchanged pinned production crates built with `target-cpu=native`; the temporary reference checkout stays read-only. Rust fixtures match at both one and sixteen workers, and the compiled Lean conformance suite checks their exact transcript outputs.

## Native reference and thread accounting

The [LeanVM counter audit](https://github.com/zksecurity/leanvm-security/blob/perf-rounds-2/docs/prover-counter-audit.md) records three complete SET/Fibonacci repetitions with inherited process counters and independent counters on every live TID. Complete Rust PCS includes grinding; no worker instructions are missing. The pinned Rust code uses its own `parallel` pool, with the caller as worker zero and no background workers at `LEANVM_NUM_THREADS=1`. It does not use Rayon for these kernels.

The standalone builder enforces `RUSTFLAGS=-C target-cpu=native` for Cargo dependencies as well as the wrapper. The component benchmark enforces one Rust worker for its wall and hardware-count passes and records executable hashes. The [raw audit](keccak-reference-audit.json) retains the pinned source, compiler, dependency manifest, observed backend width and three repetitions per build. It measures 805.814M instructions with portable dependencies and a native wrapper, versus 197.269M with fully native dependencies; their hash backends have one and four lanes respectively.

The archived twenty-bit Rust count of 771.278M and its 1.26× ratio lack a binary hash and enforced dependency-flag/worker environment. They cannot establish a single-worker full-native comparison. The portable rebuild does not reproduce that exact archived value, so the evidence does not identify its exact build and execution configuration. The builder's dependency flags and the benchmark's instruction-pass worker count both depended on the ambient environment. The complete-proof Rust denominators and the standalone scalar, Merkle, duplex and eight-bit instruction denominators agree with the audited native measurements. The sixteen-worker wall observations above are historical loaded-host observations whose native dependency configuration is not independently fingerprinted.
