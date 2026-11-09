# Keccak kernel measurements

The single-thread user-instruction comparison uses CompStark main `8772ae76` and unchanged leanMultisig revision `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`, built with `target-cpu=native`. The host selects Rust's AVX-512 single-state permutation. The additional scalar reference uses the portable `u64` implementation from the same revision. FIFO phase markers acknowledge hardware-counter boundaries; allocation and result materialization belong to the measured operation. Wall times require the shared `/tmp/compstark-bench.lock`.

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
