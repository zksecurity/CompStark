import Lake

open System Lake DSL

package CompStark where
  version := v!"0.1.0"
  testDriver := "CompStarkNativeTests"

-- Pinned to a CompPoly commit with the packed NTT, the batched coset LDE on chunks of rows with
-- input transposes by column range, coset interpolation generic over 32-bit Montgomery fields,
-- fast KoalaBear⁵ and spec fields over the fast base field, and word-sized packed loads and stores.
require CompPoly from git "https://github.com/mitschabaude-bot/CompPoly.git" @
    "6de4e90026a12ea10a2a24f53f332aed3e877961"

-- ArkLib main with Johnson-regime mutual correlated agreement for power curves, lossy mutual
-- correlated agreement, FRI on the interaction layer with its knowledge certificate on Plonky3's
-- commit-phase tree, state restoration over public-coin protocols with grinding draws, and
-- Fiat–Shamir on a duplex challenger with challenges of several squeezes, its draws bounded
-- against the certificate's challenge laws, the BCS compiler: Merkle commitments in place of
-- oracle messages, correlated agreement and lossy MCA for Reed–Solomon curves in the
-- unique-decoding range, and the fold lists of Plonky3's schedule, against VCVio with Merkle trees
-- of injected payloads (branch `compstark` of the bot fork).
require Arklib from git "https://github.com/mitschabaude-bot/ArkLib.git" @
    "6bb602c24b595b1b5e53dd00ca63f8a11eba28a4"

-- VCVio with Merkle trees of injected payloads, caps and pruned multi-openings (branch
-- `merkle-mixed` of the bot fork).
require VCVio from git "https://github.com/mitschabaude-bot/VCVio.git" @
    "d8cfe466f594510465d56e06f65075861e32fedc"

-- Mathlib as CompPoly pins it, last so that its dependencies take precedence over ArkLib's.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib CompStark where
  platformIndependent := true

/-- CPU-targeted packed kernels; the proof artifacts remain platform independent. -/
lean_lib CompStarkPackedNative where
  roots := #[`CompStark.Poseidon2.Packed, `CompStark.Poseidon2.Packed24,
    `CompStark.Merkle.Packed, `CompStark.Merkle.PackedColumns, `CompStark.Stark.Words,
    `CompStark.Stark.ExtWords,
    `CompStark.Stark.ProgWords, `CompStark.Stark.ProgGroup, `CompStark.Stark.Fast,
    `CompStark.KoalaBear.Fast, `CompStark.KoalaBear.Group, `CompStark.BabyBear.Fast]
  platformIndependent := true
  moreLeancArgs := #["-march=native", "-mstackrealign"]

lean_lib CompStarkTests where
  srcDir := "tests"

/-- AIRs and constants of the tests and benchmarks that are not part of the library, such as
Plonky3's Keccak AIR and its quotient kernel. -/
lean_lib CompStarkFixtures where
  srcDir := "fixtures"
  moreLeancArgs := #["-march=native"]

/-- The test driver: builds the `#guard` library `CompStarkTests`, which it imports, and runs the
known-answer checks on the packed kernels compiled. -/
lean_exe CompStarkNativeTests where
  srcDir := "tests"
  moreLeancArgs := #["-march=native"]

lean_exe CompStarkBench where
  srcDir := "bench"
  moreLeancArgs := #["-march=native"]
