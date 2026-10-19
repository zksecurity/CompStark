import Lake

open System Lake DSL

package CompStark where
  version := v!"0.1.0"
  testDriver := "CompStarkTests"

-- Pinned to a CompPoly commit with the packed NTT and the batched coset LDE.
require CompPoly from git "https://github.com/mitschabaude-bot/CompPoly.git" @ "3e09608ea702552a3e3f466926c4607ea959190c"

-- Pinned to Verified-zkEVM/ArkLib#1316, the Poseidon2 round-constant fix, for the equivalence of
-- our Poseidon2 with ArkLib's.
require Arklib from git "https://github.com/mitschabaude-bot/ArkLib.git" @ "452a6c33d3f5e57c021eb594eb4ec74ed01ee16c"

-- VCVio at ArkLib's pin with the fixes for Lean v4.35's Mathlib that its Merkle trees need.
require VCVio from git "https://github.com/mitschabaude-bot/VCVio.git" @ "06ab47f2b261dd00d705cee535af33edf54bff11"

-- Mathlib as CompPoly pins it, last so that its dependencies take precedence over ArkLib's.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib CompStark where
  platformIndependent := true

/-- CPU-targeted packed kernels; the proof artifacts remain platform independent. -/
lean_lib CompStarkPackedNative where
  roots := #[`CompStark.Poseidon2.Packed, `CompStark.Poseidon2.Packed24,
    `CompStark.Merkle.Packed, `CompStark.Stark.Words, `CompStark.Stark.ExtWords,
    `CompStark.Stark.Fast]
  platformIndependent := true
  moreLeancArgs := #["-march=native", "-mstackrealign"]

lean_lib CompStarkTests where
  srcDir := "tests"

lean_exe CompStarkBench where
  srcDir := "bench"
  moreLeancArgs := #["-march=native"]
