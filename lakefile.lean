import Lake

open System Lake DSL

package CompStark where
  version := v!"0.1.0"
  testDriver := "CompStarkTests"

-- Pinned to a CompPoly commit with the packed NTT and the batched coset LDE.
require CompPoly from git "https://github.com/mitschabaude-bot/CompPoly.git" @ "3e09608ea702552a3e3f466926c4607ea959190c"

-- ArkLib with FRI round-by-round soundness on Lean v4.35 (Verified-zkEVM/ArkLib#1317, stacked on
-- #992 and #1251) and lossy mutual correlated agreement (branch `fri-lossy`).
require Arklib from git "https://github.com/mitschabaude-bot/ArkLib.git" @ "03d276bab5e918542cfbeb0953884b1553f86d1e"

-- VCVio as ArkLib#1317 pins it: Verified-zkEVM/VCVio#821 on Lean v4.35.
require VCVio from git "https://github.com/Verified-zkEVM/VCVio" @ "0de3bf11c4acd77a5e750288049ad35e1a650bf9"

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
