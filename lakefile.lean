import Lake

open System Lake DSL

package CompStark where
  version := v!"0.1.0"
  testDriver := "CompStarkTests"

-- Pinned to a CompPoly commit with the packed NTT and the batched coset LDE.
require CompPoly from git "https://github.com/mitschabaude-bot/CompPoly.git" @ "3e09608ea702552a3e3f466926c4607ea959190c"

-- ArkLib with its Poseidon2 round-constant fix (Verified-zkEVM/ArkLib#1316), for the equivalence
-- of our Poseidon2 with ArkLib's.
require Arklib from git "https://github.com/Verified-zkEVM/ArkLib" @ "2817d8c7d2f28d706b17f8de0f885880d0b2eb13"

-- VCVio on Lean v4.35, Verified-zkEVM/VCVio#866, ahead of ArkLib's v4.34 pin.
require VCVio from git "https://github.com/Verified-zkEVM/VCVio" @ "cf8cf2564ff1a05ca5023fb742ca5e0195cd41ad"

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
