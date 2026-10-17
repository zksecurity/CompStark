import Lake

open System Lake DSL

package CompStark where
  version := v!"0.1.0"
  testDriver := "CompStarkTests"

-- Pinned to a CompPoly commit with the packed NTT and the batched coset LDE.
require CompPoly from git "https://github.com/mitschabaude-bot/CompPoly.git" @ "3e09608ea702552a3e3f466926c4607ea959190c"

@[default_target]
lean_lib CompStark where
  platformIndependent := true

/-- CPU-targeted packed kernels; the proof artifacts remain platform independent. -/
lean_lib CompStarkPackedNative where
  roots := #[`CompStark.Poseidon2.Packed]
  platformIndependent := true
  moreLeancArgs := #["-march=native", "-mstackrealign"]

lean_lib CompStarkTests where
  srcDir := "tests"

lean_exe CompStarkBench where
  srcDir := "bench"
  moreLeancArgs := #["-march=native"]
