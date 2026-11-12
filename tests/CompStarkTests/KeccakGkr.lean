/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.SharedTable

/-! Rust conformance of the Keccak-f GKR prover: every sliced witness layer, transmitted scalar, challenge, batch claim and terminal opening on the 512-permutation fixture in `tests/data/keccak-gkr/active`, from leanMultisig `9d8bce818aa7c7e18e67026e522a9b1539d0a57d` (leanvm-security's `tests/rust/generate-gkr.py`). -/

@[expose] public section
namespace CompStarkTests.KeccakGkr
open CompStark.Keccak.GkrProver

/-- Read canonical little-endian machine words. -/
def readWords (path : System.FilePath) : IO (Array UInt64) := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size % 8 == 0 do throw (IO.userError s!"unaligned word file: {path}")
  return Array.ofFn fun i : Fin (bytes.size/8) => Id.run do
    let mut word : UInt64 := 0
    for b in [:8] do word := word ||| (bytes[8*i.val+b]!.toUInt64 <<< (8*b).toUInt64)
    return word

/-- Parse canonical three-word extension values. -/
def readScalars (path : System.FilePath) : IO (Array W) := do
  let words ← readWords path
  unless words.size % 3 == 0 do throw (IO.userError s!"unaligned scalar file: {path}")
  return Array.ofFn fun i : Fin (words.size/3) =>
    ⟨⟨words[3*i.val]!⟩, ⟨words[3*i.val+1]!⟩, ⟨words[3*i.val+2]!⟩⟩

/-- Compare every word and identify the first unequal coordinate. -/
def compareWords (path : System.FilePath) (actual : Array UInt64) : IO Unit := do
  let expected ← readWords path
  unless actual.size == expected.size do
    throw (IO.userError s!"{path}: size {actual.size}, expected {expected.size}")
  for i in [:actual.size] do
    unless actual[i]! == expected[i]! do
      throw (IO.userError s!"{path}: word {i}: {actual[i]!}, expected {expected[i]!}")

/-- Compare extension values in constant, linear, quadratic limb order. -/
def compareScalars (path : System.FilePath) (actual : Array W) : IO Unit :=
  compareWords path (actual.flatMap fun a => #[a.c0.val, a.c1.val, a.c2.val])

/-- Serialize a sliced layer in the source's block, position, group order. -/
def rustLayer (w : SlicedWitness) (r : Nat) : Array UInt64 :=
  let groups := 2^w.nLog/64
  Array.ofFn fun i : Fin (1600*groups) =>
    let block := i.val/12800
    let j := i.val/8%1600
    let g := i.val%8
    (w.layers[r]!)[j*groups+8*block+g]!

/-- Construct and compare the full reduction, with arbitrary nonzero spare-slot riders. -/
def fixture (name : String) (mark : Phase → Bool → IO Unit) : IO Unit := do
  let dir : System.FilePath := s!"tests/data/keccak-gkr/{name}"
  let committed ← readWords (dir / "committed.bin")
  let n := committed.size/64
  let nLog := n.log2
  unless n ≥ 512 && 2^nLog == n do throw (IO.userError "invalid committed shape")
  let witness := buildWitness nLog committed
  for r in [:25] do compareWords (dir / s!"layer-{r}.bin") (rustLayer witness r)
  let writer := Writer.seed #[1,2,3,4] #[5,6,7,8]
  let (batchPoint, writer) := writer.sampleMany nLog
  compareScalars (dir / "instance.bin") batchPoint
  let output := outputWords witness.outputs n batchPoint |>.extract 0 25
  compareScalars (dir / "output.bin") output
  let writer := writer.writeAll output
  mark .total true
  let start ← IO.monoNanosNow
  let result ← proveM mark writer witness committed batchPoint output
  let retained ← IO.mkRef result
  let stop ← IO.monoNanosNow
  mark .total false
  let result ← retained.get
  unless result.layers.size == 12 do throw (IO.userError "invalid reduction layer count")
  for (layer, d) in result.layers.zipIdx do
    let eq := eqTable layer.positionPoint
    let beta2 := layer.beta*layer.beta
    let weights := transposeWeights (Array.ofFn fun j : Fin 1600 =>
      eq[j.val]!+layer.beta*eq[shift j.val 4]!+beta2*eq[shift j.val 3]!)
    let value := layer.evaluations[0]!+layer.beta*(layer.evaluations[1]!+layer.beta*layer.evaluations[2]!)
    compareScalars (dir / s!"claim-{d}.bin")
      (#[value]++instanceWeights layer.s++layer.packPoint++weights)
  let final := result.finalClaim
  compareScalars (dir / "claim-11.bin") (#[final.value]++final.mu++final.point++final.weights)
  compareScalars (dir / "stream.bin") result.writer.stream
  compareScalars (dir / "challenges.bin") result.writer.challenges
  compareScalars (dir / "word-point.bin") (batchPoint++result.openings.outputPoint)
  compareScalars (dir / "word-value.bin") #[result.openings.outputValue]
  let low := result.openings.inputPoint.extract 0 4
  let pack := result.finalClaim.point.extract 0 (nLog-4)
  let slot := result.openings.inputPoint.extract 4 10
  compareScalars (dir / "slice-point.bin") (low++pack++slot)
  compareScalars (dir / "slices.bin") result.openings.slices
  IO.println s!"{name}: reduction_ns={stop-start} scalars={result.writer.stream.size} challenges={result.writer.challenges.size}; all witness layers, scalars, batch claims, challenges and openings match Rust"

/-- Run the active fixture with no phase marks. -/
def check : IO Unit := fixture "active" fun _ _ => pure ()

end CompStarkTests.KeccakGkr
