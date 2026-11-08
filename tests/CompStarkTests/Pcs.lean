/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BasisColumnPrepared
public import CompStark.Pcs.PackedInductionDot
public import CompStark.Pcs.SparseInduction
public import CompStark.Pcs.CompactInduction
public import CompStark.Pcs.SparseStrip
public import CompStark.Pcs.FusedRound
public import CompStark.Pcs.DirectSums
public import CompStark.Pcs.WindowBitFold
public import CompStark.Pcs.WindowScatter
public import CompStark.Pcs.HonestWhir
public import CompStarkFixtures.Pcs
meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command

/-! Native binary-field PCS known answers and honest WHIR acceptance regressions. -/

@[expose] public section
namespace CompStarkTests.Pcs
open BF64 CompStark.Pcs CompStark.Fixtures.Pcs

/-- A small linear encoding over natural coefficients, exercising arbitrary commutative rings. -/
def testEncoding (n : Nat) : Whir.Encoding Nat n where
  rate := 1
  domain := ⟨Fin.val, Fin.val_injective⟩
  weight x u := (x.val + 1) ^ (vertexIndex n u).val

/-- Two encoded levels followed by a one-variable plaintext. -/
def testSchedule : Whir.Schedule Nat 3 :=
  .more 1 (testEncoding 2) 3 (.last 1 1 (testEncoding 1) 2)

/-- Fixed verifier coins include repeated query positions. -/
def testCoins : WhirCoins Nat (ZMod 17) testSchedule :=
  (3, fun _ => 2, fun i => i.val + 4, fun i => ⟨i.val, by change i.val < 8; omega⟩,
    (4, fun _ => 6, fun _ => ⟨1, by decide⟩, 7, fun _ => 8))

/-- The exact honest opening is accepted in a ring of odd characteristic as well. -/
def testWhir : Bool :=
  let table : Whir.Table (ZMod 17) 3 := fun u => (vertexIndex 3 u).val + 1
  let weight : Whir.Table (ZMod 17) 3 := fun u => (vertexIndex 3 u).val + 2
  let claims : List (Whir.Claim (ZMod 17) 3) := [⟨weight, dot weight table⟩]
  Whir.accepts (Nat.castRingHom (ZMod 17)) testSchedule
    (encodeLevel (Nat.castRingHom (ZMod 17)) testSchedule table) claims
    (honestWhir (Nat.castRingHom (ZMod 17)) testSchedule table claims testCoins)

/-- The empty-dimensional, query-free terminal level is also a valid honest opening. -/
def testEmpty : Bool :=
  let schedule := Whir.Schedule.last 0 0 (testEncoding 0) 0
  let table : Whir.Table (ZMod 17) 0 := fun _ => 11
  let coins : WhirCoins Nat (ZMod 17) schedule :=
    (2, Fin.elim0, Fin.elim0, 3, Fin.elim0)
  Whir.accepts (Nat.castRingHom (ZMod 17)) schedule
    (encodeLevel (Nat.castRingHom (ZMod 17)) schedule table) []
    (honestWhir (Nat.castRingHom (ZMod 17)) schedule table [] coins)

/-- Compare the projected lane matrices with Rust and follow all six folded messages. -/
def checkBasis : IO Unit := do
  let input : Vector Word (8*32) := Vector.ofFn fun i => ⟨UInt64.ofNat (i.val*31337)⟩
  let tensor : Vector WordExt3 32 := Vector.ofFn fun i => value (i.val+31)
  let coordinates : Vector (Fin 192) 6 := #v[0, 63, 64, 127, 128, 191]
  let columns : Vector (BasisColumn 32) 10 := Vector.ofFn fun i =>
    if h : i.val < 6 then .binary tensor coordinates[i.val] else
    if i.val < 9 then .point ⟨3, 5, Vector.ofFn (fun j => value (j.val+17)), by decide⟩
    else .point ⟨32, 0, #v[], by decide⟩
  unless projectColumns 8 32 10 input columns ==
      projectBasis 8 32 10 input (columns.map BasisColumn.expand) do
    throw (IO.userError "compact Basis point/binary projection mismatch")
  let coefficients : Vector WordExt3 10 := Vector.ofFn fun i => value (i.val+131)
  unless liftColumns 32 10 coefficients columns ==
      liftBasis 32 10 coefficients (columns.map BasisColumn.expand) do
    throw (IO.userError "compact Basis final lift mismatch")
  let (projection, factors) := basisMatrices 0
  for (name, values) in [("projection", projection.toArray), ("lane-factors", factors.toArray)] do
    let expected ← IO.FS.readBinFile s!"tests/data/pcs/{name}.bin"
    unless bytes values == expected do throw (IO.userError s!"projected Basis Rust mismatch: {name}")
  let kernels := basisKernels 0
  let mut projected := projection.toArray
  let mut lanes := factors.toArray
  let mut table := (basisWitness 0).toArray.map fun x => (⟨x, ⟨0⟩, ⟨0⟩⟩ : WordExt3)
  let mut weight := (Array.ofFn fun i : Fin 4096 =>
    (liftBasis 64 3 (Vector.ofFn fun t => factors[basisAddress (⟨i.val/64, by omega⟩ : Fin 64) t])
      kernels)[i.val%64]!)
  for j in [:6] do
    let rows := 2^(5-j)
    let small := roundCoefficients rows 3 (Vector.ofFn fun i => projected[i.val]!)
      (Vector.ofFn fun i => lanes[i.val]!)
    let large := roundCoefficients rows 64 (Vector.ofFn fun i => table[i.val]!)
      (Vector.ofFn fun i => weight[i.val]!)
    unless small == large do throw (IO.userError s!"projected Basis round mismatch: {j}")
    let map := CompStark.Sumcheck.prepare (value (j+701))
    projected := (CompStark.Sumcheck.fold map rows 3 (Vector.ofFn fun i => projected[i.val]!)).toArray
    lanes := (CompStark.Sumcheck.fold map rows 3 (Vector.ofFn fun i => lanes[i.val]!)).toArray
    table := (CompStark.Sumcheck.fold map rows 64 (Vector.ofFn fun i => table[i.val]!)).toArray
    weight := (CompStark.Sumcheck.fold map rows 64 (Vector.ofFn fun i => weight[i.val]!)).toArray
  let lifted := liftBasis 64 3 (Vector.ofFn fun i => lanes[i.val]!) kernels
  unless lifted.toArray == weight do throw (IO.userError "projected Basis final lift mismatch")

/-- Split tensors and occupied butterflies preserve empty shapes, duplicate queries and all limbs. -/
def checkInduction : IO Unit := do
  for (lo, hi, rate, lanes, count) in
      [(0, 0, 0, 3, 0), (0, 0, 1, 3, 3), (2, 3, 0, 0, 7),
       (2, 3, 0, 3, 0), (2, 3, 2, 3, 10), (6, 6, 2, 3, 137)] do
    if hd : lo+hi+rate < 64 then
      let plan := (AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis (lo+hi+rate) hd).toPacked
      let positions : Vector (Fin (2^(lo+hi+rate))) count := Vector.ofFn fun q =>
        ⟨(if q.val%7 = 0 then 0 else q.val*7919+91) % 2^(lo+hi+rate),
          Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let values := fun q : Fin count => fun c : Fin lanes =>
        mapLimb (value (q.val+77)) ⟨c.val%3, Nat.mod_lt _ (by decide)⟩
      let original := induceRows hd plan lanes positions values
      let split := induceSplitRows lo hi rate hd lanes positions values
      let packed := induceSplitRowsPacked lo hi rate hd lanes positions values
      let sparse := induceOccupiedRows hd plan lanes positions values
      let prepared := induceOccupiedRows hd (sparseInductionPlan _ hd) lanes positions values
      let compact := induceOccupiedCompactRows hd lanes positions values
      let byteRows := induceOccupiedByteRows hd lanes positions values
      let tiled := induceSparseStripRows hd lanes positions values
      unless original.val.bytes == packed.val.bytes && original.val.bytes == tiled.val.bytes && original.val.bytes == byteRows.val.bytes && original.val.bytes == compact.val.bytes && original.val.bytes == split.val.bytes && original.val.bytes == sparse.val.bytes && original.val.bytes == prepared.val.bytes do
        throw (IO.userError s!"induction shape mismatch: {lo}/{hi}/{rate}/{lanes}/{count}")
      if lo = 6 && hi = 6 then
        let expected ← IO.FS.readBinFile "tests/data/pcs/induced-large.bin"
        unless original.val.bytes == expected do throw (IO.userError "large induced weights Rust mismatch")

/-- Short scalar folds and shared maps preserve blocked pairs and the preparation boundary. -/
def checkChallengeFold : IO Unit := do
  for (rows, width) in [(0, 0), (3, 0), (0, 3), (7, 3), (256, 1), (257, 1), (129, 2)] do
    let input : Vector WordExt3 (2*rows*width) := Vector.ofFn fun i => value (i.val+71)
    let weight : Vector WordExt3 (2*rows*width) := Vector.ofFn fun i => value (i.val+173)
    let r := value 43
    let shared := CompStark.Sumcheck.prepare r
    let expected := (CompStark.Sumcheck.fold shared rows width input,
      CompStark.Sumcheck.fold shared rows width weight)
    unless foldPairChallenge r rows width input weight == expected &&
        (foldScalar r rows width input, foldScalar r rows width weight) == expected do
      throw (IO.userError s!"challenge fold mismatch: {rows}/{width}")

/-- Fused folds retain both restricted arrays and the following message across the map threshold. -/
def checkFusedRound : IO Unit := do
  for rows in [0,1,7,128,129,1024] do
    let input : Vector WordExt3 (4*rows) := Vector.ofFn fun i => value (i.val+71)
    let weight : Vector WordExt3 (4*rows) := Vector.ofFn fun i => value (i.val+173)
    let r := value 43
    let fused := foldMessage r rows input weight
    let table := Vector.ofFn (foldedCoordinate (CompStark.Sumcheck.prepare r) rows input)
    let weights := Vector.ofFn (foldedCoordinate (CompStark.Sumcheck.prepare r) rows weight)
    let message := roundCoefficients rows 1
      (Vector.ofFn fun i => table[i.val]'(by have := i.isLt; omega))
      (Vector.ofFn fun i => weights[i.val]'(by have := i.isLt; omega))
    unless fused.table == table.toArray && fused.weight == weights.toArray &&
        #[fused.constant,fused.quadratic] == message.toArray do
      throw (IO.userError s!"fused WHIR round mismatch: {rows}")

/-- Compare coordinate maps, cached factors, packed-bit folds and mapped tensors against Rust bytes. -/
def check : IO Unit := do
  checkBasis
  checkInduction
  checkChallengeFold
  checkFusedRound
  unless testWhir && testEmpty do throw (IO.userError "honest WHIR acceptance failed")
  let coordinates := coordinateWeights challenges
  let point : Fin (4 + 4) → BF64.Ext3 := fun i => (value (i.val + 101)).toField
  let factors := wordFactoredEq (lo := 4) (hi := 4) point
  let tensor : Vector WordExt3 256 := Vector.ofFn fun i => factors.eval (vertex 8 i)
  let packed : Vector Word 256 := Vector.ofFn fun i => ⟨UInt64.ofNat (0x9e3779b97f4a7c15 * (i.val + 1))⟩
  let slices := foldBits packed tensor
  let mapped : Vector WordExt3 256 := tensor.map (applyCoordinates coordinates)
  for (name, actual) in [("coordinates", coordinates.toArray), ("tensor", tensor.toArray),
      ("slices", slices.toArray), ("mapped", mapped.toArray)] do
    let expected ← IO.FS.readBinFile s!"tests/data/pcs/{name}.bin"
    unless bytes actual == expected do throw (IO.userError s!"PCS Rust mismatch: {name}")
  let plan := AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis 8 (by decide)
  let encoded := encodeExtensionRows (ell := 6) (rate := 2) (by decide) plan 16
    (by decide) (encodingInput 6 16) (by decide)
  let expected ← IO.FS.readBinFile "tests/data/pcs/encoded.bin"
  unless encoded.val.bytes == expected do throw (IO.userError "bitsliced E encoding Rust mismatch")
  let positions : Vector (Fin 256) 7 := ⟨#[3, 17, 3, 255, 128, 0, 64], rfl⟩
  let induced := induceRows (ell := 6) (rate := 2) (by decide) plan.toPacked 3 positions fun q c =>
    mapLimb (value (q.val + 77)) c
  let dense := induceDenseRows (ell := 6) (rate := 2) (by decide) plan.toPacked 3 positions fun q c =>
    mapLimb (value (q.val + 77)) c
  let expected ← IO.FS.readBinFile "tests/data/pcs/induced.bin"
  unless induced.val.bytes == expected && dense.val.bytes == expected do throw (IO.userError "sparse induced weights Rust mismatch")
  let acc : Vector WordExt3 256 := Vector.ofFn fun i => value (i.val + 100)
  let incoming : Vector WordExt3 256 := Vector.ofFn fun i => value (i.val + 200)
  let accumulated := addScaled (CompStark.Sumcheck.prepare (value 43)) acc incoming
  let expected ← IO.FS.readBinFile "tests/data/pcs/accumulated.bin"
  unless bytes accumulated.toArray == expected do throw (IO.userError "accumulated weights Rust mismatch")
  let round := roundCoefficients 128 1 accumulated incoming
  let expected ← IO.FS.readBinFile "tests/data/pcs/round.bin"
  unless bytes round.toArray == expected do throw (IO.userError "native WHIR round mismatch")
  for lo in [0, 1, 3, 8] do
    let point : Fin (lo + 2) → BF64.Ext3 := fun i => (value (i.val + 7)).toField
    let factors := wordFactoredEq (lo := lo) (hi := 2) point
    for i in List.finRange (2 ^ (lo + 2)) do
      let u := vertex (lo + 2) i
      let expected := Whir.eqWeight (fun j => WordExt3.ofField (point j)) u
      unless factors.eval u == expected do throw (IO.userError "factored equality tensor mismatch")
  for rings in [0, 1, 3] do
    for points in [0, 1, 7] do
      unless powersFrom (value 3) (rings + points) 1 ==
          powersFrom (value 3) rings 1 ++ powersFrom (value 3) points ((value 3) ^ rings) do
        throw (IO.userError "PCS shared batching-power order mismatch")
  for seed in [0, 1, 73] do
    let weights := Vector.ofFn fun i : Fin 192 => value (i.val+seed)
    let prepared := prepareCoordinates weights
    let inputs := #[⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩, value seed,
      ⟨⟨0xffffffffffffffff⟩, ⟨0xffffffffffffffff⟩, ⟨0xffffffffffffffff⟩⟩] ++
      (Vector.ofFn coordinateBasis).toArray
    for a in inputs do
      unless applyCoordinateBytes prepared a == applyCoordinates weights a do
        throw (IO.userError "prepared binary-coordinate map mismatch")
  for cols in [0, 1, 17] do
    let values := Vector.ofFn fun i : Fin cols => value (i.val+91)
    let points : Vector (BasisWindow cols) 2 :=
      #v[⟨0, 0, #v[], by omega⟩, ⟨0, cols, values, by omega⟩]
    let weights := Vector.ofFn fun i : Fin 194 => value (i.val+12)
    unless liftPointBinary cols 2 points values weights == liftColumns cols 194 weights
        (points.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary values bit)) do
      throw (IO.userError "shared binary Basis reconstruction mismatch")
  for cols in [0, 1, 17, 63, 64, 65, 129] do
    let values := Vector.ofFn fun i : Fin cols => value (i.val+91)
    let words := Vector.ofFn fun i : Fin cols =>
      (⟨UInt64.ofNat (0x9e3779b97f4a7c15*(i.val+1))⟩ : Word)
    let plan := prepareByteFold values
    unless foldBytePlan plan words == foldBits words values do
      throw (IO.userError "padded byte-table bit fold mismatch")
    unless dotBytePlan plan words == sumExt cols (fun i => WordExt3.mulScalar values[i] words[i]) do
      throw (IO.userError "byte-table mixed dot mismatch")
    unless dotMixedPlan (prepareMixedDot values) (fun i => words[i]) ==
        sumExt cols (fun i => WordExt3.mulScalar values[i] words[i]) do
      throw (IO.userError "packed mixed dot mismatch")
    let sparse := words.map fun a => if a.val % 3 = 0 then (⟨0⟩ : Word) else a
    unless dotMixedPlan (prepareMixedDot values) (fun i => sparse[i]) ==
        sumExt cols (fun i => WordExt3.mulScalar values[i] sparse[i]) do
      throw (IO.userError "packed sparse mixed dot mismatch")
    let points : Vector (BasisWindow cols) 2 :=
      #v[⟨0, 0, #v[], by omega⟩, ⟨0, cols, values, by omega⟩]
    let witness : Vector Word (2*cols) := Vector.ofFn fun i =>
      ⟨UInt64.ofNat (0x9e3779b97f4a7c15*(i.val+1))⟩
    unless projectPointBinary 2 cols 2 witness points values == projectColumns 2 cols 194 witness
        (points.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary values bit)) do
      throw (IO.userError "joint point/ring byte projection mismatch")
  for low in [0, 1, 17, 64] do
    for high in [0, 1, 3] do
      let windows : Vector (BasisWindow low) 3 := Vector.ofFn fun t =>
        if t.val = 0 then ⟨0, 0, #v[], by omega⟩ else
          ⟨low/3, low-low/3, Vector.ofFn (fun x => value (x.val+31)), by omega⟩
      let gamma : Vector (Vector WordExt3 high) 3 := Vector.ofFn fun t =>
        Vector.ofFn fun h => if h.val = 0 then 0 else value (t.val+19*h.val)
      let full : Vector (BasisWindow (high*low)) 3 := Vector.ofFn fun t =>
        ⟨0, high*low, Vector.ofFn (fun x => roundProduct gamma[t][x.divNat] windows[t].expand[x.modNat]), by omega⟩
      let ring : Vector WordExt3 (high*low) := Vector.ofFn fun x => value (x.val+21)
      let witness : Vector Word (2*(high*low)) := Vector.ofFn fun x =>
        ⟨UInt64.ofNat ((x.val+1)*0x9e3779b97f4a7c15)⟩
      let columns := full.map BasisColumn.point ++ Vector.ofFn (fun bit : Fin 192 => BasisColumn.binary ring bit)
      unless projectTensorPointBinary 2 (high*low) low high 3 rfl witness windows gamma ring ==
          projectColumns 2 (high*low) 195 witness columns do
        throw (IO.userError "shared low/high tensor projection mismatch")
      let ringWindow : BasisWindow (high*low) :=
        ⟨high*low/3, high*low-high*low/3, Vector.ofFn (fun x => value (x.val+21)), by omega⟩
      unless projectTensorPointWindow 2 (high*low) low high 3 rfl witness windows gamma ringWindow ==
          projectTensorPointBinary 2 (high*low) low high 3 rfl witness windows gamma ringWindow.expand do
        throw (IO.userError "occupied ring projection mismatch")
      let weights : Vector WordExt3 195 := Vector.ofFn fun t => value (t.val+41)
      unless liftTensorPointBinary (high*low) low high 3 rfl windows gamma ring weights ==
          liftColumns (high*low) 195 weights columns do
        throw (IO.userError "grouped low/high tensor lift mismatch")
  IO.println "PCS coordinate maps, factored weights, bit folds, honest WHIR: passed"

end CompStarkTests.Pcs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "CompStark.Pcs." then
      for axiomName in ← collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
