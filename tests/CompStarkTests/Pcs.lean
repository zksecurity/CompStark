/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.Tensor
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

/-- Compare coordinate maps, cached factors, packed-bit folds and mapped tensors against Rust bytes. -/
def check : IO Unit := do
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
