/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Sumcheck.PackedFold
public import CompStark.Sumcheck.IndexFold
meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command

/-! Compiled prepared-fold regressions, including empty tables and column order. -/

@[expose] public section
namespace CompStarkTests.Sumcheck
open BF64 CompStark.Sumcheck

/-- Deterministic full-limb test values. -/
def value (i : Nat) : WordExt3 :=
  ⟨⟨UInt64.ofNat (0x123456789abcdef0 + 31 * i)⟩,
    ⟨UInt64.ofNat (0xfedcba9876543210 + i * i)⟩,
    ⟨UInt64.ofNat (0x8000000000000001 + 17 * i)⟩⟩

/-- Compare native multiplication and folds with the independently evaluated scalar kernels. -/
def check : IO Unit := do
  for r in [value 0, ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩, ⟨⟨1⟩, ⟨0⟩, ⟨0⟩⟩] do
    let plan := prepare r
    for i in [0:128] do
      unless (plan.mul (value i)).toField == (WordExt3.mul r (value i)).toField do
        throw (IO.userError s!"prepared multiplication mismatch at {i}")
    for rows in [0, 1, 2, 17, 256] do
      for width in [0, 1, 4, 15] do
        let table := Vector.ofFn fun i : Fin (2 * rows * width) => value i.val
        let folded := fold plan rows width table
        if hn : 8 * table.size < USize.size then
          let packed := PackedScalars.ofArray table.toArray (by simpa only [Vector.size_toArray] using hn)
          let packedOutput := (foldPacked plan rows width table.toArray.size packed (by simpa only [Vector.size_toArray] using hn) (by simp only [Vector.size_toArray]; rfl)).toArray (by
            simp only [Vector.size] at hn
            nlinarith)
          unless packedOutput == folded.toArray do
            throw (IO.userError s!"packed fold mismatch rows={rows} width={width}")
        else throw (IO.userError "unaddressable packed fold fixture")
        for i in [:folded.size] do
          let a := table[2 * (i / width) * width + i % width]!
          let b := table[(2 * (i / width) + 1) * width + i % width]!
          let expected := WordExt3.add a (WordExt3.mul r (WordExt3.add a b))
          unless folded[i]!.toField == expected.toField do
            throw (IO.userError s!"fold mismatch rows={rows} width={width} at {i}")
  let output := fold (prepare (value 19)) 17 4 (Vector.ofFn fun i => value i.val)
  let bytes := output.toArray.foldl (fun bytes x =>
    [x.c0.val, x.c1.val, x.c2.val].foldl (fun acc w =>
      (List.range 8).foldl (fun b j => b.push ((w >>> (8 * j).toUInt64).toUInt8)) acc) bytes) ByteArray.empty
  let expected ← IO.FS.readBinFile "tests/data/sumcheck-fold.bin"
  unless bytes == expected do throw (IO.userError "Rust interleaved-fold byte mismatch")
  IO.println "prepared sumcheck folds: passed"

end CompStarkTests.Sumcheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "CompStark.Sumcheck." then
      for axiomName in ← collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
