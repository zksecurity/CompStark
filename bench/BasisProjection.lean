/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.BasisColumnPrepared
public import CompStarkFixtures.Pcs

/-! Shared-binary projection benchmark at the production fixture dimensions. -/
@[expose] public section
open BF64 CompStark.Pcs

/-- Exercise the complete projection kernel on an output-dependent production-sized matrix. -/
def main : IO Unit := do
  let input : Vector Word (64*8192) := Vector.ofFn fun i =>
    ⟨UInt64.ofNat ((i.val+1)*0x9e3779b97f4a7c15)⟩
  let values : Vector WordExt3 8192 := Vector.ofFn fun i => CompStark.Fixtures.Pcs.value (i.val+31)
  let window : BasisWindow 8192 := ⟨0, 8192, values, by decide⟩
  let columns := Vector.ofFn fun i : Fin 200 =>
    if h : i.val < 192 then BasisColumn.binary values ⟨i.val, h⟩ else .point window
  let began ← IO.monoNanosNow
  let result := projectColumns 64 8192 200 input columns
  let elapsed := (← IO.monoNanosNow)-began
  unless result[12799]!.c0.val == 10364763122551214041 do
    throw (IO.userError "production Basis projection sink differs")
  IO.println s!"projection_ns={elapsed} sink={result[12799]!.c0.val}"
