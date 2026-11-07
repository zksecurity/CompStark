/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import CompStark.Pcs.CoordinateMap
public import CompStark.Pcs.Encoding
public import CompStark.Pcs.Induction
public import CompStark.Pcs.Accumulated
public import CompStark.Pcs.NativeRound
public import CompStark.Pcs.NativeBasis
public import CompStark.Pcs.BasisColumnPrepared
/-! Deterministic inputs for binary-field PCS conformance and measurement. -/
@[expose] public section
namespace CompStark.Fixtures.Pcs
open BF64 CompStark.Pcs

/-- Deterministic test elements with all three limbs populated. -/
def value (i : Nat) : WordExt3 :=
  ⟨⟨UInt64.ofNat (0x123456789abcdef0 + 31 * i)⟩,
    ⟨UInt64.ofNat (0xfedcba9876543210 + i * i)⟩,
    ⟨UInt64.ofNat (0x8000000000000001 + 17 * i)⟩⟩

/-- The six shared map challenges. -/
def challenges : Vector WordExt3 6 := Vector.ofFn fun i => value (i.val + 19)

/-- Canonical little-endian bytes of consecutive extension words. -/
def bytes (values : Array WordExt3) : ByteArray :=
  values.foldl (fun output x =>
    [x.c0.val, x.c1.val, x.c2.val].foldl (fun output word =>
      (List.range 8).foldl (fun output j => output.push ((word >>> (8 * j).toUInt64).toUInt8))
        output) output) ByteArray.empty

/-- Full-limb cubic-extension messages in row-major lane and coefficient order. -/
def encodingInput (ell lanes : Nat) : BF64.Packed.Buffer (2 ^ ell * (3 * lanes)) :=
  AdditiveNTT.Packed.tabulate _ fun i =>
    let a := value (i.val / 3)
    if i.val % 3 = 0 then a.c0 else if i.val % 3 = 1 then a.c1 else a.c2


/-- Sixty-four full base-field witness lanes with sixty-four columns each. -/
def basisWitness (seed : Nat) : Vector Word (64*64) :=
  Vector.ofFn fun i => ⟨UInt64.ofNat (0x9e3779b97f4a7c15 * (seed + i.val + 1))⟩

/-- Three independent low/high tensor pairs of the production Basis fixture. -/
def basisFactors (seed : Nat) : Fin 3 → FactoredEq WordExt3 6 6 := fun t =>
  wordFactoredEq (fun i => (value (seed+t.val*17+i.val+101)).toField)

/-- Shared low equality tensors in numeric column order. -/
def basisKernels (seed : Nat) : Vector (Vector WordExt3 64) 3 :=
  let factors := Vector.ofFn (basisFactors seed)
  Vector.ofFn fun t => Vector.ofFn fun x => factors[t].low (vertex 6 x)

/-- Scaled high equality tensors in row-major lane/term order. -/
def basisLaneFactors (seed : Nat) : Vector WordExt3 (64*3) :=
  let factors := Vector.ofFn (basisFactors seed)
  Vector.ofFn fun i => WordExt3.mul (value (seed+i.val%3+501))
    (factors[(⟨i.val%3, by omega⟩ : Fin 3)].high (vertex 6 ⟨i.val/3, by omega⟩))

/-- The point factors retain their native window representation. -/
def basisColumns (seed : Nat) : Vector (BasisColumn 64) 3 :=
  (basisKernels seed).map fun values => .point ⟨0, 64, values, by decide⟩

/-- The production-style projection and lane matrices for the Rust fixture. -/
def basisMatrices (seed : Nat) : Vector WordExt3 (64*3) × Vector WordExt3 (64*3) :=
  (projectColumns 64 64 3 (basisWitness seed) (basisColumns seed), basisLaneFactors seed)

/-- Production-style shared binary columns and repeated point windows for the instruction gate. -/
def projectionColumns (seed : Nat) : Vector (BasisColumn 1024) 200 :=
  let values := Vector.ofFn fun i : Fin 1024 => value (i.val+31+seed)
  let window : BasisWindow 1024 := ⟨0, 1024, values, by decide⟩
  Vector.ofFn fun i => if h : i.val < 192 then .binary values ⟨i.val, h⟩ else .point window

/-- A complete eight-lane witness for the shared-column gate. -/
def projectionWitness (seed : Nat) : Vector Word (8*1024) :=
  Vector.ofFn fun i => ⟨UInt64.ofNat ((i.val+seed+1)*0x9e3779b97f4a7c15)⟩

end CompStark.Fixtures.Pcs
