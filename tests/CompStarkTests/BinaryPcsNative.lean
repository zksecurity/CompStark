/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Honest
public import CompStark.Pcs.Prover.Encoding

/-! Compiled checks of the binary PCS prover: the honest opening is accepted and an inconsistent
claim rejected, and the native extension encoding and the ring-switching target agree with
leanMultisig `9d8bce818aa7c7e18e67026e522a9b1539d0a57d` on the bytes in `tests/data/binary-pcs`, which
`tests/rust/binary-pcs.rs` writes and `scripts/check-binary-stack-reference` reproduces. -/

@[expose] public section
namespace CompStarkTests.BinaryPcsNative
open CompStark CompStark.BinaryFields

/-- Full-limb deterministic field values shared with the Rust harness. -/
def value (i : Nat) : E :=
  BF64.WordExt3.toField ⟨⟨UInt64.ofNat (0x123456789abcdef0 + 31 * i)⟩,
    ⟨UInt64.ofNat (0xfedcba9876543210 + i * i)⟩,
    ⟨UInt64.ofNat (0x8000000000000001 + 17 * i)⟩⟩

/-- Canonical little-endian extension scalars, constant limb first. -/
def bytes (values : Array E) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for x in values do
    let w := BF64.WordExt3.ofField x
    for limb in #[w.c0.val, w.c1.val, w.c2.val] do
      for i in [:8] do out := out.push (limb >>> (8 * i).toUInt64).toUInt8
  return out

/-- Read canonical extension scalars. -/
def scalars (raw : ByteArray) : Array E :=
  Array.ofFn fun i : Fin (raw.size / 24) =>
    let word (j : Nat) : UInt64 := Id.run do
      let mut w : UInt64 := 0
      for b in [:8] do w := w ||| (raw[24 * i.val + 8 * j + b]!.toUInt64 <<< (8 * b).toUInt64)
      return w
    BF64.WordExt3.toField ⟨⟨word 0⟩, ⟨word 1⟩, ⟨word 2⟩⟩

/-- An additive encoding with one folded coordinate and a two-variable terminal table. -/
def schedule : Whir.Schedule K 3 := .last 1 2 (Pcs.encoding 2 1 (by decide)) 3

/-- Fixed verifier coins with repeated query positions. -/
def coins : CompStark.Pcs.WhirCoins K E schedule :=
  (value 3, fun _ => value 7, fun i => ⟨i.val, by change i.val < 8; omega⟩,
    value 13, fun i => value (i.val + 17))

/-- The honest opening is accepted, and rejected against an inconsistent claim. -/
def checkHonest : Bool :=
  let table : Whir.Table K 3 := fun u => K.ofBits ((Pcs.cubeEquiv 3).symm u).val
  let weight : Whir.Table E 3 := fun u => value ((Pcs.cubeEquiv 3).symm u).val
  let claim : Whir.Claim E 3 :=
    ⟨weight, CompStark.Pcs.dot weight (fun u => ofK (table u))⟩
  let opening := Pcs.Honest.prove schedule table [claim] coins
  let initial := Whir.mapMasked ofK opening.initial
  Whir.accepts (algebraMap K E) schedule initial [claim] opening.transcript &&
    !Whir.accepts (algebraMap K E) schedule initial [⟨weight, claim.value + 1⟩] opening.transcript

/-- Every native extension-encoding output word against the Rust additive NTT. -/
def checkEncoding : IO Unit := do
  let input : BF64.Packed.Buffer (2 ^ 6 * (3 * 2 ^ 4)) := AdditiveNTT.Packed.tabulate _ fun i =>
    let a := BF64.WordExt3.ofField (value (i.val / 3))
    if i.val % 3 = 0 then a.c0 else if i.val % 3 = 1 then a.c1 else a.c2
  let plan := AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis 8 (by decide)
  let encoded := Pcs.Prover.Encoding.encode (vars := 6) (rate := 2) (lanes := 4)
    (by decide) plan (by decide) input (by decide)
  let actual := bytes (Array.ofFn fun i : Fin 4096 =>
    encoded ⟨i.val / 16, by omega⟩ (Pcs.mask 4 ⟨i.val % 16, by omega⟩))
  let expected ← IO.FS.readBinFile "tests/data/binary-pcs/encoded.bin"
  unless actual == expected do throw (IO.userError "native extension encoding differs from Rust")

/-- The six-map ring-switching target of 64 Rust slice values against Rust. -/
def checkRingTarget : IO Unit := do
  let slices := scalars (← IO.FS.readBinFile "tests/data/binary-pcs/ring-slices.bin")
  unless slices.size == 64 do throw (IO.userError "ring slice fixture shape mismatch")
  let statement : Pcs.RingSwitch.Statement 15 := ⟨fun i => value (i.val + 101), fun i => slices[i]!⟩
  let target := Pcs.RingSwitch.Prover.target statement (Vector.ofFn fun i => value (i.val + 19))
  let expected ← IO.FS.readBinFile "tests/data/binary-pcs/ring-target.bin"
  unless bytes #[target] == expected do throw (IO.userError "ring-switching target differs from Rust")

/-- Run the compiled PCS prover checks. -/
def check : IO Unit := do
  unless checkHonest do throw (IO.userError "honest PCS acceptance or inconsistent-claim rejection failed")
  checkEncoding
  checkRingTarget
  IO.println "binary PCS: honest opening, native extension encoding and ring-switching target match"

end CompStarkTests.BinaryPcsNative
