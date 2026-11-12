/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Verifier
public import CompStark.Tables.Composed.Keccak.Honest
public import CompStark.Keccak.GkrProver.Refinement
public import CompStark.Keccak.Scalar
public import CompStark.Pcs.WordEncoding
public import CompStarkFixtures.Tables

/-! `hashes`: a Keccak table of 256 rows, four executed, whose 25 output lanes are virtual columns
discharged by the Keccak-f GKR, pushes `(input, output)` states on bus `keccak`; a user table of
four rows pulls them, one state twice. The composed proof system on it, with the native Keccak-f
GKR prover for the external argument, for the compiled tests. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[expose] public section
namespace CompStark.Fixtures.TablesKeccak
open CompStark.Tables CompStark.Tables.Composed CompStark.BinaryFields CompStark.Multilinear
open CompStark.Stark CompStark.Compose CompStark.Fixtures.Tables

/-- The base-field word of a lane. -/
def word (x : UInt64) : K := K.ofBits x.toNat

/-- Twelve Keccak-f rounds from round `r` on 25 lanes. -/
def rounds (r : ℕ) (s : Array UInt64) : Array UInt64 :=
  CompStark.Keccak.permute 12 r s[0]! s[1]! s[2]! s[3]! s[4]! s[5]! s[6]! s[7]! s[8]! s[9]! s[10]!
    s[11]! s[12]! s[13]! s[14]! s[15]! s[16]! s[17]! s[18]! s[19]! s[20]! s[21]! s[22]! s[23]! s[24]!

/-- A Keccak row: input lanes, middle lanes, fourteen zero columns, output lanes. -/
def keccakRow (input : Array UInt64) : Array K :=
  let middle := rounds 0 input
  (input ++ middle ++ Array.replicate 14 0 ++ rounds 12 middle).map word

/-- A user row: input lanes, output lanes. -/
def userRow (input : Array UInt64) : Array K :=
  (input ++ rounds 12 (rounds 0 input)).map word

/-- The zero state. -/
def zero : Array UInt64 := Array.replicate 25 0

/-- The Keccak table: 64 committed slots and 25 virtual output lanes; it pushes its input and
output lanes. -/
def keccakTable : Table K where
  air := { width := 89, numPublicValues := 0, constraints := [] }
  interactions := [⟨"keccak", true, (List.range 25).map .cur ++ (List.range 25).map fun l ↦ .cur (64 + l)⟩]
  virtual := List.range' 64 25
  padding := List.ofFn fun i : Fin 89 ↦ (keccakRow zero).getD i.val 0

/-- The user table: it pulls input and output lanes. -/
def userTable : Table K where
  air := { width := 50, numPublicValues := 0, constraints := [] }
  interactions := [⟨"keccak", false, (List.range 50).map .cur⟩]
  padding := List.replicate 50 0

/-- The Keccak-f relation of the Keccak table's rows. -/
def hashesRelation (w : Witness K 2) : Prop :=
  Keccak.Gkr.InputRelation (p := 4) (ofK g) (fun b l ↦ ofK (((w 0).getD b.val #[]).getD (64 + l.val) 0))
    (fun b j z ↦ Pcs.wordBits (((w 0).getD b.val #[]).getD j.val 0) z)

/-- Keccak-f states pushed by a Keccak table and pulled by a user table. -/
def hashes : System K where
  tables := [keccakTable, userTable]
  buses := ["keccak"]
  external := hashesRelation

/-- Heights 256 and four, four rows of each executed. -/
def hashesLayout : Layout hashes.tables.length :=
  ⟨fun t ↦ [4, 4].getD t.val 0, fun t ↦ [8, 2].getD t.val 0⟩

/-- Four input states, the first twice. -/
def inputs : List (Array UInt64) :=
  let state (seed : ℕ) : Array UInt64 := Array.ofFn fun i : Fin 25 ↦ UInt64.ofNat (seed * 0x9e3779b97f4a7c15 + i.val)
  [state 1, state 1, state 2, state 3]

/-- The witness: the four states and 252 zero-state padding rows; the user table pulls the four. -/
def hashesWitness : Witness K hashes.tables.length := fun t ↦
  [inputs.map keccakRow ++ List.replicate 252 (keccakRow zero), inputs.map userRow].getD t.val []

/-- The description and layout are well formed. -/
theorem hashes_wellFormed : hashes.WellFormed hashesLayout := by decide +kernel

/-- The bus's tuples: the separator and fifty entries. -/
def width : String → ℕ := fun _ ↦ 50

/-- The bus has one width and fits 64 entries. -/
theorem hashesShape : hashes.BusShape 6 width := by decide +kernel

/-- The stack fits fifteen variables. -/
theorem hashesFits : (hashes.stackBlocks hashesLayout).total ≤ 2 ^ 15 := by
  rw [System.stackBlocks_total]
  decide

/-- The Keccak table. -/
def keccakIndex : Fin hashes.tables.length := ⟨0, by decide⟩

/-- The user table. -/
def userIndex : Fin hashes.tables.length := ⟨1, by decide⟩

/-- The stack: the Keccak table's 64 slots, then the user table's 50 columns. -/
theorem hashes_stackColumns : hashes.stackColumns hashesLayout =
    (List.range 64).map (keccakIndex, ·) ++ (List.range 50).map (userIndex, ·) := by
  rw [System.stackColumns_of_descending _ _ (by decide +kernel)]
  decide +kernel

/-- The Keccak table of `hashes`. -/
def keccak : KeccakTable hashes hashesLayout 15 where
  table := keccakIndex
  p := 4
  height := rfl
  active := by decide
  slot j := j.val
  output l := 64 + l.val
  first := 0
  stacked j := by
    have hj := j.isLt
    refine ⟨by rw [hashes_stackColumns]; simp only [List.length_append, List.length_map,
      List.length_range]; omega, ?_⟩
    simp only [hashes_stackColumns, Nat.zero_add]
    rw [List.getElem_append_left (by simp only [List.length_map, List.length_range]; omega),
      List.getElem_map, List.getElem_range]
  aligned := by
    rw [show (hashes.stackBlocks hashesLayout).offsetNat 0 = 0 from Finset.sum_range_zero _]
    exact dvd_zero _
  fits := by
    rw [show (hashes.stackBlocks hashesLayout).offsetNat 0 = 0 from Finset.sum_range_zero _]
    decide
  output_lt := by decide +kernel
  output_transmitted := by decide +kernel
  output_injective a b h := Fin.ext (by simp only at h; omega)
  virtual_iff t c := by
    match t with
    | ⟨0, _⟩ =>
      change c ∈ List.range' 64 25 ↔ _
      rw [List.mem_range']
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨Fin.ext rfl, ⟨i, hi⟩, ?_⟩
        change 64 + i = 64 + 1 * i
        omega
      · rintro ⟨_, l, hl⟩
        change 64 + l.val = c at hl
        exact ⟨l.val, l.isLt, by omega⟩
    | ⟨1, _⟩ =>
      change c ∈ ([] : List ℕ) ↔ _
      simp only [List.not_mem_nil, false_iff, not_and]
      intro h
      exact absurd (congrArg Fin.val h) (by simp [keccakIndex])
  external_iff _ := Iff.rfl

/-- The composed setup of `hashes` with the Keccak table's argument. -/
def hashesSetup : Setup hashes hashesLayout 6 15 where
  width := width
  wellFormed := hashes_wellFormed
  busShape := hashesShape
  fits := hashesFits
  boundary := by decide +kernel
  degree_le := by decide +kernel
  external := keccak.external hashesFits

/-- A fourteen-variable terminal table after one folded coordinate. -/
def schedule : CompStark.Pcs.EvaluatedSchedule 15 :=
  .last 1 14 (CompStark.Pcs.evaluatedEncoding 14 1 (by decide)) 3

/-- Fixed verifier coins. -/
def coins : Coins (S := hashes) (L := hashesLayout) (k := 6) schedule.schedule where
  bus := ((fun i ↦ value (i.val + 1), value 3), GrandProduct.Coins.fill (fun n ↦ value (n + 11)) _ 0 0)
  table := (value 5, fun i ↦ value (i.val + 41))
  opening := (value 61, fun _ ↦ value 67, fun i ↦ ⟨i.val, by change i.val < 32768; omega⟩, value 73,
    fun i ↦ value (i.val + 79))

/-- The native Keccak-f GKR on the stack's slot region at the table's point, its challenges drawn by
a Keccak duplex, then six ring-switching draws. -/
def keccakProve : ExternalProver hashesSetup := fun o q ↦
  let committed := Array.ofFn fun u : Fin (2 ^ 14) ↦ UInt64.ofBitVec (keccak.word q u).toBitVec
  let batch := Array.ofFn fun i : Fin 8 ↦ BF64.WordExt3.ofField (keccak.instancePoint o i)
  let output := Array.ofFn fun l : Fin 25 ↦
    BF64.WordExt3.ofField (o.values ⟨keccak.table, keccak.active⟩ (keccak.outputIndex l))
  let writer := (Keccak.GkrProver.Writer.seed #[1, 2, 3, 4] #[5, 6, 7, 8]).writeAll output
  let reduction := Keccak.GkrProver.prove writer (Keccak.GkrProver.buildWitness 8 committed) committed batch output
  let t := reduction.toProtocol 4 (Keccak.GkrProver.prove_layers_size ..)
  joinPath _ _ (wirePath (gkrSteps 4) ((Keccak.Gkr.transcriptMessages t).drop 8))
    (ringPath (Vector.ofFn fun i ↦ value (i.val + 97)))

/-- The honest transcript of a witness of `hashes`. -/
def hashesProof (w : Witness K hashes.tables.length) :
    (composedProtocol hashesSetup schedule.schedule).tree.ExecutionPath :=
  honestPath hashesSetup schedule.schedule keccakProve w coins

/-- The fast verifier on a transcript of `hashes`. -/
def hashesVerify (path : (composedProtocol hashesSetup schedule.schedule).tree.ExecutionPath) : Bool :=
  verifyWith hashesSetup schedule path

end CompStark.Fixtures.TablesKeccak
