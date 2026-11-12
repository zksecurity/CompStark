/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Encoding
public import CompStark.Tables.Composed.External
public import CompStark.Pcs.Bits

/-! A Keccak table of a system: rows of `2 ^ (p + 4)` permutations whose 64 committed slots hold the
input lanes, the middle lanes after twelve rounds and fourteen further columns, stacked as one
aligned region of the stack, and whose 25 virtual columns are the output lanes after the other
twelve rounds. The system's external relation is the Keccak-f relation of these rows, as the
Keccak-f GKR states it (`KeccakRelation`); the virtual outputs read off a stack are computed from
its middle lanes (`interpret`). -/

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System

variable {S : System K}

/-- The word in slot column `c` of row `b` of table `t`. -/
def rowWord (w : Witness K S.tables.length) (t : Fin S.tables.length) (b c : ℕ) : K :=
  ((w t).getD b #[]).getD c 0

/-- The bits of a table's 64 slot columns, row by row: the Keccak-f GKR's witness. -/
def witnessBits (p : ℕ) (w : Witness K S.tables.length) (t : Fin S.tables.length) (slot : Fin 64 → ℕ) :
    Keccak.Gkr.Witness p :=
  fun b j z ↦ Pcs.wordBits (rowWord w t b.val (slot j)) z

/-- A table's output lanes, row by row, in the challenge field. -/
def witnessOutputs (p : ℕ) (w : Witness K S.tables.length) (t : Fin S.tables.length)
    (output : Fin 25 → ℕ) : Fin (2 ^ (p + 4)) → Fin 25 → E :=
  fun b l ↦ ofK (rowWord w t b.val (output l))

/-- The Keccak-f relation of a table's rows: the middle lanes are twelve rounds of the input lanes,
and the output lanes twelve rounds of the middle lanes. -/
def KeccakRelation (p : ℕ) (w : Witness K S.tables.length) (t : Fin S.tables.length)
    (slot : Fin 64 → ℕ) (output : Fin 25 → ℕ) : Prop :=
  Keccak.Gkr.InputRelation (ofK g) (witnessOutputs p w t output) (witnessBits p w t slot)

/-- The output lane word of a row: the last twelve rounds of its middle lanes. -/
noncomputable def outputWord {p : ℕ} (bits : Keccak.Gkr.Witness p) (b : Fin (2 ^ (p + 4)))
    (l : Fin 25) : K :=
  ∑ z : Fin 64, ZMod.castHom (dvd_refl 2) K
    (Keccak.Gkr.segmentState bits b 1 12 (by omega) ⟨z.val + 64 * l.val, by omega⟩) * g ^ z.val

/-- An output lane word embeds as the GKR's lane value. -/
theorem ofK_outputWord {p : ℕ} (bits : Keccak.Gkr.Witness p) (b : Fin (2 ^ (p + 4))) (l : Fin 25) :
    ofK (outputWord bits b l) = Keccak.Gkr.laneValue (ofK g)
      (fun z ↦ Keccak.Gkr.segmentState bits b 1 12 (by omega) ⟨z.val + 64 * l.val, by omega⟩) := by
  unfold outputWord Keccak.Gkr.laneValue
  change algebraMap K E _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_mul, map_pow]
  congr 1

variable (S) (L : Layout S.tables.length) (M : ℕ)

/-- A Keccak table of a system, with its slots stacked as one aligned region of a stack on `M`
variables, and the system's external relation its Keccak-f relation. -/
structure KeccakTable where
  /-- The table. -/
  table : Fin S.tables.length
  /-- Its rows are `2 ^ (p + 4)` permutations. -/
  p : ℕ
  /-- The table's height. -/
  height : L.logHeight table = p + 4
  /-- The 64 committed slot columns: input lanes, middle lanes, fourteen further columns. -/
  slot : Fin 64 → ℕ
  /-- The 25 virtual output lane columns. -/
  output : Fin 25 → ℕ
  /-- The stack index of slot 0. -/
  first : ℕ
  /-- The slots are stacked in order from `first`. -/
  stacked : ∀ j : Fin 64, ∃ h : first + j.val < (S.stackColumns L).length,
    (S.stackColumns L)[first + j.val] = (table, slot j)
  /-- The slots' region is aligned to its size. -/
  aligned : 2 ^ (p + 10) ∣ (S.stackBlocks L).offsetNat first
  /-- The region fits the stack. -/
  fits : (S.stackBlocks L).offsetNat first + 2 ^ (p + 10) ≤ 2 ^ M
  /-- The output lanes are columns of the table. -/
  output_lt : ∀ l, output l < (S.table table).air.width
  /-- Distinct lanes have distinct columns. -/
  output_injective : Function.Injective output
  /-- The virtual columns are exactly the Keccak table's output lanes. -/
  virtual_iff : ∀ t c, c ∈ (S.table t).virtual ↔ t = table ∧ ∃ l, output l = c
  /-- The system's external relation is the Keccak-f relation of the table. -/
  external_iff : ∀ w, S.external w ↔ KeccakRelation p w table slot output

namespace KeccakTable

variable {S L M} (kt : KeccakTable S L M)

/-- A slot column is committed. -/
theorem slot_committed (j : Fin 64) : kt.slot j ∈ S.committedColumns kt.table := by
  obtain ⟨h, hget⟩ := kt.stacked j
  have := (S.mem_stackColumns L kt.table (kt.slot j)).mp (hget ▸ List.getElem_mem h)
  exact this

/-- The lane of an output column. -/
def outputLane (c : ℕ) : Option (Fin 25) := (List.finRange 25).find? (kt.output · = c)

/-- A unique member satisfying a predicate is what a list search finds. -/
theorem find?_unique {A : Type} (predicate : A → Bool) (list : List A) (value : A)
    (member : value ∈ list) (matching : predicate value = true)
    (unique : ∀ other ∈ list, predicate other = true → other = value) :
    list.find? predicate = some value := by
  induction list with
  | nil => cases member
  | cons head tail ih =>
      by_cases yes : predicate head = true
      · rw [List.find?_cons_of_pos yes, unique head (List.mem_cons_self ..) yes]
      · rw [List.find?_cons_of_neg yes]
        apply ih
        · obtain same | member := List.mem_cons.mp member
          · exact False.elim (yes (same ▸ matching))
          · exact member
        · intro other member
          exact unique other (List.mem_cons_of_mem head member)

/-- The lane of a lane's column is the lane. -/
theorem outputLane_output (l : Fin 25) : kt.outputLane (kt.output l) = some l :=
  find?_unique _ _ l (List.mem_finRange l) (by simp only [decide_true])
    (fun l' _ h ↦ kt.output_injective (of_decide_eq_true h))

/-- A column that is no output lane has no lane. -/
theorem outputLane_none (c : ℕ) (hc : ∀ l, kt.output l ≠ c) : kt.outputLane c = none := by
  unfold outputLane
  rw [List.find?_eq_none]
  intro l _
  simp only [decide_eq_true_eq]
  exact hc l

/-- The Keccak-f GKR's witness read off a stack. -/
def bits (q : Whir.Table K M) : Keccak.Gkr.Witness kt.p :=
  witnessBits kt.p (S.read L M q) kt.table kt.slot

/-- The witness read off a stack: the stack's committed columns, and each output lane computed
from the middle lanes. -/
noncomputable def interpret (q : Whir.Table K M) : Witness K S.tables.length := fun t ↦
  if h : t = kt.table then
    List.ofFn fun b : Fin (2 ^ L.logHeight t) ↦ Array.ofFn fun c : Fin (S.table t).air.width ↦
      match kt.outputLane c.val with
      | some l => outputWord (kt.bits q)
          ⟨b.val, by rw [← (congrArg L.logHeight h).trans kt.height]; exact b.isLt⟩ l
      | none => S.readCell L M q t b.val c.val
  else S.read L M q t

/-- An interpreted witness has the system's shape. -/
theorem interpret_shaped (q : Whir.Table K M) : S.Shaped L (kt.interpret q) := by
  intro t
  unfold interpret
  split
  · refine ⟨by simp only [List.length_ofFn], ?_⟩
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp only [Array.size_ofFn]
  · exact S.read_shaped L M q t

/-- An interpreted witness's cells: an output lane's word, or the stack's. -/
theorem interpret_cell (q : Whir.Table K M) (t : Fin S.tables.length) (b c : ℕ)
    (hb : b < 2 ^ L.logHeight t) (hc : c < (S.table t).air.width) :
    ((kt.interpret q t).getD b #[]).getD c 0 =
      if h : t = kt.table then
        match kt.outputLane c with
        | some l => outputWord (kt.bits q)
            ⟨b, by rw [← (congrArg L.logHeight h).trans kt.height]; exact hb⟩ l
        | none => S.readCell L M q t b c
      else S.readCell L M q t b c := by
  unfold interpret
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn, hb]), List.getElem_ofFn,
      Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hc, ↓reduceDIte, Option.getD_some]
  · exact read_cell S L M q t b c hb hc

/-- A committed cell of an interpreted witness is the stack's. -/
theorem interpret_committed (q : Whir.Table K M) (t : Fin S.tables.length) (b c : ℕ)
    (hc : c ∈ S.committedColumns t) :
    ((kt.interpret q t).getD b #[]).getD c 0 = ((S.read L M q t).getD b #[]).getD c 0 := by
  have hcw : c < (S.table t).air.width := List.mem_range.mp (List.mem_filter.mp hc).1
  have hnv : c ∉ (S.table t).virtual := by
    intro hv
    have h2 := (List.mem_filter.mp hc).2
    rw [List.contains_iff_mem.mpr hv] at h2
    exact absurd h2 (by decide)
  by_cases hb : b < 2 ^ L.logHeight t
  · rw [interpret_cell kt q t b c hb hcw, read_cell S L M q t b c hb hcw]
    split
    · rename_i h
      rw [kt.outputLane_none c (fun l hl ↦ hnv ((kt.virtual_iff t c).mpr ⟨h, l, hl⟩))]
    · rfl
  · have h1 : (kt.interpret q t).getD b #[] = #[] := by
      rw [List.getD_eq_default _ _ (by
        have := (kt.interpret_shaped q t).1
        omega)]
    have h2 : (S.read L M q t).getD b #[] = #[] := by
      rw [List.getD_eq_default _ _ (by
        have := (S.read_shaped L M q t).1
        omega)]
    rw [h1, h2]

end KeccakTable

end CompStark.Tables.Composed
