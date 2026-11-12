/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Basic
public import CompStark.Tables.Fingerprint

/-! The bus relation of a set of tables as one multiset equality, and its fingerprint test.

Every tuple is encoded with the index of its bus first, padded with zeros to `2 ^ k` entries;
`BusShape` asks that the tuples of a bus have one width and that the encodings fit. Then every
bus balances exactly when the multisets of encoded pushes and pulls are equal (`balanced_iff`),
and an unbalanced set of tables passes the grand-product test at a uniform `(α, β)` with
probability at most `max 1 k · cap / |E|` (`unbalanced_collision_le`). -/

@[expose] public section

namespace CompStark.Tables

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear OracleComp

/-- A bus index followed by a tuple, padded with zeros to `2 ^ k` entries. -/
def encode (k i : ℕ) (tuple : List K) : Vector K (2 ^ k) :=
  Vector.ofFn fun j ↦ (K.ofBits i :: tuple).getD j.val 0

/-- The bus index of an encoding: its first entry. -/
def head {k : ℕ} (v : Vector K (2 ^ k)) : K := v.toList.getD 0 0

/-- The tuple of length `n` of an encoding. -/
def decode (k n : ℕ) (v : Vector K (2 ^ k)) : List K := (v.toList.drop 1).take n

/-- Decoding recovers a tuple of length `n` whose encoding fits. -/
theorem decode_encode (k i : ℕ) (tuple : List K) (hfit : 1 + tuple.length ≤ 2 ^ k) :
    decode k tuple.length (encode k i tuple) = tuple := by
  apply List.ext_getElem
  · simp only [decode, encode, Vector.toList_ofFn, List.length_take, List.length_drop,
      List.length_ofFn]
    omega
  · intro j hj _
    simp only [decode, encode, Vector.toList_ofFn, List.length_take, List.length_drop,
      List.length_ofFn] at hj
    simp only [decode, encode, Vector.toList_ofFn, List.getElem_take, List.getElem_drop,
      List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_cons]; omega)]
    simp only [Nat.add_comm 1 j, List.getElem_cons_succ]

/-- The head of an encoding is its bus index. -/
theorem head_encode (k i : ℕ) (tuple : List K) : head (encode k i tuple) = K.ofBits i := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  simp only [head, encode, Vector.toList_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hk), List.getElem_ofFn]
  rfl

/-- Bus indices below `2 ^ 64` have distinct encodings. -/
theorem ofBits_injective {i j : ℕ} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : K.ofBits i = K.ofBits j) : i = j := by
  have hv := congrArg BF64.toBitVec h
  simp only [K.ofBits, BF64.toBitVec_ofBitVec] at hv
  have := congrArg BitVec.toNat hv
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

namespace System

variable (S : System K)

/-- A bus's position among the buses. -/
def busIndex (b : String) : ℕ := S.buses.idxOf b

/-- Every bus has one tuple width, its encodings fit `2 ^ k` entries, and there are fewer than
`2 ^ 64` buses. -/
def BusShape (k : ℕ) (width : String → ℕ) : Prop :=
  S.buses.length < 2 ^ 64 ∧ (∀ b ∈ S.buses, 1 + width b ≤ 2 ^ k) ∧
  ∀ T ∈ S.tables, ∀ I ∈ T.interactions, I.tuple.length = width I.bus

/-- All pushed (`push = true`) or pulled tuples, encoded. -/
def encoded (k : ℕ) (L : Layout S.tables.length) (w : Witness K S.tables.length) (push : Bool) :
    Multiset (Vector K (2 ^ k)) :=
  (S.buses.map fun b ↦ (S.tuples L w b push).map (encode k (S.busIndex b))).sum

/-- Every emitted tuple has its bus's width. -/
theorem tuples_length {k : ℕ} {width : String → ℕ} (h : S.BusShape k width)
    (L : Layout S.tables.length) (w : Witness K S.tables.length) (b : String) (push : Bool) :
    ∀ x ∈ S.tuples L w b push, x.length = width b := by
  intro x hx
  simp only [tuples, Multiset.mem_coe, List.mem_flatMap, List.mem_finRange, true_and,
    tableTuples, List.mem_range, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq] at hx
  obtain ⟨t, i, -, I, ⟨hI, hb, -⟩, rfl⟩ := hx
  rw [List.length_map, h.2.2 _ (List.getElem_mem _) I hI, hb]

/-- A filter distributes over a list's sum of multisets. -/
theorem filter_list_sum {α β : Type} (p : α → Prop) [DecidablePred p] (l : List β)
    (f : β → Multiset α) : (l.map f).sum.filter p = (l.map fun b ↦ (f b).filter p).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, Multiset.filter_zero]
  | cons b l ih => simp only [List.map_cons, List.sum_cons, Multiset.filter_add, ih]

/-- In a list without duplicates, a sum selecting one member is that member's term. -/
theorem sum_select {α β : Type} [DecidableEq β] (l : List β) (hl : l.Nodup) (b : β) (hb : b ∈ l)
    (x : Multiset α) : (l.map fun b' ↦ if b' = b then x else 0).sum = x := by
  induction l with
  | nil => cases hb
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · have : (l.map fun b' ↦ if b' = b then x else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
        have : c ≠ b := fun h ↦ (List.nodup_cons.mp hl).1 (h ▸ hc)
        simp only [this, ↓reduceIte]
      simp only [↓reduceIte, this, add_zero]
    · have hab : a ≠ b := fun h ↦ (List.nodup_cons.mp hl).1 (h ▸ hb')
      simp only [hab, ↓reduceIte, zero_add, ih (List.nodup_cons.mp hl).2 hb']

/-- Keeping the encodings whose head is a bus's index keeps exactly that bus's tuples. -/
theorem filter_encoded {k : ℕ} {width : String → ℕ} (h : S.BusShape k width)
    (L : Layout S.tables.length) (w : Witness K S.tables.length) (push : Bool)
    (b : String) (hb : b ∈ S.buses) (hk : 0 < 2 ^ k) :
    (S.encoded k L w push).filter (fun v ↦ head v = K.ofBits (S.busIndex b)) =
      (S.tuples L w b push).map (encode k (S.busIndex b)) := by
  have nodup : S.buses.Nodup := List.nodup_dedup _
  unfold encoded
  rw [filter_list_sum]
  have each : ∀ b' ∈ S.buses,
      ((S.tuples L w b' push).map (encode k (S.busIndex b'))).filter
          (fun v ↦ head v = K.ofBits (S.busIndex b)) =
        if b' = b then (S.tuples L w b push).map (encode k (S.busIndex b)) else 0 := by
    intro b' hb'
    rw [Multiset.filter_map]
    by_cases e : b' = b
    · subst e
      simp only [↓reduceIte, Function.comp_def, head_encode k _ _, Multiset.filter_true]
    · simp only [e, ↓reduceIte, Function.comp_def, head_encode k _ _]
      rw [Multiset.map_eq_zero]
      apply Multiset.filter_eq_nil.mpr
      intro x _ hx
      have hi := ofBits_injective
        (lt_of_lt_of_le (List.idxOf_lt_length_of_mem hb') h.1.le)
        (lt_of_lt_of_le (List.idxOf_lt_length_of_mem hb) h.1.le) hx
      exact e ((List.idxOf_inj hb').mp hi)
  rw [List.map_congr_left each]
  exact sum_select _ nodup b hb _

/-- Every bus balances exactly when the encoded pushes and pulls are equal. -/
theorem balanced_iff {k : ℕ} {width : String → ℕ} (h : S.BusShape k width)
    (L : Layout S.tables.length) (w : Witness K S.tables.length) :
    (∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) ↔
      S.encoded k L w true = S.encoded k L w false := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  constructor
  · intro bal
    unfold encoded
    exact congrArg List.sum (List.map_congr_left fun b hb ↦ by rw [bal b hb])
  · intro eq b hb
    have filtered := congrArg (Multiset.filter (fun v ↦ head v = K.ofBits (S.busIndex b))) eq
    rw [S.filter_encoded h L w true b hb hk, S.filter_encoded h L w false b hb hk] at filtered
    have decoded := congrArg (Multiset.map (decode k (width b))) filtered
    have back (push : Bool) : ((S.tuples L w b push).map (encode k (S.busIndex b))).map
        (decode k (width b)) = S.tuples L w b push := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id (S.tuples L w b push)]
      apply Multiset.map_congr rfl
      intro x hx
      have hlen := S.tuples_length h L w b push x hx
      simp only [Function.comp_apply, id]
      rw [← hlen]
      exact decode_encode k _ x (hlen ▸ h.2.1 b hb)
    rwa [back, back] at decoded

/-- An unbalanced set of tables with at most `cap` pushed and pulled tuples passes the
grand-product test with probability at most `max 1 k · cap / |E|`. -/
theorem unbalanced_collision_le {k : ℕ} {width : String → ℕ} (h : S.BusShape k width)
    (L : Layout S.tables.length) (w : Witness K S.tables.length) (cap : ℕ)
    (hpush : (S.encoded k L w true).card ≤ cap) (hpull : (S.encoded k L w false).card ≤ cap)
    (unbalanced : ¬ ∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) :
    Pr{let ab ← ($ᵗ ((Fin k → E) × E))}[
      sideProduct k ab.1 ab.2 (S.encoded k L w true) =
        sideProduct k ab.1 ab.2 (S.encoded k L w false)] ≤ overE (max 1 k * cap) :=
  sideProduct_collision_le k _ _ cap (fun e ↦ unbalanced ((S.balanced_iff h L w).mpr e))
    hpush hpull

/-- A balanced set of tables passes the grand-product test at every `(α, β)`. -/
theorem balanced_sideProduct {k : ℕ} {width : String → ℕ} (h : S.BusShape k width)
    (L : Layout S.tables.length) (w : Witness K S.tables.length)
    (bal : ∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) (α : Fin k → E) (β : E) :
    sideProduct k α β (S.encoded k L w true) = sideProduct k α β (S.encoded k L w false) := by
  rw [(S.balanced_iff h L w).mp bal]

end System

end CompStark.Tables

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields

variable (S : System K)

/-- Every row and interaction that emits on a side: table, row and interaction. -/
def emitted (L : Layout S.tables.length) (push : Bool) :
    Multiset (Fin S.tables.length × ℕ × Interaction K) :=
  ((List.finRange S.tables.length).flatMap fun t ↦ (List.range (L.executed t)).flatMap fun i ↦
    ((S.table t).interactions.filter (·.push == push)).map fun I ↦ (t, i, I) : List _)

/-- The tuple an emission carries. -/
def emittedTuple (L : Layout S.tables.length) (w : Witness K S.tables.length)
    (x : Fin S.tables.length × ℕ × Interaction K) : List K :=
  x.2.2.tuple.map (Expr.eval (S.env L w x.1 x.2.1))

/-- A bus's tuples are the tuples of the emissions on it. -/
theorem tuples_eq_emitted (L : Layout S.tables.length) (w : Witness K S.tables.length)
    (b : String) (push : Bool) :
    S.tuples L w b push = ((S.emitted L push).filter (·.2.2.bus = b)).map (S.emittedTuple L w) := by
  simp only [tuples, emitted, tableTuples, Multiset.filter_coe, Multiset.map_coe,
    List.filter_flatMap, List.map_flatMap, List.filter_map, List.map_map, List.map_filter]
  congr 1
  apply List.flatMap_congr
  intro t _
  apply List.flatMap_congr
  intro i _
  rw [List.filter_filter]
  simp only [Function.comp_def, emittedTuple, Bool.and_comm, decide_eq_true_eq, beq_iff_eq]
  rfl

/-- Every emission's bus is a bus of the system. -/
theorem emitted_bus (L : Layout S.tables.length) (push : Bool) :
    ∀ x ∈ S.emitted L push, x.2.2.bus ∈ S.buses := by
  intro x hx
  simp only [emitted, Multiset.mem_coe, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_range, List.mem_map, List.mem_filter] at hx
  obtain ⟨t, i, -, I, ⟨hI, -⟩, rfl⟩ := hx
  exact List.mem_dedup.mpr (List.mem_flatMap.mpr
    ⟨S.table t, List.getElem_mem _, List.mem_map.mpr ⟨I, hI, rfl⟩⟩)

/-- Splitting a multiset by a key over a list of all keys, each once, recovers it. -/
theorem sum_filter_key {α β : Type} [DecidableEq β] (B : List β) (hB : B.Nodup) (key : α → β)
    (M : Multiset α) (hM : ∀ x ∈ M, key x ∈ B) :
    (B.map fun b ↦ M.filter (key · = b)).sum = M := by
  induction M using Multiset.induction_on with
  | empty => simp only [Multiset.filter_zero, List.map_const', List.sum_replicate, nsmul_zero]
  | cons a M ih =>
    have split : ∀ b ∈ B, (a ::ₘ M).filter (key · = b) =
        (if key a = b then {a} else 0) + M.filter (key · = b) := by
      intro b _
      by_cases h : key a = b
      · simp only [Multiset.filter_cons, h, ↓reduceIte, Multiset.singleton_add]
      · simp only [Multiset.filter_cons, h, ↓reduceIte, zero_add]
    rw [List.map_congr_left split, List.sum_map_add, ih fun x hx ↦ hM x (Multiset.mem_cons_of_mem hx)]
    have pick : (B.map fun b ↦ if key a = b then ({a} : Multiset α) else 0).sum = {a} := by
      exact (congrArg List.sum (List.map_congr_left fun b _ ↦
        if_congr ⟨Eq.symm, Eq.symm⟩ rfl rfl)).trans
        (sum_select B hB (key a) (hM a (Multiset.mem_cons_self a M)) ({a} : Multiset α))
    rw [pick, Multiset.singleton_add]

/-- The encoded pushes or pulls are the encodings of all emissions. -/
theorem encoded_eq_emitted (k : ℕ) (L : Layout S.tables.length) (w : Witness K S.tables.length)
    (push : Bool) :
    S.encoded k L w push = (S.emitted L push).map fun x ↦
      encode k (S.busIndex x.2.2.bus) (S.emittedTuple L w x) := by
  unfold encoded
  have each : ∀ b ∈ S.buses, (S.tuples L w b push).map (encode k (S.busIndex b)) =
      ((S.emitted L push).filter (·.2.2.bus = b)).map fun x ↦
        encode k (S.busIndex x.2.2.bus) (S.emittedTuple L w x) := by
    intro b _
    rw [tuples_eq_emitted, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    rw [(Multiset.mem_filter.mp hx).2]
    rfl
  rw [List.map_congr_left each]
  conv_rhs => rw [← sum_filter_key S.buses (List.nodup_dedup _) (·.2.2.bus) (S.emitted L push)
    (S.emitted_bus L push)]
  induction S.buses with
  | nil => simp only [List.map_nil, List.sum_nil, Multiset.map_zero]
  | cons b B ih => simp only [List.map_cons, List.sum_cons, Multiset.map_add, ih]

end CompStark.Tables.System
