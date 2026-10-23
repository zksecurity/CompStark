/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgCorrect

/-! # Register allocation is correct

The allocator (`allocate`) walks the schedule keeping, for every register, the node it holds
(`owner`), and for every node its register (`loc`). Running the code it emits on a row
(`fieldMachine`) keeps an invariant (`AllocInv`): a register holding a node holds the node's
value, and every computed node that a later step reads is held in its register. A node's register
is released only at its last read (`lastUses`), and a computed node takes a free register. So
every instruction reads its operands' values, and the run accumulates the scheduled nodes' values
with their weights (`allocate_run`).
-/

@[expose] public section
namespace CompStark.Stark.Prog

variable {F : Type}

namespace Alloc

/-! ### The allocator's operations -/

/-- The node register `r` holds. -/
def own (s : Alloc F) (r : Nat) : Option Nat := s.owner.getD r none

/-- The register of node `j`. -/
def locOf (s : Alloc F) (j : Nat) : Nat := s.loc.getD j 0

theorem getD_set! {α : Type} (a : Array α) (i j : Nat) (v d : α) :
    (a.set! i v).getD j d = if i = j ∧ i < a.size then v else a.getD j d := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h
    by_cases h' : i < a.size
    · simp only [h', ite_true, and_self, Option.getD_some]
    · simp only [h', ite_false, and_false, Array.getElem?_eq_none (Nat.le_of_not_lt h'),
        ite_self]
  · simp only [h, ite_false, false_and]

theorem getD_push {α : Type} (a : Array α) (j : Nat) (v d : α) :
    (a.push v).getD j d = if j = a.size then v else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem default_nat : (default : Nat) = 0 := rfl

theorem owner_some {s : Alloc F} {r j : Nat} :
    s.owner[r]? = some (some j) ↔ r < s.owner.size ∧ s.own r = some j := by
  simp only [own, Array.getD_eq_getD_getElem?]
  constructor
  · intro h
    have hr : r < s.owner.size := by
      rcases Nat.lt_or_ge r s.owner.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h
        exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    rw [h]
    exact ⟨hr, rfl⟩
  · rintro ⟨hr, h⟩
    rw [Array.getElem?_eq_getElem hr] at h ⊢
    simp only [Option.getD_some] at h
    rw [h]

theorem own_some_lt {s : Alloc F} {r j : Nat} (h : s.own r = some j) : r < s.owner.size := by
  rcases Nat.lt_or_ge r s.owner.size with h1 | h1
  · exact h1
  · simp only [own, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h1, Option.getD_none,
      reduceCtorEq] at h

/-- Releasing node `j`: its register is freed if it holds `j`. -/
theorem release_eq (s : Alloc F) (j : Nat) : s.release j =
    if s.own (s.locOf j) = some j then
      ⟨s.owner.set! (s.locOf j) none, s.locOf j :: s.free, s.loc, s.code⟩
    else s := by
  obtain ⟨owner, free, loc, code⟩ := s
  simp only [release, Array.getElem!_eq_getD, default_nat]
  by_cases h : owner.getD (loc.getD j 0) none = some j
  · have h' : owner[loc.getD j 0]? = some (some j) :=
      (owner_some (s := ⟨owner, free, loc, code⟩)).mpr ⟨own_some_lt (s := ⟨owner, free, loc, code⟩)
        h, h⟩
    simp only [own, locOf, h, h', ite_true]
  · have h' : ¬owner[loc.getD j 0]? = some (some j) := fun h' ↦
      h ((owner_some (s := ⟨owner, free, loc, code⟩)).mp h').2
    simp only [own, locOf, h, h', ite_false]

theorem release_loc (s : Alloc F) (j : Nat) : (s.release j).loc = s.loc := by
  rw [release_eq]; split <;> rfl

theorem release_code (s : Alloc F) (j : Nat) : (s.release j).code = s.code := by
  rw [release_eq]; split <;> rfl

theorem release_size (s : Alloc F) (j : Nat) : (s.release j).owner.size = s.owner.size := by
  rw [release_eq]; split
  · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  · rfl

theorem release_own (s : Alloc F) (j r : Nat) :
    (s.release j).own r = if r = s.locOf j ∧ s.own r = some j then none else s.own r := by
  rw [release_eq]
  split
  · rename_i hj
    show (s.owner.set! (s.locOf j) none).getD r none = _
    rw [Alloc.getD_set!]
    by_cases hr : r = s.locOf j
    · subst hr
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, own_some_lt hj⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hj⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hr h.1.symm),
        ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hr h.1)]
      rfl
  · rename_i hj
    split
    · rename_i h'
      obtain ⟨hr, h''⟩ := h'
      subst hr
      exact absurd h'' hj
    · rfl

theorem release_free (s : Alloc F) (j r : Nat) :
    r ∈ (s.release j).free ↔ r ∈ s.free ∨ (r = s.locOf j ∧ s.own r = some j) := by
  rw [release_eq]
  split
  · rename_i hj
    simp only [List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨h, by rw [h]; exact hj⟩
      · exact Or.inl h
    · rintro (h | ⟨h, -⟩)
      · exact Or.inr h
      · exact Or.inl h
  · rename_i hj
    constructor
    · exact Or.inl
    · rintro (h' | ⟨hr, h''⟩)
      · exact h'
      · subst hr
        exact absurd h'' hj

theorem release_nodup (s : Alloc F) (j : Nat) (hn : s.free.Nodup)
    (hf : ∀ r ∈ s.free, s.own r = none) : (s.release j).free.Nodup := by
  rw [release_eq]
  split
  · rename_i hj
    refine List.nodup_cons.mpr ⟨fun hm ↦ ?_, hn⟩
    rw [hf _ hm] at hj
    exact absurd hj (by simp only [reduceCtorEq, not_false_eq_true])
  · exact hn

/-- Taking a register for node `i`: the first free one, or a new one. -/
theorem take_eq (s : Alloc F) (i : Nat) : s.take i =
    match s.free with
    | r :: rest => (⟨s.owner.set! r (some i), rest, s.loc.set! i r, s.code⟩, r)
    | [] => (⟨s.owner.push (some i), [], s.loc.set! i s.owner.size, s.code⟩, s.owner.size) := by
  obtain ⟨owner, free, loc, code⟩ := s
  cases free <;> rfl

theorem take_loc (s : Alloc F) (i : Nat) :
    (s.take i).1.loc = s.loc.set! i (s.take i).2 := by
  rw [take_eq]; split <;> rfl

theorem take_code (s : Alloc F) (i : Nat) : (s.take i).1.code = s.code := by
  rw [take_eq]; split <;> rfl

theorem take_free (s : Alloc F) (i : Nat) : (s.take i).1.free = s.free.tail := by
  rw [take_eq]; split <;> rename_i h <;> simp only [h, List.tail_cons, List.tail_nil]

theorem take_own (s : Alloc F) (i r : Nat) (hf : ∀ r ∈ s.free, r < s.owner.size) :
    (s.take i).1.own r = if r = (s.take i).2 then some i else s.own r := by
  rw [take_eq]
  split
  · rename_i r0 rest h
    simp only [own]
    rw [Alloc.getD_set!]
    have := hf r0 (by rw [h]; exact List.mem_cons_self)
    by_cases hr : r = r0
    · subst hr; simp only [this, and_self, ite_true]
    · simp only [Ne.symm hr, false_and, ite_false, hr]
  · simp only [own]
    rw [getD_push]

/-- The register taken is free or new. -/
theorem take_fresh (s : Alloc F) (i : Nat) :
    ((s.take i).2 ∈ s.free ∧ (s.take i).1.owner.size = s.owner.size) ∨
      ((s.take i).2 = s.owner.size ∧ (s.take i).1.owner.size = s.owner.size + 1) := by
  rw [take_eq]
  split
  · rename_i r0 rest h
    left
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h, List.mem_cons_self,
      and_self]
  · right
    simp only [Array.size_push, and_self]

theorem emit_code (s : Alloc F) (ins : Instr F) : (s.emit ins).code = s.code.push ins := by
  obtain ⟨owner, free, loc, code⟩ := s; rfl
theorem emit_owner (s : Alloc F) (ins : Instr F) : (s.emit ins).owner = s.owner := by
  obtain ⟨owner, free, loc, code⟩ := s; rfl
theorem emit_free (s : Alloc F) (ins : Instr F) : (s.emit ins).free = s.free := by
  obtain ⟨owner, free, loc, code⟩ := s; rfl
theorem emit_loc (s : Alloc F) (ins : Instr F) : (s.emit ins).loc = s.loc := by
  obtain ⟨owner, free, loc, code⟩ := s; rfl

end Alloc

/-! ### The schedule -/

/-- Node `j` is computed into a register. -/
def InReg (nodes : Array (Node F)) (j : Nat) : Prop :=
  match nodes[j]? with
  | some (.load _) | some (.scalar _) | some (.bin ..) => True
  | _ => False

/-- The nodes read at step `t`; after the last step, the outputs. -/
def readsAt (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat) (t : Nat) :
    List Nat :=
  if h : t < steps.size then steps[t].reads nodes
  else if t = steps.size then outs.toList else []

/-- Node `j` is computed at a step before `t`. -/
def Computed (steps : Array Step) (t j : Nat) : Prop := ∃ t' < t, steps[t']? = some (Step.node j)

/-- A schedule of well-formed nodes: every step computes a node once, and every node a step reads
is computed before it unless it is a column or a constant. -/
structure SchedOk (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat) : Prop where
  node_lt : ∀ (t i : Nat), steps[t]? = some (Step.node i) → i < nodes.size
  once : ∀ (t i : Nat), steps[t]? = some (Step.node i) → ¬Computed steps t i
  reads : ∀ (t j : Nat), j ∈ readsAt nodes steps outs t →
    j < nodes.size ∧ (InReg nodes j → Computed steps t j)
  before : ∀ (i : Nat) (n : Node F), nodes[i]? = some n → n.Before i

/-- An operand's register is below `n`. -/
def Opd.RegsLt (n : Nat) : Opd F → Prop
  | .reg r => r < n
  | _ => True

/-- An instruction's registers are below `n`. -/
def Instr.RegsLt (n : Nat) : Instr F → Prop
  | .load d _ | .scalar d _ => d < n
  | .bin _ d a b => d < n ∧ a.RegsLt n ∧ b.RegsLt n
  | .acc a _ => a.RegsLt n

theorem Opd.RegsLt.mono {o : Opd F} {n n' : Nat} (h : o.RegsLt n) (hn : n ≤ n') :
    o.RegsLt n' := by
  cases o with
  | reg r => exact Nat.lt_of_lt_of_le h hn
  | cur c => trivial
  | const x => trivial

theorem Instr.RegsLt.mono {i : Instr F} {n n' : Nat} (h : i.RegsLt n) (hn : n ≤ n') :
    i.RegsLt n' := by
  cases i with
  | load d s => exact Nat.lt_of_lt_of_le h hn
  | scalar d k => exact Nat.lt_of_lt_of_le h hn
  | bin o d a b => exact ⟨Nat.lt_of_lt_of_le h.1 hn, h.2.1.mono hn, h.2.2.mono hn⟩
  | acc a w => exact Opd.RegsLt.mono (o := a) (n := n) h hn

/-! ### Ownership -/

theorem Alloc.own_take (s : Alloc F) (i : Nat) (hf : ∀ r ∈ s.free, s.own r = none) :
    s.own (s.take i).2 = none := by
  rcases s.take_fresh i with ⟨h, -⟩ | ⟨h, -⟩
  · exact hf _ h
  · rw [h]
    simp only [Alloc.own, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_refl _),
      Option.getD_none]

theorem Alloc.take_not_mem (s : Alloc F) (i : Nat) (hn : s.free.Nodup) :
    (s.take i).2 ∉ (s.take i).1.free := by
  rw [Alloc.take_eq]
  split
  · rename_i r rest h
    rw [h] at hn
    exact (List.nodup_cons.mp hn).1
  · exact List.not_mem_nil

theorem Alloc.take_size_le (s : Alloc F) (i : Nat) : s.owner.size ≤ (s.take i).1.owner.size := by
  rcases s.take_fresh i with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem Alloc.take_lt (s : Alloc F) (i : Nat) (hf : ∀ r ∈ s.free, r < s.owner.size) :
    (s.take i).2 < (s.take i).1.owner.size := by
  rcases s.take_fresh i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]; exact hf _ h1
  · omega

theorem run_push {σ : Type} (M : Machine F σ) (code : Array (Instr F)) (ins : Instr F) (s : σ) :
    run M (code.push ins) s = ins.exec M (run M code s) := by
  simp only [run, Array.foldl_push]

section Need
variable (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat)

/-- Node `j` is read at step `t` or later. -/
def Need (t j : Nat) : Prop := ∃ t', t ≤ t' ∧ j ∈ readsAt nodes steps outs t'

variable {nodes steps outs}

theorem need_succ {t j : Nat} (h : Need nodes steps outs (t + 1) j) :
    Need nodes steps outs t j := by
  obtain ⟨t', h1, h2⟩ := h
  exact ⟨t', by omega, h2⟩

/-- A node whose last read is at step `t` is not needed after it. -/
theorem not_need {last : Array Nat}
    (hlast : ∀ t j, j ∈ readsAt nodes steps outs t → t ≤ last[j]!) {t j : Nat}
    (hj : last[j]! = t) : ¬Need nodes steps outs (t + 1) j := by
  rintro ⟨t', h1, h2⟩
  have := hlast t' j h2
  omega

end Need

section Own
variable [Field F]

/-- The allocator's state `s` on a row's run state `st`: a register holding a node holds its
value, the free registers are distinct and hold nothing, and every node `need`ed and computed
(`comp`) is held in its register. -/
structure Good (ctx : Ctx F) (nodes : Array (Node F)) (need comp : Nat → Prop) (s : Alloc F)
    (st : St F) : Prop where
  loc : s.loc.size = nodes.size
  owned : ∀ r j, s.own r = some j →
    InReg nodes j ∧ comp j ∧ s.locOf j = r ∧ st.reg r = val ctx nodes j
  nodup : s.free.Nodup
  free : ∀ r ∈ s.free, r < s.owner.size ∧ s.own r = none
  ready : ∀ j, InReg nodes j → comp j → need j → s.own (s.locOf j) = some j

theorem Good.weaken {ctx : Ctx F} {nodes : Array (Node F)} {need need' comp : Nat → Prop}
    {s : Alloc F} {st : St F} (h : Good ctx nodes need comp s st)
    (hn : ∀ j, need' j → need j) : Good ctx nodes need' comp s st :=
  ⟨h.loc, h.owned, h.nodup, h.free, fun j h1 h2 h3 ↦ h.ready j h1 h2 (hn j h3)⟩

/-- Releasing a node no longer needed. -/
theorem Good.release {ctx : Ctx F} {nodes : Array (Node F)} {need comp : Nat → Prop}
    {s : Alloc F} {st : St F} (h : Good ctx nodes need comp s st) (j : Nat) (hj : ¬need j) :
    Good ctx nodes need comp (s.release j) st := by
  refine ⟨by rw [Alloc.release_loc]; exact h.loc, fun r j' hr ↦ ?_,
    Alloc.release_nodup s j h.nodup fun r hr ↦ (h.free r hr).2, fun r hr ↦ ?_,
    fun j' h1 h2 h3 ↦ ?_⟩
  · rw [Alloc.release_own] at hr
    split at hr
    · exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
    · have := h.owned r j' hr
      have hl : (s.release j).locOf j' = s.locOf j' := by
        simp only [Alloc.locOf, Alloc.release_loc]
      rw [hl]
      exact this
  · rw [Alloc.release_free] at hr
    rw [Alloc.release_size, Alloc.release_own]
    rcases hr with hr | ⟨hr, hj'⟩
    · obtain ⟨h1, h2⟩ := h.free r hr
      refine ⟨h1, ?_⟩
      split
      · rfl
      · exact h2
    · refine ⟨Alloc.own_some_lt hj', ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hr, hj'⟩)]
  · have hown := h.ready j' h1 h2 h3
    have hl : (s.release j).locOf j' = s.locOf j' := by
      simp only [Alloc.locOf, Alloc.release_loc]
    rw [hl, Alloc.release_own]
    split
    · rename_i hc
      obtain ⟨-, hc⟩ := hc
      rw [hown] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      exact absurd h3 hj
    · exact hown

/-- Releasing the nodes of `js` whose last step is `t`, none of them needed. -/
theorem Good.releaseLast {ctx : Ctx F} {nodes : Array (Node F)} {need comp : Nat → Prop}
    (last : Array Nat) (t : Nat) :
    ∀ (js : List Nat) (s : Alloc F) (st : St F), Good ctx nodes need comp s st →
      (∀ j ∈ js, last[j]! = t → ¬need j) →
      Good ctx nodes need comp (Alloc.releaseLast last t s js) st ∧
        (Alloc.releaseLast last t s js).code = s.code ∧
        (Alloc.releaseLast last t s js).loc = s.loc ∧
        (Alloc.releaseLast last t s js).owner.size = s.owner.size
  | [], s, st, h, _ => ⟨h, rfl, rfl, rfl⟩
  | j :: js, s, st, h, hj => by
    simp only [Alloc.releaseLast, List.foldl_cons]
    have hstep : Good ctx nodes need comp (if last[j]! = t then s.release j else s) st ∧
        (if last[j]! = t then s.release j else s).code = s.code ∧
        (if last[j]! = t then s.release j else s).loc = s.loc ∧
        (if last[j]! = t then s.release j else s).owner.size = s.owner.size := by
      split
      · rename_i ht
        exact ⟨h.release j (hj j List.mem_cons_self ht), Alloc.release_code s j,
          Alloc.release_loc s j, Alloc.release_size s j⟩
      · exact ⟨h, rfl, rfl, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := Good.releaseLast last t js _ st hstep.1
      fun j' hj' ↦ hj j' (List.mem_cons_of_mem _ hj')
    exact ⟨h1, by rw [← hstep.2.1]; exact h2, by rw [← hstep.2.2.1]; exact h3,
      by rw [← hstep.2.2.2]; exact h4⟩

/-- Taking a register for a node `i` not yet computed, the run state then holding its value
there. -/
theorem Good.take {ctx : Ctx F} {nodes : Array (Node F)} {need comp : Nat → Prop} {s : Alloc F}
    {st : St F} (h : Good ctx nodes need comp s st) (i : Nat) (hi : i < nodes.size)
    (hreg : InReg nodes i) (hnew : ¬comp i) (st' : St F)
    (hst : ∀ r, st'.reg r = if r = (s.take i).2 then val ctx nodes i else st.reg r) :
    Good ctx nodes need (fun j ↦ comp j ∨ j = i) (s.take i).1 st' := by
  have hf : ∀ r ∈ s.free, r < s.owner.size := fun r hr ↦ (h.free r hr).1
  have hloc : ∀ j, (s.take i).1.locOf j = if j = i then (s.take i).2 else s.locOf j := by
    intro j
    simp only [Alloc.locOf, Alloc.take_loc]
    rw [Alloc.getD_set!]
    by_cases hj : j = i
    · subst hj; simp only [h.loc, hi, and_self, ite_true]
    · simp only [Ne.symm hj, false_and, ite_false, hj]
  have hR := s.own_take i fun r hr ↦ (h.free r hr).2
  refine ⟨by
    rw [Alloc.take_loc, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h.loc,
    fun r j hr ↦ ?_, by rw [Alloc.take_free]; exact h.nodup.sublist (List.tail_sublist _),
    fun r hr ↦ ?_, fun j h1 h2 h3 ↦ ?_⟩
  · rw [Alloc.take_own s i r hf] at hr
    split at hr
    · rename_i hrR
      simp only [Option.some.injEq] at hr
      subst hr hrR
      refine ⟨hreg, Or.inr rfl, by rw [hloc]; simp only [ite_true],
        by rw [hst]; simp only [ite_true]⟩
    · rename_i hrR
      obtain ⟨g1, g2, g3, g4⟩ := h.owned r j hr
      have hji : j ≠ i := fun e ↦ hnew (e ▸ g2)
      refine ⟨g1, Or.inl g2, by rw [hloc]; simp only [hji, ite_false, g3], by
        rw [hst]; simp only [hrR, ite_false, g4]⟩
  · have hnm := s.take_not_mem i h.nodup
    have hr' : r ∈ s.free := by
      rw [Alloc.take_free] at hr; exact List.mem_of_mem_tail hr
    have hrR : r ≠ (s.take i).2 := fun e ↦ hnm (e ▸ hr)
    obtain ⟨g1, g2⟩ := h.free r hr'
    refine ⟨Nat.lt_of_lt_of_le g1 (s.take_size_le i), ?_⟩
    rw [Alloc.take_own s i r hf]
    simp only [hrR, ite_false, g2]
  · rw [hloc, Alloc.take_own s i _ hf]
    by_cases hji : j = i
    · subst hji; simp only [ite_true]
    · rcases h2 with h2 | h2
      · have := h.ready j h1 h2 h3
        simp only [hji, ite_false]
        split
        · rename_i e
          rw [e, hR] at this
          exact absurd this (by simp only [reduceCtorEq, not_false_eq_true])
        · exact this
      · exact absurd h2 hji

end Own

/-! ### One step of the allocation -/

section FieldMachine
variable [Field F] (ctx : Ctx F) (st : St F)

theorem exec_load (d : Nat) (src : Src) : (Instr.load d src).exec (fieldMachine ctx) st =
    { st with reg := Function.update st.reg d (ctx.src src) } := rfl

theorem exec_scalar (d k : Nat) : (Instr.scalar d k).exec (fieldMachine ctx) st =
    { st with reg := Function.update st.reg d (ctx.scalar k) } := rfl

theorem exec_bin (o : Op) (d : Nat) (a b : Opd F) :
    (Instr.bin o d a b).exec (fieldMachine ctx) st =
      { st with reg := Function.update st.reg d (o.eval (a.val ctx st) (b.val ctx st)) } := rfl

theorem exec_acc (a : Opd F) (w : Nat) : (Instr.acc a w).exec (fieldMachine ctx) st =
    { st with acc := fun j ↦ st.acc j + a.val ctx st * ctx.weight w j } := rfl

end FieldMachine

section Step
variable [Field F] (ctx : Ctx F) (nodes : Array (Node F)) (steps : Array Step) (outs : Array Nat)

/-- The accumulators after the steps before `t` from `a0`: every accumulation adds its node's value
times its weight. -/
def accTo (a0 : Nat → F) : Nat → Nat → F
  | 0 => a0
  | t + 1 => match steps[t]? with
    | some (.acc i w) => fun k ↦ accTo a0 t k + val ctx nodes i * ctx.weight w k
    | _ => accTo a0 t

variable {ctx nodes steps outs}

theorem computed_succ {t j : Nat} :
    Computed steps (t + 1) j ↔ Computed steps t j ∨ steps[t]? = some (Step.node j) := by
  constructor
  · rintro ⟨t', h1, h2⟩
    rcases Nat.lt_or_ge t' t with h | h
    · exact Or.inl ⟨t', h, h2⟩
    · have : t' = t := by omega
      subst this; exact Or.inr h2
  · rintro (⟨t', h1, h2⟩ | h)
    · exact ⟨t', by omega, h2⟩
    · exact ⟨t, by omega, h⟩

/-- A node read at step `t` is its operand's value there. -/
theorem opd_val (hs : SchedOk nodes steps outs) {t : Nat} {s : Alloc F} {st : St F}
    (h : Good ctx nodes (Need nodes steps outs t) (Computed steps t) s st) (j : Nat)
    (hj : j ∈ readsAt nodes steps outs t) :
    (Alloc.opd nodes s j).val ctx st = val ctx nodes j ∧
      (Alloc.opd nodes s j).RegsLt s.owner.size := by
  obtain ⟨hlt, hc⟩ := hs.reads t j hj
  have hn : Need nodes steps outs t j := ⟨t, Nat.le_refl _, hj⟩
  obtain ⟨n, hnj⟩ : ∃ n, nodes[j]? = some n := ⟨_, Array.getElem?_eq_getElem hlt⟩
  have hv := val_eq ctx nodes j n hnj (hs.before j n hnj)
  have hreg (hr : InReg nodes j) : (Alloc.opd nodes s j).val ctx st = val ctx nodes j ∧
      (Alloc.opd nodes s j).RegsLt s.owner.size := by
    have hown := h.ready j hr (hc hr) hn
    obtain ⟨-, -, -, hval⟩ := h.owned _ j hown
    have hop : Alloc.opd nodes s j = .reg (s.locOf j) := by
      unfold Alloc.opd
      rw [hnj]
      unfold InReg at hr
      rw [hnj] at hr
      split
      · rename_i c hc'; simp only [Option.some.injEq] at hc'; subst hc'; exact absurd hr id
      · rename_i x hc'; simp only [Option.some.injEq] at hc'; subst hc'; exact absurd hr id
      · simp only [Alloc.locOf, Array.getElem!_eq_getD, Alloc.default_nat]
    rw [hop]
    exact ⟨hval, Alloc.own_some_lt hown⟩
  cases n with
  | cur c =>
    have hop : Alloc.opd nodes s j = .cur c := by simp only [Alloc.opd, hnj]
    rw [hop, hv]
    exact ⟨rfl, trivial⟩
  | const x =>
    have hop : Alloc.opd nodes s j = .const x := by simp only [Alloc.opd, hnj]
    rw [hop, hv]
    exact ⟨rfl, trivial⟩
  | load src => exact hreg (by simp only [InReg, hnj])
  | scalar k => exact hreg (by simp only [InReg, hnj])
  | bin o a b => exact hreg (by simp only [InReg, hnj])

theorem Good.emit {need comp : Nat → Prop} {s : Alloc F} {st st' : St F}
    (h : Good ctx nodes need comp s st) (ins : Instr F) (hst : st'.reg = st.reg) :
    Good ctx nodes need comp (s.emit ins) st' := by
  obtain ⟨owner, free, loc, code⟩ := s
  exact ⟨h.loc, fun r j hr ↦ by rw [hst]; exact h.owned r j hr, h.nodup, h.free, h.ready⟩

theorem Good.mono_comp {need comp comp' : Nat → Prop} {s : Alloc F} {st : St F}
    (h : Good ctx nodes need comp s st) (h1 : ∀ j, comp j → comp' j)
    (h2 : ∀ j, InReg nodes j → comp' j → comp j) : Good ctx nodes need comp' s st :=
  ⟨h.loc, fun r j hr ↦ by
    obtain ⟨a, b, c, d⟩ := h.owned r j hr; exact ⟨a, h1 j b, c, d⟩, h.nodup, h.free,
    fun j a b c ↦ h.ready j a (h2 j a b) c⟩

/-- Computing node `i` at step `t` into a register. -/
theorem compute_good (hs : SchedOk nodes steps outs) {last : Array Nat}
    (hlast : ∀ t j, j ∈ readsAt nodes steps outs t → t ≤ last[j]!) (st0 : St F) {t i : Nat}
    (hti : steps[t]? = some (Step.node i)) (hreg : InReg nodes i) {s : Alloc F}
    (h : Good ctx nodes (Need nodes steps outs t) (Computed steps t) s
      (run (fieldMachine ctx) s.code st0))
    (hwf : ∀ ins ∈ s.code, ins.RegsLt s.owner.size) (args : List Nat) (ins : Nat → Instr F)
    (hins : ∀ r, (ins r).exec (fieldMachine ctx) (run (fieldMachine ctx) s.code st0) =
      { run (fieldMachine ctx) s.code st0 with
        reg := Function.update (run (fieldMachine ctx) s.code st0).reg r (val ctx nodes i) })
    (hinsw : ∀ r n, r < n → s.owner.size ≤ n → (ins r).RegsLt n) :
    let s' := Alloc.compute last t s i args ins
    Good ctx nodes (Need nodes steps outs (t + 1)) (Computed steps (t + 1)) s'
        (run (fieldMachine ctx) s'.code st0) ∧
      (run (fieldMachine ctx) s'.code st0).acc = (run (fieldMachine ctx) s.code st0).acc ∧
      (∀ ins ∈ s'.code, ins.RegsLt s'.owner.size) := by
  intro s'
  have hi : i < nodes.size := hs.node_lt t i hti
  have hnew : ¬Computed steps t i := hs.once t i hti
  set st := run (fieldMachine ctx) s.code st0 with hst
  obtain ⟨h1, hc1, hl1, hz1⟩ := (h.weaken fun j ↦ need_succ).releaseLast last t args s st
    fun j _ hj ↦ not_need hlast hj
  set s1 := Alloc.releaseLast last t s args
  set st3 := (ins (s1.take i).2).exec (fieldMachine ctx) st
  have hst3 : ∀ r, st3.reg r = if r = (s1.take i).2 then val ctx nodes i else st.reg r := by
    intro r
    simp only [st3, hins, Function.update_apply]
  have h2 := h1.take i hi hreg hnew st3 hst3
  have h3 := h2.emit (ins (s1.take i).2) (st' := st3) rfl
  have hcomp : ∀ j, (Computed steps t j ∨ j = i) ↔ Computed steps (t + 1) j := by
    intro j
    rw [computed_succ, hti]
    constructor
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl h
      · simp only [Option.some.injEq, Step.node.injEq] at h; exact Or.inr h.symm
  have h4 := h3.mono_comp (fun j hj ↦ (hcomp j).mp hj) (fun j _ hj ↦ (hcomp j).mpr hj)
  have hcode3 : ((s1.take i).1.emit (ins (s1.take i).2)).code =
      s.code.push (ins (s1.take i).2) := by
    rw [Alloc.emit_code, Alloc.take_code, hc1]
  have hrun3 : run (fieldMachine ctx) ((s1.take i).1.emit (ins (s1.take i).2)).code st0 = st3 := by
    rw [hcode3, run_push]
  have hsize3 : ((s1.take i).1.emit (ins (s1.take i).2)).owner.size = (s1.take i).1.owner.size := by
    rw [Alloc.emit_owner]
  have hwf3 : ∀ ins' ∈ ((s1.take i).1.emit (ins (s1.take i).2)).code,
      ins'.RegsLt ((s1.take i).1.emit (ins (s1.take i).2)).owner.size := by
    rw [hcode3, hsize3]
    intro ins' hm
    rcases Array.mem_push.mp hm with hm | hm
    · exact (hwf ins' hm).mono (by rw [← hz1]; exact s1.take_size_le i)
    · subst hm
      exact hinsw _ _ (s1.take_lt i fun r hr ↦ (h1.free r hr).1)
        (by rw [← hz1]; exact s1.take_size_le i)
  have hs' : s' = if last[i]! = t then ((s1.take i).1.emit (ins (s1.take i).2)).release i
      else (s1.take i).1.emit (ins (s1.take i).2) := rfl
  have hacc3 : st3.acc = st.acc := by simp only [st3, hins]
  rw [hs']
  split
  · rename_i hlt
    rw [Alloc.release_code, hrun3]
    exact ⟨h4.release i (not_need hlast hlt), hacc3, fun ins' hm ↦ by
      rw [Alloc.release_size]; exact hwf3 ins' hm⟩
  · rw [hrun3]
    exact ⟨h4, hacc3, hwf3⟩

theorem computed_succ_of_ne {t j : Nat} (h : ∀ i, steps[t]? ≠ some (Step.node i)) :
    Computed steps (t + 1) j ↔ Computed steps t j := by
  rw [computed_succ]
  exact ⟨fun h' ↦ h'.elim id fun e ↦ absurd e (h j), Or.inl⟩

/-- One step of the allocation keeps the invariant, accumulates as the schedule does, and keeps
the registers below the allocator's count. -/
theorem step_good (hs : SchedOk nodes steps outs) {last : Array Nat}
    (hlast : ∀ t j, j ∈ readsAt nodes steps outs t → t ≤ last[j]!) (st0 : St F) {t : Nat}
    (ht : t < steps.size) {s : Alloc F}
    (h : Good ctx nodes (Need nodes steps outs t) (Computed steps t) s
      (run (fieldMachine ctx) s.code st0))
    (hacc : (run (fieldMachine ctx) s.code st0).acc = accTo ctx nodes steps st0.acc t)
    (hwf : ∀ ins ∈ s.code, ins.RegsLt s.owner.size) :
    let s' := s.step nodes last t steps[t]!
    Good ctx nodes (Need nodes steps outs (t + 1)) (Computed steps (t + 1)) s'
        (run (fieldMachine ctx) s'.code st0) ∧
      (run (fieldMachine ctx) s'.code st0).acc = accTo ctx nodes steps st0.acc (t + 1) ∧
      (∀ ins ∈ s'.code, ins.RegsLt s'.owner.size) := by
  intro s'
  have hget : steps[t]? = some steps[t] := Array.getElem?_eq_getElem ht
  have hget! : steps[t]! = steps[t] := getElem!_pos steps t ht
  have hreads : readsAt nodes steps outs t = steps[t].reads nodes := by
    simp only [readsAt, ht, dite_true]
  have hs' : s' = s.step nodes last t steps[t] := by simp only [s', hget!]
  rw [hs']
  generalize hstep : steps[t] = step at hget hreads
  cases step with
  | node i =>
    have hi := hs.node_lt t i hget
    have hacc' : accTo ctx nodes steps st0.acc (t + 1) = accTo ctx nodes steps st0.acc t := by
      simp only [accTo, hget]
    obtain ⟨n, hn⟩ : ∃ n, nodes[i]? = some n := ⟨_, Array.getElem?_eq_getElem hi⟩
    have hv := val_eq ctx nodes i n hn (hs.before i n hn)
    have hmid (hnr : ¬InReg nodes i) (hs'' : s.step nodes last t (.node i) = s) :
        Good ctx nodes (Need nodes steps outs (t + 1)) (Computed steps (t + 1))
          (s.step nodes last t (.node i))
          (run (fieldMachine ctx) (s.step nodes last t (.node i)).code st0) ∧
        (run (fieldMachine ctx) (s.step nodes last t (.node i)).code st0).acc =
          accTo ctx nodes steps st0.acc (t + 1) ∧
        (∀ ins ∈ (s.step nodes last t (.node i)).code,
          ins.RegsLt (s.step nodes last t (.node i)).owner.size) := by
      rw [hs'', hacc']
      refine ⟨(h.weaken fun j ↦ need_succ).mono_comp (fun j hj ↦ computed_succ.mpr (Or.inl hj))
        (fun j hj hc ↦ ?_), hacc, hwf⟩
      rcases computed_succ.mp hc with hc | hc
      · exact hc
      · rw [hget] at hc
        simp only [Option.some.injEq, Step.node.injEq] at hc
        subst hc
        exact absurd hj hnr
    cases n with
    | cur c => exact hmid (by simp only [InReg, hn, not_false_eq_true]) (by
        simp only [Alloc.step, hn])
    | const x => exact hmid (by simp only [InReg, hn, not_false_eq_true]) (by
        simp only [Alloc.step, hn])
    | load src =>
      simp only [Alloc.step, hn]
      obtain ⟨g, a, w⟩ := compute_good hs hlast st0 hget (by simp only [InReg, hn]) h hwf []
        (fun r ↦ .load r src) (fun r ↦ by rw [hv]; rfl) (fun r n hr _ ↦ hr)
      exact ⟨g, by rw [a, hacc, hacc'], w⟩
    | scalar k =>
      simp only [Alloc.step, hn]
      obtain ⟨g, a, w⟩ := compute_good hs hlast st0 hget (by simp only [InReg, hn]) h hwf []
        (fun r ↦ .scalar r k) (fun r ↦ by rw [hv]; rfl) (fun r n hr _ ↦ hr)
      exact ⟨g, by rw [a, hacc, hacc'], w⟩
    | bin o a b =>
      simp only [Alloc.step, hn]
      have hra : a ∈ readsAt nodes steps outs t := by
        rw [hreads]; simp only [Step.reads, hn, Option.map_some, Option.getD_some,
          Node.regArgs, List.mem_cons, true_or]
      have hrb : b ∈ readsAt nodes steps outs t := by
        rw [hreads]; simp only [Step.reads, hn, Option.map_some, Option.getD_some,
          Node.regArgs]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      obtain ⟨va, wa⟩ := opd_val hs h a hra
      obtain ⟨vb, wb⟩ := opd_val hs h b hrb
      obtain ⟨g, ac, w⟩ := compute_good hs hlast st0 hget (by simp only [InReg, hn]) h hwf
        [a, b] (fun r ↦ .bin o r (Alloc.opd nodes s a) (Alloc.opd nodes s b))
        (fun r ↦ by rw [exec_bin, va, vb, hv]; rfl)
        (fun r n hr hn' ↦ ⟨hr, wa.mono hn', wb.mono hn'⟩)
      exact ⟨g, by rw [ac, hacc, hacc'], w⟩
  | acc i w =>
    have hri : i ∈ readsAt nodes steps outs t := by
      rw [hreads]; simp only [Step.reads, List.mem_singleton]
    obtain ⟨vi, wi⟩ := opd_val hs h i hri
    have hne : ∀ j, steps[t]? ≠ some (Step.node j) := by
      intro j; rw [hget]; simp only [ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]
    simp only [Alloc.step]
    have hrun1 : run (fieldMachine ctx) (s.emit (.acc (Alloc.opd nodes s i) w)).code st0 =
        (Instr.acc (Alloc.opd nodes s i) w).exec (fieldMachine ctx)
          (run (fieldMachine ctx) s.code st0) := by
      rw [Alloc.emit_code, run_push]
    have h1 : Good ctx nodes (Need nodes steps outs t) (Computed steps t)
        (s.emit (.acc (Alloc.opd nodes s i) w))
        (run (fieldMachine ctx) (s.emit (.acc (Alloc.opd nodes s i) w)).code st0) := by
      rw [hrun1]; exact h.emit _ rfl
    obtain ⟨g, hc, -, hz⟩ := (h1.weaken fun j ↦ need_succ).releaseLast last t [i] _ _
      fun j _ hj ↦ not_need hlast hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      exact g.mono_comp (fun j hj ↦ (computed_succ_of_ne hne).mpr hj)
        (fun j _ hj ↦ (computed_succ_of_ne hne).mp hj)
    · rw [hc, hrun1, exec_acc]
      funext k
      simp only [accTo, hget, hacc, vi]
    · rw [hc, hz, Alloc.emit_code, Alloc.emit_owner]
      intro ins hm
      rcases Array.mem_push.mp hm with hm | hm
      · exact hwf ins hm
      · subst hm; exact wi

end Step

/-! ### Last uses -/

theorem foldl_set_getD (v : Nat) : ∀ (js : List Nat) (a : Array Nat) (k : Nat),
    (js.foldl (fun l j ↦ l.set! j v) a).getD k 0 =
      (if k ∈ js ∧ k < a.size then v else a.getD k 0) ∧
    (js.foldl (fun l j ↦ l.set! j v) a).size = a.size
  | [], a, k => ⟨by simp only [List.not_mem_nil, false_and, ite_false, List.foldl_nil], rfl⟩
  | j :: js, a, k => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_set_getD v js (a.set! j v) k
    have hs : (a.set! j v).size = a.size := by
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    refine ⟨?_, by rw [h2, hs]⟩
    rw [h1, hs, Alloc.getD_set!]
    simp only [List.mem_cons, show (k = j) = (j = k) from propext eq_comm]
    by_cases h3 : k ∈ js <;> by_cases h4 : k < a.size <;> by_cases h5 : j = k <;>
      simp only [h3, h4, h5, ite_true, ite_false, and_true, and_false, false_and, or_true,
        or_false, and_self]

section Last
variable {nodes : Array (Node F)} {steps : Array Step}

/-- Every step reading a node is at most its last use. -/
theorem lastUses_spec :
    (lastUses nodes steps).size = nodes.size ∧ ∀ t < steps.size, ∀ j ∈ steps[t]!.reads nodes,
      j < nodes.size → t ≤ (lastUses nodes steps).getD j 0 := by
  unfold lastUses
  suffices h : ∀ T, ((List.range T).foldl (fun last t ↦
      (steps[t]!.reads nodes).foldl (fun l j ↦ l.set! j t)
        (match steps[t]! with | .node i => last.set! i t | .acc _ _ => last))
      (Array.replicate nodes.size 0)).size = nodes.size ∧ ∀ t < T, ∀ j ∈ steps[t]!.reads nodes,
        j < nodes.size → t ≤ ((List.range T).foldl (fun last t ↦
          (steps[t]!.reads nodes).foldl (fun l j ↦ l.set! j t)
            (match steps[t]! with | .node i => last.set! i t | .acc _ _ => last))
          (Array.replicate nodes.size 0)).getD j 0 by
    obtain ⟨h1, h2⟩ := h steps.size
    exact ⟨h1, fun t ht ↦ h2 t ht⟩
  intro T
  induction T with
  | zero => exact ⟨Array.size_replicate .., fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
  | succ T ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨ih1, ih2⟩ := ih
    generalize (List.range T).foldl _ _ = L at ih1 ih2
    have hm : (match steps[T]! with | .node i => L.set! i T | .acc _ _ => L).size = L.size ∧
        ∀ k, (match steps[T]! with | .node i => L.set! i T | .acc _ _ => L).getD k 0 ≥
          min T (L.getD k 0) := by
      split
      · refine ⟨by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds],
          fun k ↦ ?_⟩
        rw [Alloc.getD_set!]; split <;> omega
      · exact ⟨rfl, fun k ↦ by omega⟩
    generalize (match steps[T]! with | .node i => L.set! i T | .acc _ _ => L) = M at hm
    obtain ⟨hm1, hm3⟩ := hm
    obtain ⟨hf1, hf2⟩ := (foldl_set_getD T (steps[T]!.reads nodes) M 0)
    refine ⟨by rw [hf2, hm1, ih1], fun t ht j hj hjs ↦ ?_⟩
    rw [(foldl_set_getD T (steps[T]!.reads nodes) M j).1]
    by_cases hT : t = T
    · subst hT
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj, by rw [hm1, ih1]; exact hjs⟩)]
    · have := ih2 t (by omega) j hj hjs
      have := hm3 j
      split <;> omega

end Last

/-! ### The allocated program -/

/-- **Register allocation is correct**: on every row, the allocated program accumulates the
scheduled nodes' values with their weights (`accTo`), its outputs are the output nodes' values,
and its registers are below its count. -/
theorem allocate_run [Field F] (ctx : Ctx F) (nodes : Array (Node F)) (steps : Array Step)
    (outs : Array Nat) (hs : SchedOk nodes steps outs) (st0 : St F) :
    (run (fieldMachine ctx) (allocate nodes steps outs).code st0).acc =
        accTo ctx nodes steps st0.acc steps.size ∧
      (∀ k < outs.size, ((allocate nodes steps outs).outs.getD k (.reg 0)).val ctx
          (run (fieldMachine ctx) (allocate nodes steps outs).code st0) =
        val ctx nodes (outs.getD k 0) ∧
        ((allocate nodes steps outs).outs.getD k (.reg 0)).RegsLt
          (allocate nodes steps outs).regs) ∧
      ∀ ins ∈ (allocate nodes steps outs).code, ins.RegsLt (allocate nodes steps outs).regs := by
  -- The last uses, with the outputs read after the last step.
  obtain ⟨hl1, hl2⟩ := lastUses_spec (nodes := nodes) (steps := steps)
  set last := outs.foldl (fun l j ↦ l.set! j steps.size) (lastUses nodes steps) with hlast
  have hlast' : ∀ t j, j ∈ readsAt nodes steps outs t → t ≤ last[j]! := by
    intro t j hj
    have hjn := (hs.reads t j hj).1
    rw [Array.getElem!_eq_getD, Alloc.default_nat, hlast, ← Array.foldl_toList,
      (foldl_set_getD steps.size outs.toList _ j).1]
    unfold readsAt at hj
    split at hj
    · rename_i ht
      have := hl2 t ht j (by rw [getElem!_pos steps t ht]; exact hj) hjn
      split <;> omega
    · split at hj
      · rename_i ht
        subst ht
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj, by rw [hl1]; exact hjn⟩)]
      · exact absurd hj List.not_mem_nil
  -- The allocator's states.
  let s0 : Alloc F := ⟨#[], [], Array.replicate nodes.size 0, #[]⟩
  let S (T : Nat) : Alloc F := (List.range T).foldl (fun s t ↦ s.step nodes last t steps[t]!) s0
  have hgood : ∀ T ≤ steps.size,
      Good ctx nodes (Need nodes steps outs T) (Computed steps T) (S T)
        (run (fieldMachine ctx) (S T).code st0) ∧
      (run (fieldMachine ctx) (S T).code st0).acc = accTo ctx nodes steps st0.acc T ∧
      ∀ ins ∈ (S T).code, ins.RegsLt (S T).owner.size := by
    intro T hT
    induction T with
    | zero =>
      refine ⟨⟨Array.size_replicate .., fun r j hr ↦ ?_, List.nodup_nil, fun r hr ↦ ?_,
        fun j _ hc ↦ ?_⟩, rfl, fun ins hm ↦ ?_⟩
      · simp only [S, List.range_zero, List.foldl_nil, Alloc.own, s0,
          Array.getD_eq_getD_getElem?, Array.getElem?_empty, Option.getD_none, reduceCtorEq] at hr
      · exact absurd hr List.not_mem_nil
      · obtain ⟨t', ht', -⟩ := hc; exact absurd ht' (Nat.not_lt_zero t')
      · simp only [S, List.range_zero, List.foldl_nil, s0] at hm
        exact absurd hm (by simp only [Array.not_mem_empty, not_false_eq_true])
    | succ T ih =>
      obtain ⟨g, a, w⟩ := ih (by omega)
      have hS : S (T + 1) = (S T).step nodes last T steps[T]! := by
        simp only [S, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hS]
      exact step_good hs hlast' st0 (by omega) g a w
  obtain ⟨g, a, w⟩ := hgood steps.size (Nat.le_refl _)
  have hP : allocate nodes steps outs = ⟨(S steps.size).code, (S steps.size).owner.size,
      outs.map (Alloc.opd nodes (S steps.size))⟩ := rfl
  rw [hP]
  refine ⟨a, fun k hk ↦ ?_, w⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
    Option.getD_some]
  exact opd_val hs g outs[k] (by
    simp only [readsAt, Nat.lt_irrefl, dite_false, ite_true]
    exact Array.getElem_mem_toList hk)

end CompStark.Stark.Prog
