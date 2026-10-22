/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Lookup.LogUp

/-! # Lookups of a batch

How Plonky3's batch STARK (revision `a4982ec`) lays out the lookups of a batch's AIRs:

* An AIR's quotient is sized by its constraints and its lookups' LogUp constraints
  (`Air.logQuotientChunksWith`).
* The global lookups of an AIR on one bus are packed into shared fraction columns, as long as a
  column's fraction pin stays within the degree that keeps the quotient's chunks
  (`packSameBus`, Plonky3's `pack_same_bus_with_degree`; `Air.packedLookups`). The verifier
  derives the packed lookups from its AIRs, as Plonky3's keygen does for its common data.
* One challenge pair `(α, β)` serves the whole batch: bus `b` has the denominator base
  `α + (b + 1) βᵂ`, `W` the widest tuple of the batch and at least `1`, the global buses numbered
  by first appearance and every local lookup on a bus of its own (`challengeLayout`, Plonky3's
  `lay_out_lookup_challenges`).
* Every lookup's tuples, and every tuple on a global bus, share one width (`widthsOk`), and the
  multiplicities cannot wrap around the field's characteristic `p`: `∑ᵢ wᵢ nᵢ < p` over the
  instances, `wᵢ` the sum of an AIR's count weights and `nᵢ` its trace's height
  (`heightBoundOk`, Plonky3's `check_multiplicity_height_bound`).
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark
open scoped List

variable {F : Type}

/-! ### Quotient sizing and packing -/

/-- The largest degree of the extension constraints `ext` in the model of `A`'s chunk count:
Plonky3's `degree_multiple` without periodic columns, the polynomial degree in multiples of
`n - 1` with them (`Air.constraintDegree`). -/
def extDegree (A : Air F) (logN : Nat) (ext : List (ExtExpr F)) : Nat :=
  if A.periodic = [] then ext.foldl (fun m c ↦ max m c.degree) 0 else
    let D := ext.foldl (fun m c ↦ max m (c.degBound (2 ^ logN) (A.periodicDegree (2 ^ logN)))) 0
    let denom := max (2 ^ logN - 1) 1
    if D = 0 then 0 else (D - 1 + denom - 1) / denom

/-- Plonky3's log number of quotient chunks of `A`'s constraints and the extension constraints
`ext` on a trace of `2 ^ logN` rows. -/
def _root_.CompStark.Stark.Air.logQuotientChunksWith (A : Air F) (logN : Nat)
    (ext : List (ExtExpr F)) : Nat :=
  let d := max (max (A.constraintDegree logN) (extDegree A logN ext)) 2 - 1
  Nat.log2 d.nextPowerOfTwo

/-- The step of `packBus`: the lookup `m` joins the open column `cur` while the column's fraction
pin stays within the degree `budget`; otherwise the column is sealed and `m` opens the next. -/
def packStep (budget : Nat) (s : List (Lookup F) × Lookup F) (m : Lookup F) :
    List (Lookup F) × Lookup F :=
  let trial : Lookup F := { s.2 with entries := s.2.entries ++ m.entries }
  if lookupDegree trial ≤ budget then (s.1, trial) else (s.1 ++ [s.2], m)

/-- One bus's lookups packed greedily in order (`packStep`), each packed column holding its
lookups' tuples and so the sum of their count weights. -/
def packBus (budget : Nat) : List (Lookup F) → List (Lookup F)
  | [] => []
  | l :: ls =>
    let (cols, cur) := ls.foldl (packStep budget) ([], l)
    cols ++ [cur]

/-- The step of `buses`: the lookup's global bus joins the names unless it is there. -/
def busesStep (bs : List String) (l : Lookup F) : List String :=
  match l.bus with
  | some b => if bs.contains b then bs else bs ++ [b]
  | none => bs

/-- The global buses of the lookups, in order of first appearance. -/
def buses (ls : List (Lookup F)) : List String := ls.foldl busesStep []

/-- Plonky3's `pack_same_bus_with_degree`: the local lookups in order, then every bus's global
lookups packed (`packBus`), the buses in order of first appearance. -/
def packSameBus (budget : Nat) (ls : List (Lookup F)) : List (Lookup F) :=
  ls.filter (·.bus.isNone) ++
    (buses ls).flatMap fun b ↦ packBus budget (ls.filter (·.bus == some b))

/-- Packing a bus keeps its tuples, in order. -/
theorem flatMap_packBus (budget : Nat) :
    ∀ ms : List (Lookup F), (packBus budget ms).flatMap (·.entries) = ms.flatMap (·.entries)
  | [] => rfl
  | l :: ls => by
    suffices h : ∀ (ms : List (Lookup F)) (r : List (Lookup F) × Lookup F),
        ((ms.foldl (packStep budget) r).1 ++ [(ms.foldl (packStep budget) r).2]).flatMap
          (·.entries) = (r.1 ++ [r.2]).flatMap (·.entries) ++ ms.flatMap (·.entries) by
      have := h ls ([], l)
      simp only [packBus, List.nil_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at this ⊢
      exact this
    intro ms
    induction ms with
    | nil => exact fun r ↦ by rw [List.flatMap_nil, List.append_nil, List.foldl_nil]
    | cons m ms ih =>
      intro r
      rw [List.foldl_cons, ih, List.flatMap_cons, ← List.append_assoc]
      congr 1
      unfold packStep
      dsimp only
      split
      · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc]
      · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc]

/-- A flat map over keys without repeats, one of whose lists `f c` gains the prefix `e`, permutes
`e` before the flat map without it. -/
theorem perm_flatMap_of_eq_append {α : Type*} (c : String) (e : List α) (f g : String → List α)
    (hc : f c = e ++ g c) (hne : ∀ b, b ≠ c → f b = g b) :
    ∀ bs : List String, bs.Nodup → c ∈ bs → bs.flatMap f ~ e ++ bs.flatMap g
  | [], _, h => absurd h List.not_mem_nil
  | b :: bs, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.flatMap_cons]
    by_cases hb : b = c
    · subst hb
      have hrest : bs.flatMap f = bs.flatMap g :=
        List.flatMap_congr fun x hx ↦ hne x fun h ↦ hnd.1 (h ▸ hx)
      rw [hc, hrest, List.append_assoc]
    · rw [hne b hb]
      have hc' : c ∈ bs := (List.mem_cons.mp h).resolve_left (Ne.symm hb)
      exact ((perm_flatMap_of_eq_append c e f g hc hne bs hnd.2 hc').append_left _).trans
        (List.perm_append_comm_assoc _ _ _)

/-- Splitting the lookups by bus, over a list of bus names without repeats that holds every
global bus, permutes their tuples. -/
theorem perm_flatMap_filter_bus (bs : List String) (hbs : bs.Nodup) :
    ∀ ls : List (Lookup F), (∀ l ∈ ls, ∀ b, l.bus = some b → b ∈ bs) →
      (ls.filter (·.bus.isNone)).flatMap (·.entries) ++
        bs.flatMap (fun b ↦ (ls.filter (·.bus == some b)).flatMap (·.entries)) ~
      ls.flatMap (·.entries)
  | [], _ => by
    simp only [List.filter_nil, List.flatMap_nil, List.nil_append]
    rw [List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl]
  | l :: ls, h => by
    have ih := perm_flatMap_filter_bus bs hbs ls fun m hm ↦ h m (List.mem_cons_of_mem _ hm)
    rw [List.flatMap_cons]
    cases hl : l.bus with
    | none =>
      have hf : ∀ b, (l :: ls).filter (·.bus == some b) = ls.filter (·.bus == some b) := by
        intro b
        rw [List.filter_cons_of_neg (by rw [hl]; exact Bool.false_ne_true)]
      have hp : l.bus.isNone = true := by rw [hl]; rfl
      simp only [hf]
      rw [List.filter_cons_of_pos (p := fun x : Lookup F ↦ x.bus.isNone) hp, List.flatMap_cons,
        List.append_assoc]
      exact ih.append_left _
    | some c =>
      have hc : c ∈ bs := h l List.mem_cons_self c hl
      rw [List.filter_cons_of_neg (by rw [hl]; exact Bool.false_ne_true)]
      have hg := perm_flatMap_of_eq_append c l.entries
        (fun b ↦ ((l :: ls).filter (·.bus == some b)).flatMap (·.entries))
        (fun b ↦ (ls.filter (·.bus == some b)).flatMap (·.entries))
        (by
          rw [List.filter_cons_of_pos (by rw [hl]; exact beq_self_eq_true _), List.flatMap_cons])
        (fun b hb ↦ by
          rw [List.filter_cons_of_neg (by
            rw [hl]; simp only [beq_iff_eq, Option.some.injEq]; exact fun h ↦ hb h.symm)])
        bs hbs hc
      exact (hg.append_left _).trans ((List.perm_append_comm_assoc _ _ _).trans (ih.append_left _))

/-- Folding `busesStep` keeps the names without repeats and adds every lookup's bus. -/
theorem foldl_busesStep : ∀ (ls : List (Lookup F)) (bs : List String), bs.Nodup →
    (ls.foldl busesStep bs).Nodup ∧ (∀ b ∈ bs, b ∈ ls.foldl busesStep bs) ∧
      ∀ l ∈ ls, ∀ b, l.bus = some b → b ∈ ls.foldl busesStep bs
  | [], bs, h => ⟨h, fun _ hb ↦ hb, fun _ hl ↦ absurd hl List.not_mem_nil⟩
  | l :: ls, bs, h => by
    rw [List.foldl_cons]
    have h' : (busesStep bs l).Nodup ∧ (∀ b ∈ bs, b ∈ busesStep bs l) ∧
        ∀ b, l.bus = some b → b ∈ busesStep bs l := by
      unfold busesStep
      cases hl : l.bus with
      | none => exact ⟨h, fun _ hb ↦ hb, fun _ hb ↦ nomatch hb⟩
      | some c =>
        dsimp only
        split
        · rename_i hcon
          refine ⟨h, fun _ hb ↦ hb, fun b hb ↦ ?_⟩
          rw [Option.some.injEq] at hb
          subst hb
          exact List.contains_iff_mem.mp hcon
        · rename_i hcon
          refine ⟨List.nodup_append.mpr ⟨h, List.nodup_singleton c, fun a ha b hb ↦ ?_⟩,
            fun b hb ↦ List.mem_append_left _ hb, fun b hb ↦ ?_⟩
          · rw [List.mem_singleton] at hb
            subst hb
            rintro rfl
            exact hcon (List.contains_iff_mem.mpr ha)
          · rw [Option.some.injEq] at hb
            subst hb
            exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨h1, h2, h3⟩ := foldl_busesStep ls _ h'.1
    refine ⟨h1, fun b hb ↦ h2 b (h'.2.1 b hb), fun m hm b hb ↦ ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h2 b (h'.2.2 b hb)
    · exact h3 m hm b hb

/-- Packing permutes the lookups' tuples. -/
theorem perm_packSameBus (budget : Nat) (ls : List (Lookup F)) :
    (packSameBus budget ls).flatMap (·.entries) ~ ls.flatMap (·.entries) := by
  obtain ⟨hnd, -, hall⟩ := foldl_busesStep ls [] List.nodup_nil
  rw [packSameBus, List.flatMap_append, List.flatMap_assoc]
  simp only [flatMap_packBus]
  exact perm_flatMap_filter_bus _ hnd ls hall

/-- The sum of the lookups' count weights is the sum of their tuples' weights. -/
theorem sum_countWeight (ls : List (Lookup F)) :
    (ls.map (·.countWeight)).sum = ((ls.flatMap (·.entries)).map (·.2.weight)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.map_append, List.sum_append]
    rfl

/-- Every tuple of a packed lookup is a tuple of one of the lookups. -/
theorem packSameBus_entries (budget : Nat) (ls : List (Lookup F)) :
    ∀ l ∈ packSameBus budget ls, ∀ x ∈ l.entries, ∃ m ∈ ls, x ∈ m.entries := fun l hl _ hx ↦
  List.mem_flatMap.mp ((perm_packSameBus budget ls).subset (List.mem_flatMap.mpr ⟨l, hl, hx⟩))

/-- Every tuple of a packed lookup is a tuple of one of the lookups, as LogUp reads them. -/
theorem packSameBus_tuples (budget : Nat) (ls : List (Lookup F)) :
    ∀ l ∈ packSameBus budget ls, ∀ x ∈ l.tuples, ∃ m ∈ ls, x ∈ m.tuples := by
  intro l hl x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨m, hm, hym⟩ := packSameBus_entries budget ls l hl y hy
  exact ⟨m, hm, List.mem_map.mpr ⟨y, hym, rfl⟩⟩

/-- One lookup's bus in the numbering state `(ids, names, next)`: a global bus's number, given at
its first appearance; a fresh number for a local lookup. -/
def busStep (s : List Nat × List (String × Nat) × Nat) (l : Lookup F) :
    List Nat × List (String × Nat) × Nat :=
  match l.bus with
  | some b => match s.2.1.lookup b with
    | some k => (s.1 ++ [k], s.2.1, s.2.2)
    | none => (s.1 ++ [s.2.2], s.2.1 ++ [(b, s.2.2)], s.2.2 + 1)
  | none => (s.1 ++ [s.2.2], s.2.1, s.2.2 + 1)

/-- The buses of the lookups of the instances `ls`, the global buses already numbered as
`names` and `next` the next free number. -/
def busIdsFrom (names : List (String × Nat)) (next : Nat) :
    List (List (Lookup F)) → List (List Nat)
  | [] => []
  | inst :: rest =>
    let s := inst.foldl busStep ([], names, next)
    s.1 :: busIdsFrom s.2.1 s.2.2 rest

/-- Every instance's lookups' buses: the global buses numbered by first appearance across the
instances in order, every local lookup a fresh number. -/
def busIds (ls : List (List (Lookup F))) : List (List Nat) := busIdsFrom [] 0 ls

theorem length_busIdsFrom (names : List (String × Nat)) (next : Nat) :
    ∀ ls : List (List (Lookup F)), (busIdsFrom names next ls).length = ls.length
  | [] => rfl
  | _ :: ls => by
    simp only [busIdsFrom, List.length_cons]
    exact congrArg (· + 1) (length_busIdsFrom _ _ ls)

section
variable [Zero F] [One F]

/-- `A`'s lookups packed for a trace of `2 ^ logN` rows, within the degree that keeps the chunks
of the unpacked lookups (Plonky3's `from_airs_and_degrees`). -/
def _root_.CompStark.Stark.Air.packedLookups (A : Air F) (logN : Nat) : List (Lookup F) :=
  packSameBus (2 ^ A.logQuotientChunksWith logN (logUpConstraints A.lookups) + 1) A.lookups

/-- The LogUp constraints of `A`'s packed lookups on a trace of `2 ^ logN` rows. -/
def _root_.CompStark.Stark.Air.lookupConstraints (A : Air F) (logN : Nat) : List (ExtExpr F) :=
  logUpConstraints (A.packedLookups logN)

/-- `A`'s packed lookups read the columns its lookups read. -/
theorem _root_.CompStark.Stark.Air.packedLookups_colsBelow (A : Air F) (logN w pw : Nat)
    (h : ∀ l ∈ A.lookups, l.ColsBelow w pw) : ∀ l ∈ A.packedLookups logN, l.ColsBelow w pw :=
  fun l hl x hx ↦ by
    obtain ⟨m, hm, hx'⟩ := packSameBus_tuples _ A.lookups l hl x hx
    exact h m hm x hx'

/-! ### Row-local lookups -/

/-- The expression reads only the trace's and the preprocessed trace's rows, the public values and
constants: no selector and no periodic column. -/
def _root_.CompStark.Stark.Expr.rowLocal : Expr F → Bool
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .pub _ | .const _ => true
  | .periodic _ | .isFirstRow | .isLastRow | .isTransition => false
  | .add a b | .sub a b | .mul a b => a.rowLocal && b.rowLocal

/-- Every element and multiplicity of the lookup is row-local (`Expr.rowLocal`) and reads columns
below `w`, `wNext`, `pw` and `pwNext` (`Expr.colsBelow`). -/
def _root_.CompStark.Stark.Lookup.Fits (l : Lookup F) (w wNext pw pwNext : Nat) : Prop :=
  ∀ x ∈ l.tuples, (∀ e ∈ x.1, e.rowLocal ∧ e.colsBelow w wNext pw pwNext) ∧
    x.2.rowLocal ∧ x.2.colsBelow w wNext pw pwNext

/-! ### Widths and the multiplicity bound -/

/-- A lookup's tuple width: its first tuple's, `0` without tuples. -/
def _root_.CompStark.Stark.Lookup.width (l : Lookup F) : Nat :=
  (l.tuples.headD ([], .const 0)).1.length

/-- Every lookup's tuples share its width, and every global bus's tuples one width across the
lookups `ls` of the batch (Plonky3's `assert_uniform_tuple_width` and `check_bus_widths`). -/
def widthsOk (ls : List (Lookup F)) : Bool :=
  ls.all (fun l ↦ l.tuples.all (·.1.length == l.width)) &&
    (buses ls).all fun b ↦ match ls.filter (·.bus == some b) with
      | [] => true
      | l :: rest => rest.all (·.width == l.width)

/-- The widest tuple of the lookups, at least `1` (`W`). -/
def maxWidth (ls : List (Lookup F)) : Nat := ls.foldl (fun w l ↦ max w l.width) 1

/-- `∑ᵢ wᵢ 2 ^ logNᵢ < p` over the instances' lookups and log heights `ls`, `wᵢ` the sum of the
count weights, `p` the characteristic (Plonky3's `check_multiplicity_height_bound`). -/
def heightBoundOk (p : Nat) (ls : List (List (Lookup F) × Nat)) : Bool :=
  (ls.map fun (l, logN) ↦ (l.map (·.countWeight)).sum * 2 ^ logN).sum < p

/-! ### The challenges -/

end

variable [BaseField F] {EF : Type} [Challenge F EF]

/-- Every instance's challenges from the batch's pair `(α, β)`: for each lookup, its bus `b`'s
denominator base `α + (b + 1) βᵂ` and the combiner `β` (Plonky3's
`lay_out_lookup_challenges`). -/
def challengeLayout (ls : List (List (Lookup F))) (alpha beta : EF) : List (List EF) :=
  let gamma := Ext.pow beta (maxWidth ls.flatten)
  (busIds ls).map fun ids ↦ ids.flatMap fun b ↦
    [alpha + Ext.ofBase ((b + 1 : Nat) : F) * gamma, beta]

theorem length_challengeLayout (ls : List (List (Lookup F))) (alpha beta : EF) :
    (challengeLayout ls alpha beta).length = ls.length := by
  rw [challengeLayout, List.length_map, busIds, length_busIdsFrom]

end CompStark.Lookup
