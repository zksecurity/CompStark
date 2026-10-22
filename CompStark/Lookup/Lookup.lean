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
@[irreducible] def _root_.CompStark.Stark.Air.logQuotientChunksWith (A : Air F) (logN : Nat)
    (ext : List (ExtExpr F)) : Nat :=
  let d := max (max (A.constraintDegree logN) (extDegree A logN ext)) 2 - 1
  Nat.log2 (2 * d - 1)

/-- One bus's lookups packed greedily in order: each joins the open column while the column's
fraction pin stays within the degree `budget`, adding its count weight; otherwise the column is
sealed and it opens the next. -/
def packBus (budget : Nat) : List (Lookup F) → List (Lookup F)
  | [] => []
  | l :: ls =>
    let (cols, cur) := ls.foldl (fun (cols, cur) m ↦
      let trial : Lookup F := { cur with tuples := cur.tuples ++ m.tuples }
      if lookupDegree trial ≤ budget then (cols, { trial with
        countWeight := cur.countWeight + m.countWeight })
      else (cols ++ [cur], m)) ([], l)
    cols ++ [cur]

/-- The global buses of the lookups, in order of first appearance. -/
def buses (ls : List (Lookup F)) : List String :=
  ls.foldl (fun bs l ↦ match l.bus with
    | some b => if bs.contains b then bs else bs ++ [b]
    | none => bs) []

/-- Plonky3's `pack_same_bus_with_degree`: the local lookups in order, then every bus's global
lookups packed (`packBus`), the buses in order of first appearance. -/
def packSameBus (budget : Nat) (ls : List (Lookup F)) : List (Lookup F) :=
  ls.filter (·.bus.isNone) ++
    (buses ls).flatMap fun b ↦ packBus budget (ls.filter (·.bus == some b))

/-- Every tuple of a bus's packed lookups is a tuple of one of its lookups. -/
theorem packBus_tuples (budget : Nat) (S : List (Lookup F)) :
    ∀ ms : List (Lookup F), (∀ m ∈ ms, m ∈ S) →
      ∀ l ∈ packBus budget ms, ∀ x ∈ l.tuples, ∃ m ∈ S, x ∈ m.tuples
  | [], _ => fun _ hl ↦ nomatch hl
  | l :: ls, hS => by
    let Q (r : List (Lookup F) × Lookup F) : Prop :=
      ∀ c ∈ r.1 ++ [r.2], ∀ x ∈ c.tuples, ∃ m ∈ S, x ∈ m.tuples
    suffices h : ∀ (ms : List (Lookup F)) (r : List (Lookup F) × Lookup F), (∀ m ∈ ms, m ∈ S) →
        Q r → Q (ms.foldl (fun (cols, cur) m ↦
          let trial : Lookup F := { cur with tuples := cur.tuples ++ m.tuples }
          if lookupDegree trial ≤ budget then (cols, { trial with
            countWeight := cur.countWeight + m.countWeight })
          else (cols ++ [cur], m)) r) by
      exact h ls ([], l) (fun m hm ↦ hS m (List.mem_cons_of_mem _ hm)) (fun c hc x hx ↦ by
        simp only [List.nil_append, List.mem_singleton] at hc
        exact ⟨l, hS l List.mem_cons_self, hc ▸ hx⟩)
    intro ms
    induction ms with
    | nil => exact fun _ _ hr ↦ hr
    | cons m ms ih =>
      intro r hms hr
      rw [List.foldl_cons]
      refine ih _ (fun m' hm' ↦ hms m' (List.mem_cons_of_mem _ hm')) ?_
      have hm := hms m List.mem_cons_self
      obtain ⟨cols, cur⟩ := r
      dsimp only
      split
      · intro c hc x hx
        rcases List.mem_append.mp hc with hc | hc
        · exact hr c (List.mem_append_left _ hc) x hx
        · rw [List.mem_singleton] at hc
          subst hc
          rcases List.mem_append.mp hx with hx | hx
          · exact hr cur (List.mem_append_right _ (List.mem_singleton_self _)) x hx
          · exact ⟨m, hm, hx⟩
      · intro c hc x hx
        rcases List.mem_append.mp hc with hc | hc
        · exact hr c hc x hx
        · rw [List.mem_singleton] at hc
          dsimp only at hc
          subst hc
          exact ⟨_, hm, hx⟩

/-- Every tuple of a packed lookup is a tuple of one of the lookups. -/
theorem packSameBus_tuples (budget : Nat) (ls : List (Lookup F)) :
    ∀ l ∈ packSameBus budget ls, ∀ x ∈ l.tuples, ∃ m ∈ ls, x ∈ m.tuples := by
  intro l hl x hx
  rcases List.mem_append.mp hl with hl | hl
  · exact ⟨l, (List.mem_filter.mp hl).1, hx⟩
  · obtain ⟨b, -, hl⟩ := List.mem_flatMap.mp hl
    exact packBus_tuples budget ls _ (fun m hm ↦ (List.mem_filter.mp hm).1) l hl x hx

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
