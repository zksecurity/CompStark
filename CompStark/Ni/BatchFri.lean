/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BatchRun
public import CompStark.Ni.BcsFri
public import CompStark.Sound.FriRun

/-! # FRI's query checks with injected words

The interactive oracle proof's FRI (`FriGame.Rounds.schedule`) folds by Plonky3's schedule
(`arities_schedule`: its arities are `foldSchedule`'s). `query_run`: if a query's folds pass
their checks against binding commitments, from the reduced opening of the tallest height, adding
each shorter height's reduced opening when they reach it, and end at the final polynomial, then
the query's point is accepted by FRI's run on the extracted words (`FriGame.Rounds.run`), at the
folding challenges in ArkLib's coordinate, and the run's first word holds the tallest reduced
opening there. The injected words are the reduced openings divided by the shift of the domain
they are injected on, as ArkLib folds at `s β` where Plonky3 folds at `β`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound Polynomial FriGame FriInject

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The schedule's arities -/

namespace FriRounds

variable {K : Type}

/-- The log arities of the folds of FRI's rounds. -/
def arities : {n : ℕ} → Rounds K n → List ℕ
  | _, .final => []
  | _, .fold k _ _ rest => k :: arities rest

theorem length_arities : ∀ {n : ℕ} (r : Rounds K n), (arities r).length = r.numFolds
  | _, .final => rfl
  | _, .fold _ _ _ rest => congrArg (· + 1) (length_arities rest)

theorem foldSchedule_cons (maxLogArity logFinal fuel n m : ℕ) (rest : List ℕ)
    (hn : ¬ n ≤ logFinal) :
    foldSchedule maxLogArity logFinal (fuel + 1) (n :: m :: rest) =
      Rounds.logArity maxLogArity logFinal n (m :: rest) :: foldSchedule maxLogArity logFinal fuel
        (if m = n - Rounds.logArity maxLogArity logFinal n (m :: rest) then
          (n - Rounds.logArity maxLogArity logFinal n (m :: rest)) :: rest
        else (n - Rounds.logArity maxLogArity logFinal n (m :: rest)) :: m :: rest) := by
  simp only [foldSchedule, ite_eq_right_of_eq_false _ _ (eq_false hn), List.head?_cons,
    Option.some.injEq, List.tail_cons, List.headD_cons]
  rfl

/-- **The rounds fold by Plonky3's schedule.** -/
theorem arities_schedule (maxLogArity logFinal : ℕ) (words : (m : ℕ) → Fin (2 ^ m) → K) :
    ∀ (fuel n : ℕ) (heights : List ℕ),
      arities (Rounds.schedule maxLogArity logFinal words fuel n heights) =
        foldSchedule maxLogArity logFinal fuel (n :: heights)
  | 0, _, _ => rfl
  | fuel + 1, n, heights => by
    by_cases hfin : n ≤ logFinal
    · simp only [Rounds.schedule, ite_eq_left_of_eq_true _ _ (eq_true hfin), arities, foldSchedule]
    have ih := arities_schedule maxLogArity logFinal words fuel
    match heights with
    | [] =>
      simp only [Rounds.schedule, ite_eq_right_of_eq_false _ _ (eq_false hfin), foldSchedule,
        arities, Rounds.logArity, List.head?_nil, reduceCtorEq, ↓reduceIte, ih]
    | m :: rest =>
      rw [foldSchedule_cons _ _ _ _ _ _ hfin]
      simp only [Rounds.schedule, ite_eq_right_of_eq_false _ _ (eq_false hfin)]
      by_cases hm : m = n - Rounds.logArity maxLogArity logFinal n (m :: rest)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hm)]
        simp only [arities, ih]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), ite_eq_right_of_eq_false _ _ (eq_false hm)]
        simp only [arities, ih]

end FriRounds

/-- One step of the schedule above the final height: a fold by `logArity`, injecting the next
input when its height is reached, as Plonky3's schedule folds. -/
theorem schedule_step {K : Type} (ma lf fuel n : ℕ) (W : (m : ℕ) → Fin (2 ^ m) → K)
    (heights : List ℕ) (hn : ¬ n ≤ lf) :
    let la := Rounds.logArity ma lf n heights
    ∃ hla : la ≤ n, ∃ heights' : List ℕ,
      foldSchedule ma lf (fuel + 1) (n :: heights) =
        la :: foldSchedule ma lf fuel ((n - la) :: heights') ∧
      ((heights = (n - la) :: heights' ∧ Rounds.schedule ma lf W (fuel + 1) n heights =
          .fold la hla (some (W (n - la))) (Rounds.schedule ma lf W fuel (n - la) heights')) ∨
        (heights' = heights ∧ heights.head? ≠ some (n - la) ∧
          Rounds.schedule ma lf W (fuel + 1) n heights =
            .fold la hla none (Rounds.schedule ma lf W fuel (n - la) heights))) := by
  cases heights with
  | nil =>
    intro la
    have hla : la ≤ n := (Rounds.logArity_le _ _ _ _).trans (Nat.sub_le _ _)
    refine ⟨hla, [], ?_, Or.inr ⟨rfl, by simp only [List.head?_nil, ne_eq, reduceCtorEq,
      not_false_eq_true], ?_⟩⟩
    · simp only [foldSchedule, ite_eq_right_of_eq_false _ _ (eq_false hn), List.head?_nil,
        reduceCtorEq, ↓reduceIte, List.headD_nil, la, Rounds.logArity]
    · simp only [Rounds.schedule, ite_eq_right_of_eq_false _ _ (eq_false hn), la]
  | cons m rest =>
    intro la
    have hla : la ≤ n := (Rounds.logArity_le _ _ _ _).trans (Nat.sub_le _ _)
    refine ⟨hla, ?_⟩
    rw [FriRounds.foldSchedule_cons _ _ _ _ _ _ hn]
    by_cases hm : m = n - la
    · refine ⟨rest, by rw [ite_eq_left_of_eq_true _ _ (eq_true hm)],
        Or.inl ⟨by rw [hm], ?_⟩⟩
      simp only [Rounds.schedule, ite_eq_right_of_eq_false _ _ (eq_false hn),
        ite_eq_left_of_eq_true _ _ (eq_true hm), la]
    · refine ⟨m :: rest, by rw [ite_eq_right_of_eq_false _ _ (eq_false hm)],
        Or.inr ⟨rfl, by simp only [List.head?_cons, ne_eq, Option.some.injEq]; exact hm, ?_⟩⟩
      simp only [Rounds.schedule, ite_eq_right_of_eq_false _ _ (eq_false hn),
        ite_eq_right_of_eq_false _ _ (eq_false hm), la]

/-! ### One fold of a query -/

section Step

/-- The points of a subdomain of a coset `c ⟨ω_n⟩`: `c ^ 2 ^ k ⟨ω_(n - k)⟩`. -/
theorem subdomain_point {n : ℕ} (D : Domain.SmoothCosetFftDomain n 𝕂) (c : 𝕂)
    (hn : n ≤ twoAdicity F) (hD : ∀ x : Fin (2 ^ n), D x = c * lift (twoAdicGen n ^ x.val))
    (k : ℕ) (hk : k ≤ n) (y : Fin (2 ^ (n - k))) :
    D.subdomain k y = c ^ 2 ^ k * lift (twoAdicGen (n - k) ^ y.val) := by
  have hy : y.val < 2 ^ n :=
    lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
  have hfold : Domain.CosetFftDomainClass.sqFoldMapGen (i := k)
      (⟨y.val, hy⟩ : Fin (2 ^ n)) = y := Fin.ext (Nat.mod_eq_of_lt y.isLt)
  have key : D.subdomain k y = D ⟨y.val, hy⟩ ^ 2 ^ k := by
    rw [← Domain.CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D), hfold]
  rw [key, hD, mul_pow, lift_pow, lift_pow, ← pow_mul]
  congr 1
  change lift (twoAdicGen n) ^ (y.val * 2 ^ k) = _
  rw [Nat.mul_comm, pow_mul, lift_twoAdicGen_pow n k hk hn]

/-- The query's point after a fold: the folded index, bit-reversed at the folded height. -/
theorem sqFoldMapGen_finMod (n la idx : ℕ) (hla : la ≤ n) :
    Domain.CosetFftDomainClass.sqFoldMapGen (i := la) (finMod n (reverseBits idx n)) =
      finMod (n - la) (reverseBits (idx >>> la) (n - la)) := by
  apply Fin.ext
  simp only [Domain.CosetFftDomainClass.sqFoldMapGen, finMod,
    Nat.mod_eq_of_lt (reverseBits_lt _ _)]
  exact reverseBits_mod idx n la hla

/-- **One fold of a query.** If fold `x` of a query at index `idx` of a domain `c ⟨ω_n⟩` passes its
checks against a binding commitment, the extracted word holds the running value at the query's
point, and its fold at `β` is ArkLib's fold of the extracted word at `c β`, at the folded point. -/
theorem fold_step (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (h : ℕ)
    (commit : Cap F)
    {n : ℕ} (D : Domain.SmoothCosetFftDomain n 𝕂) (c : 𝕂) (hn : n ≤ twoAdicity F)
    (hD : ∀ x : Fin (2 ^ n), D x = c * lift (twoAdicGen n ^ x.val))
    (x : EF × QueryFold EF) (e : EF) (idx : ℕ) (hidx : idx < 2 ^ n) (ha : x.2.logArity ≤ n)
    (hok : StepOk H h commit x (e, idx, n)) (hbind : CapBinding cache H commit) :
    let f : Fin (2 ^ n) → 𝕂 := fun z ↦ friWordAt cache commit h n x.2.logArity z.val
    f (finMod n (reverseBits idx n)) = Challenge.toSpec e ∧
      Challenge.toSpec (foldRow (idx >>> x.2.logArity) (n - x.2.logArity) x.2.logArity x.1
        (groupOf x.2 idx e)) =
        ProximityGap.foldWord D f x.2.logArity (c * Challenge.toSpec x.1)
          (finMod (n - x.2.logArity) (reverseBits (idx >>> x.2.logArity) (n - x.2.logArity))) := by
  intro f
  set a := x.2.logArity
  refine ⟨?_, ?_⟩
  · simp only [f, finMod_val (reverseBits_lt _ _)]
    exact friWordAt_eval cache H h commit x (e, idx, n) n rfl hidx ha hok hbind
  · have hpos : idx % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hgroup : groupOf x.2 idx e = (List.range (2 ^ a)).map fun k ↦
        (groupOf x.2 idx e).getD k 0 := by
      refine List.ext_getElem (by rw [List.length_map, List.length_range, length_groupOf])
        fun k h1 h2 ↦ ?_
      rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h1, Option.getD_some]
    rw [hgroup, toSpec_foldRow_eq_foldValue_of D c hn hD (n - a) a (by omega) f (idx >>> a) x.1
      (fun k ↦ (groupOf x.2 idx e).getD k 0) (fun k hk ↦ by
        simp only [f, finMod_val (reverseBits_lt _ _)]
        exact (friWordAt_group cache H h commit x e idx n hidx ha hok hbind k hk).symm)
      (idx % 2 ^ a) hpos, shiftRight_mul_add_mod, ProximityGap.foldWord,
      ← Domain.CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D),
      sqFoldMapGen_finMod n a idx ha]

end Step

/-! ### A query's folds through the rounds -/

section Query
variable (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (K I : ℕ)
  (hK : K ≤ twoAdicity F) (ma lf d : ℕ) (hd : 0 < d) (W : (m : ℕ) → Fin (2 ^ m) → 𝕂)
  (fp : Polynomial (Challenge.Spec EF))

/-- The run's acceptance at a point of a fold without an injected word. -/
theorem mem_accepting_fold {n k : ℕ} {ω : Domain.SmoothCosetFftDomain n 𝕂} (hk : k ≤ n)
    (rest : Rounds 𝕂 (n - k)) (fw : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂) (βs : ℕ → 𝕂)
    (x : Fin (2 ^ n)) :
    x ∈ (Rounds.run d hd fw fp βs ω (.fold k hk none rest)).accepting ↔
      ProximityGap.foldWord ω (fw 0 n) k (βs 0)
          (Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x) =
        (Rounds.run d hd (fun j ↦ fw (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest).initial
          (Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x) ∧
        Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x ∈
          (Rounds.run d hd (fun j ↦ fw (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k)
            rest).accepting := by
  simp only [Rounds.run, InjectTrace.accepting, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The run's acceptance at a point of a fold with an injected word. -/
theorem mem_accepting_inject {n k : ℕ} {ω : Domain.SmoothCosetFftDomain n 𝕂} (hk : k ≤ n)
    (g : Fin (2 ^ (n - k)) → 𝕂) (rest : Rounds 𝕂 (n - k)) (fw : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (βs : ℕ → 𝕂) (x : Fin (2 ^ n)) :
    x ∈ (Rounds.run d hd fw fp βs ω (.fold k hk (some g) rest)).accepting ↔
      ProximityGap.foldWord ω (fw 0 n) k (βs 0)
          (Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x) +
          βs 0 ^ 2 ^ k * g (Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x) =
        (Rounds.run d hd (fun j ↦ fw (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest).initial
          (Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x) ∧
        Domain.CosetFftDomainClass.sqFoldMapGen (i := k) x ∈
          (Rounds.run d hd (fun j ↦ fw (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k)
            rest).accepting := by
  simp only [Rounds.run, InjectTrace.accepting, Finset.mem_filter, Finset.mem_univ, true_and]


end Query

/-- **A query's folds through the rounds.** A query at index `I` of the tallest domain, of
`2 ^ K` points, in state `(ro, e, I >>> (K - n), n)` on a domain `g ^ 2 ^ (K - n) ⟨ω_n⟩`, whose
folds `l` follow the rounds' schedule and pass their checks against binding commitments, adding
the reduced openings `ro` of the injected heights, each the injected word scaled by its domain's
shift at the query's point, and end at the final polynomial: the query's point is accepted by the
run on the extracted words at the scaled challenges, and the run's first word holds `e` there. -/
theorem query_run (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (h K I : ℕ)
    (hK : K ≤ twoAdicity F) (ma lf d : ℕ) (hd : 0 < d) (W : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (fp : Polynomial 𝕂) :
    ∀ (fuel n : ℕ) (heights : List ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂)
      (l : List (EF × QueryFold EF)) (commits : List (Cap F)) (ro : List (Nat × EF)) (e : EF)
      (fw : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂) (βs : ℕ → 𝕂),
      n ≤ K → I < 2 ^ K →
      (∀ x : Fin (2 ^ n), ω x = (lift gen : 𝕂) ^ 2 ^ (K - n) * lift (twoAdicGen n ^ x.val)) →
      ro.map (·.1) = heights →
      (∀ hv ∈ ro, hv.1 ≤ K ∧ (lift gen : 𝕂) ^ 2 ^ (K - hv.1) *
        W hv.1 (finMod hv.1 (reverseBits (I >>> (K - hv.1)) hv.1)) = Challenge.toSpec hv.2) →
      l.map (·.2.logArity) = foldSchedule ma lf fuel (n :: heights) →
      (∀ (j : ℕ) (x : EF × QueryFold EF), l[j]? = some x →
        StepOk H h (commits.getD j #[]) x (foldStateR l (ro, e, I >>> (K - n), n) j).2) →
      (∀ j < l.length, CapBinding cache H (commits.getD j #[])) →
      (∀ j (hj : j < l.length), fw j = fun m z ↦
        friWordAt cache (commits.getD j #[]) h m l[j].2.logArity z.val) →
      (∀ j (hj : j < l.length), βs j = (lift gen : 𝕂) ^ 2 ^ (K -
        (foldStateR l (ro, e, I >>> (K - n), n) j).2.2.2) * Challenge.toSpec l[j].1) →
      (foldStateR l (ro, e, I >>> (K - n), n) l.length).1 = [] →
      fp.eval ((lift gen : 𝕂) ^ 2 ^ (K - (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2) *
        lift (twoAdicGen (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2 ^
          reverseBits (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.1
            (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2)) =
        Challenge.toSpec (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.1 →
      finMod n (reverseBits (I >>> (K - n)) n) ∈
          (Rounds.run d hd fw fp βs ω (Rounds.schedule ma lf W fuel n heights)).accepting ∧
        (Rounds.run d hd fw fp βs ω (Rounds.schedule ma lf W fuel n heights)).initial
          (finMod n (reverseBits (I >>> (K - n)) n)) = Challenge.toSpec e := by
  -- The final word: no folds left.
  have hterm : ∀ (n : ℕ) (heights : List ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂)
      (l : List (EF × QueryFold EF)) (ro : List (Nat × EF)) (e : EF)
      (fw : ℕ → (m : ℕ) → Fin (2 ^ m) → 𝕂) (βs : ℕ → 𝕂),
      I < 2 ^ K → n ≤ K →
      (∀ x : Fin (2 ^ n), ω x = (lift gen : 𝕂) ^ 2 ^ (K - n) * lift (twoAdicGen n ^ x.val)) →
      l = [] →
      fp.eval ((lift gen : 𝕂) ^ 2 ^ (K - (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2) *
        lift (twoAdicGen (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2 ^
          reverseBits (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.1
            (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.2.2)) =
        Challenge.toSpec (foldStateR l (ro, e, I >>> (K - n), n) l.length).2.1 →
      finMod n (reverseBits (I >>> (K - n)) n) ∈
          (Rounds.run d hd fw fp βs ω .final).accepting ∧
        (Rounds.run d hd fw fp βs ω .final).initial (finMod n (reverseBits (I >>> (K - n)) n)) =
          Challenge.toSpec e := by
    intro n heights ω l ro e fw βs hI hn hω hl hfinal
    subst hl
    simp only [List.length_nil, foldStateR_zero] at hfinal
    refine ⟨by simp only [Rounds.run, InjectTrace.accepting, Finset.mem_univ], ?_⟩
    simp only [Rounds.run, InjectTrace.initial]
    rw [hω, finMod_val (reverseBits_lt _ _)]
    exact hfinal
  intro fuel
  induction fuel with
  | zero =>
    intro n heights ω l commits ro e fw βs hn hI hω hro hW hl hsteps hbind hfw hβ hnil hfinal
    have hl0 : l = [] := List.map_eq_nil_iff.mp (by rw [hl]; rfl)
    exact hterm n heights ω l ro e fw βs hI hn hω hl0 hfinal
  | succ fuel ih =>
    intro n heights ω l commits ro e fw βs hn hI hω hro hW hl hsteps hbind hfw hβ hnil hfinal
    by_cases hfin : n ≤ lf
    · have hl0 : l = [] := List.map_eq_nil_iff.mp (by
        rw [hl, foldSchedule, ite_eq_left_of_eq_true _ _ (eq_true hfin)])
      have hs : Rounds.schedule ma lf W (fuel + 1) n heights = .final := by
        rw [Rounds.schedule, ite_eq_left_of_eq_true _ _ (eq_true hfin)]
      rw [hs]
      exact hterm n heights ω l ro e fw βs hI hn hω hl0 hfinal
    obtain ⟨hla, heights', hsch, hcase⟩ := schedule_step ma lf fuel n W heights hfin
    set la := Rounds.logArity ma lf n heights with hladef
    rw [hsch] at hl
    obtain ⟨x0, l', rfl⟩ : ∃ x0 l', l = x0 :: l' := by
      cases l with
      | nil => exact absurd hl (by simp only [List.map_nil, reduceCtorEq, not_false_eq_true])
      | cons x0 l' => exact ⟨x0, l', rfl⟩
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨hx0, hl'⟩ := hl
    set idx := I >>> (K - n) with hidx
    have hidxlt : idx < 2 ^ n := by
      rw [hidx, Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show K - n + n = K by omega]; exact hI)
    set c : 𝕂 := (lift gen : 𝕂) ^ 2 ^ (K - n) with hc
    have hst0 : foldStateR (x0 :: l') (ro, e, idx, n) 0 = (ro, e, idx, n) := foldStateR_zero _ _
    have hok0 := hsteps 0 x0 rfl
    rw [hst0] at hok0
    have hfw0 := hfw 0 (by simp only [List.length_cons]; omega)
    have hβ0 := hβ 0 (by simp only [List.length_cons]; omega)
    rw [hst0] at hβ0
    simp only [List.getElem_cons_zero] at hfw0 hβ0
    have hlaN : x0.2.logArity ≤ n := by rw [hx0]; exact hla
    obtain ⟨hf0, hfold⟩ := fold_step cache H h (commits.getD 0 #[]) ω c (by omega) hω x0 e idx
      hidxlt hlaN hok0 (hbind 0 (by simp only [List.length_cons]; omega))
    rw [hx0] at hfold
    -- The next state.
    have hidx' : idx >>> la = I >>> (K - (n - la)) := by
      rw [hidx, ← Nat.shiftRight_add]
      congr 1
      omega
    have hω' : ∀ x : Fin (2 ^ (n - la)), ω.subdomain la x =
        (lift gen : 𝕂) ^ 2 ^ (K - (n - la)) * lift (twoAdicGen (n - la) ^ x.val) := by
      intro x
      rw [subdomain_point ω c (by omega) hω la hla x, hc, ← pow_mul, ← pow_add,
        show K - n + la = K - (n - la) by omega]
    have hx' : Domain.CosetFftDomainClass.sqFoldMapGen (i := la)
        (finMod n (reverseBits idx n)) = finMod (n - la) (reverseBits (I >>> (K - (n - la)))
          (n - la)) := by
      rw [sqFoldMapGen_finMod n la idx hla, hidx']
    -- The tail's hypotheses, shifted by one fold.
    have hshift : ∀ (st1 : List (Nat × EF) × EF × Nat × Nat),
        st1 = foldStepR x0 (ro, e, idx, n) →
        ∀ j, foldStateR (x0 :: l') (ro, e, idx, n) (j + 1) = foldStateR l' st1 j :=
      fun st1 h j ↦ by rw [h, foldStateR_cons]
    have hstep_snd : (foldStepR x0 (ro, e, idx, n)).2.2 = (I >>> (K - (n - la)), n - la) := by
      rw [foldStepR_snd]
      simp only [hx0, hidx']
    have htail : ∀ j, commits.tail.getD j #[] = commits.getD (j + 1) #[] := fun j ↦ by
      cases commits <;> rfl
    -- The tail's hypotheses for a next state `st1`.
    have htailHyps : ∀ (ro1 : List (Nat × EF)) (e1 : EF),
        foldStepR x0 (ro, e, idx, n) = (ro1, e1, I >>> (K - (n - la)), n - la) →
        (∀ (j : ℕ) (x : EF × QueryFold EF), l'[j]? = some x →
          StepOk H h (commits.tail.getD j #[]) x
            (foldStateR l' (ro1, e1, I >>> (K - (n - la)), n - la) j).2) ∧
        (∀ j < l'.length, CapBinding cache H (commits.tail.getD j #[])) ∧
        (∀ j (hj : j < l'.length), (fun j ↦ fw (j + 1)) j = fun m z ↦
          friWordAt cache (commits.tail.getD j #[]) h m l'[j].2.logArity z.val) ∧
        (∀ j (hj : j < l'.length), (fun j ↦ βs (j + 1)) j = (lift gen : 𝕂) ^ 2 ^ (K -
          (foldStateR l' (ro1, e1, I >>> (K - (n - la)), n - la) j).2.2.2) *
            Challenge.toSpec l'[j].1) ∧
        foldStateR (x0 :: l') (ro, e, idx, n) (x0 :: l').length =
          foldStateR l' (ro1, e1, I >>> (K - (n - la)), n - la) l'.length := by
      intro ro1 e1 hs1
      have hsj : ∀ j, foldStateR (x0 :: l') (ro, e, idx, n) (j + 1) =
          foldStateR l' (ro1, e1, I >>> (K - (n - la)), n - la) j := fun j ↦ by
        rw [foldStateR_cons, hs1]
      refine ⟨fun j x hx ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, ?_⟩
      · rw [htail, ← hsj]
        exact hsteps (j + 1) x (by rw [List.getElem?_cons_succ]; exact hx)
      · rw [htail]
        exact hbind (j + 1) (by simp only [List.length_cons]; omega)
      · rw [htail]
        exact hfw (j + 1) (by simp only [List.length_cons]; omega)
      · rw [← hsj]
        exact hβ (j + 1) (by simp only [List.length_cons]; omega)
      · rw [List.length_cons, hsj]
    have hfold' : ProximityGap.foldWord ω (fw 0 n) la (βs 0)
        (finMod (n - la) (reverseBits (I >>> (K - (n - la))) (n - la))) =
          Challenge.toSpec (foldRow (idx >>> la) (n - la) la x0.1 (groupOf x0.2 idx e)) := by
      rw [hfw0, hβ0, ← hidx']
      simp only [hx0]
      exact hfold.symm
    have hinit : (Rounds.run d hd fw fp βs ω (Rounds.schedule ma lf W (fuel + 1) n heights)).initial
        (finMod n (reverseBits idx n)) = Challenge.toSpec e := by
      rcases hcase with ⟨-, hsr⟩ | ⟨-, -, hsr⟩ <;>
      · rw [hsr]
        simp only [Rounds.run, InjectTrace.initial, hfw0]
        exact hf0
    rcases hcase with ⟨hhe, hsr⟩ | ⟨hhe, hhead, hsr⟩
    · -- A fold that injects the next input's reduced opening.
      obtain ⟨v, ro', rfl⟩ : ∃ v ro', ro = (n - la, v) :: ro' := by
        cases ro with
        | nil => rw [hhe] at hro; exact absurd hro (by simp only [List.map_nil,
            reduceCtorEq, not_false_eq_true])
        | cons hv ro' =>
          rw [hhe, List.map_cons, List.cons.injEq] at hro
          exact ⟨hv.2, ro', by rw [← hro.1]⟩
      rw [hhe, List.map_cons, List.cons.injEq] at hro
      set e1 := foldRow (idx >>> la) (n - la) la x0.1 (groupOf x0.2 idx e) +
        Ext.powTwo x0.1 la * v with he1
      have hs1 : foldStepR x0 ((n - la, v) :: ro', e, idx, n) =
          (ro', e1, I >>> (K - (n - la)), n - la) := by
        simp only [foldStepR, hx0, beq_self_eq_true, ↓reduceIte, hidx', he1]
      obtain ⟨h1, h2, h3, h4, h5⟩ := htailHyps ro' e1 hs1
      rw [h5] at hnil hfinal
      obtain ⟨hacc, htinit⟩ := ih (n - la) heights' (ω.subdomain la) l' commits.tail ro' e1
        (fun j ↦ fw (j + 1)) (fun j ↦ βs (j + 1)) (by omega) hI hω' hro.2
        (fun hv h ↦ hW hv (List.mem_cons_of_mem _ h)) hl' h1 h2 h3 h4 hnil hfinal
      refine ⟨?_, hinit⟩
      rw [hsr, mem_accepting_inject d hd fp hla, hx']
      refine ⟨?_, hacc⟩
      rw [htinit, he1, Challenge.toSpec_add, Challenge.toSpec_mul, Ext.toSpec_powTwo, hfold',
        hβ0]
      obtain ⟨-, hwv⟩ := hW (n - la, v) List.mem_cons_self
      dsimp only at hwv
      have hW' : W (n - Rounds.logArity ma lf n heights)
          (finMod (n - la) (reverseBits (I >>> (K - (n - la))) (n - la))) =
          W (n - la) (finMod (n - la) (reverseBits (I >>> (K - (n - la))) (n - la))) := rfl
      rw [hW', ← hwv, mul_pow, ← pow_mul, ← pow_add, show K - n + la = K - (n - la) by omega]
      ring
    · -- A fold without injection.
      set e1 := foldRow (idx >>> la) (n - la) la x0.1 (groupOf x0.2 idx e) with he1
      have hs1 : foldStepR x0 (ro, e, idx, n) = (ro, e1, I >>> (K - (n - la)), n - la) := by
        have hh' : (ro.map (·.1)).head? ≠ some (n - la) := by rw [hro]; exact hhead
        have hne : ∀ hv ∈ ro.head?, hv.1 ≠ n - la := fun hv h he ↦ hh' (by
          rw [List.head?_map, h, Option.map_some, he])
        unfold foldStepR
        rcases ro with _ | ⟨hv, ro'⟩
        · simp only [hx0, hidx', he1]
        · have := hne hv rfl
          simp only [hx0, beq_eq_false_iff_ne.mpr this, Bool.false_eq_true, ↓reduceIte, hidx',
            he1]
      obtain ⟨h1, h2, h3, h4, h5⟩ := htailHyps ro e1 hs1
      rw [h5] at hnil hfinal
      obtain ⟨hacc, htinit⟩ := ih (n - la) heights (ω.subdomain la) l' commits.tail ro e1
        (fun j ↦ fw (j + 1)) (fun j ↦ βs (j + 1)) (by omega) hI hω' hro
        hW (by rw [← hhe]; exact hl') h1 h2 h3 h4 hnil hfinal
      refine ⟨?_, hinit⟩
      rw [hsr, mem_accepting_fold d hd fp hla, hx']
      refine ⟨?_, hacc⟩
      rw [htinit, he1, hfold']

end CompStark.Ni
