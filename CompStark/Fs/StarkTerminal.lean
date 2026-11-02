/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkWords
public import CompStark.Fs.StarkChallenges
public import CompStark.Iop.StarkStateRestoration

/-! # An accepted proof passes the interactive verifier's checks

Plonky3's verifier `verifyWith` on pure primitives `H` accepts a proof only if the interactive
verifier's checks (`Setup.terminal`) pass on the execution path read off the proof
(`Setup.proofPath`): the trace, quotient and FRI layers' words extracted from a cache of hash
queries under the proof's commitments (`CompStark/Fs/StarkWords.lean`), the challenges of the run
on `H`, the opened values and the final polynomial. That is `Setup.terminal_of_verifyWith`, under
the binding of the commitments (`Fs.CapBinding`).

FRI's checks at a top position along a path are `PassesAt`: each committed word agrees with the
verifier's word at the point the position reduces to, and the last word with the final
polynomial; FRI's terminal accepts when every query passes (`eval_terminal_of_passes`). A query
whose Plonky3 folds pass against binding commitments passes along the extracted path
(`passesAt_of_steps`): Plonky3 folds the same values as ArkLib's FRI on the subgroup `⟨ω⟩`, at
the same challenges.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Fri CompStark.Sound Domain
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.TypeTree
open OracleComp OracleSpec
open Fri.Interaction (Schedule Word Reader proj foldNext injected evalCoeffs)

/-! ### FRI's checks along a path -/

section Passes
variable {K : Type} [Field K] [DecidableEq K] (top d t : ℕ) (inputs : (m : ℕ) → Fin (2 ^ m) → K)

/-- The query positions of a FRI execution path. -/
def friQueries : {n : ℕ} → (s : Schedule n) →
    (Fri.Interaction.protocol K top d t s).tree.ExecutionPath → Fin t → Fin (2 ^ top)
  | _, .final, path => path.2.1
  | _, .fold _ _ _ rest, path => friQueries rest path.2.2

/-- FRI's checks at the top position `x` along an execution path from a layer where the
verifier's word is `f`: each committed word agrees with the verifier's word at the point `x`
reduces to, and the verifier's word at the last layer with the final polynomial. -/
def PassesAt (x : Fin (2 ^ top)) : {n : ℕ} → SmoothCosetFftDomain n K → (s : Schedule n) →
    Word K n → (Fri.Interaction.protocol K top d t s).tree.ExecutionPath → Prop
  | n, ω, .final, f, path => f (proj n x) = evalCoeffs path.1 (ω (proj n x))
  | n, ω, .fold k hk inject rest, f, path => f (proj n x) = path.1 (proj n x) ∧
      PassesAt x (ω.subdomain k) rest
        (foldNext hk ω path.1 path.2.1 (injected inputs (n - k) inject)) path.2.2

set_option backward.isDefEq.respectTransparency false in
/-- FRI's terminal accepts on an execution path where every query passes the checks so far
(`chk`) and FRI's checks along the path. -/
theorem eval_terminal_of_passes : ∀ {n : ℕ} (s : Schedule n) (ω : SmoothCosetFftDomain n K)
    (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (r : Reader (K := K) top A n)
    (f : Word K n) (chk : Fin (2 ^ top) → Bool), r.Reads impl inputs f →
    (∀ x, simulateQ impl (r.check x) = chk x) →
    ∀ path : (Fri.Interaction.protocol K top d t s).tree.ExecutionPath,
      (∀ i, chk (friQueries top d t s path i) = true ∧
        PassesAt top d t inputs (friQueries top d t s path i) ω s f path) →
      evalWithAnswerFn (path.closingImpl (Fri.Interaction.protocol K top d t s).oracles A impl)
        (Fri.Interaction.terminal top d t ω A r s path.toBranchPath) = true := by
  intro n s
  induction s with
  | final =>
    intro ω A impl r f chk hr hcheck path hpass
    change simulateQ impl (r.checkAll ω path.1 path.2.1) = true
    rw [Reader.simulateQ_checkAll impl inputs hr, decide_eq_true_eq]
    intro i
    obtain ⟨hc, hp⟩ := hpass i
    rw [hcheck]
    exact (Bool.and_eq_true _ _).mpr ⟨hc, beq_iff_eq.mpr hp⟩
  | @fold m k hk inject rest ih =>
    intro ω A impl r f chk hr hcheck path hpass
    obtain ⟨word, β, path⟩ := path
    exact ih (ω.subdomain k) _ _ _ _ (fun x ↦ chk x && f (proj m x) == word (proj m x))
      (Reader.reads_fold _ inputs (Reader.reads_commit impl inputs hr word) ω k hk inject β)
      (fun x ↦ by rw [Reader.fold_check, Reader.simulateQ_commit_check impl inputs hr, hcheck])
      path fun i ↦ by
        obtain ⟨hc, hp1, hp2⟩ := hpass i
        exact ⟨(Bool.and_eq_true _ _).mpr ⟨hc, beq_iff_eq.mpr hp1⟩, hp2⟩

end Passes

/-! ### Schedules -/

/-- The log arities of a schedule's folds. -/
def scheduleArities : {n : ℕ} → Schedule n → List ℕ
  | _, .final => []
  | _, .fold k _ _ rest => k :: scheduleArities rest

/-- A schedule injects no input. -/
def NoInjection : {n : ℕ} → Schedule n → Prop
  | _, .final => True
  | _, .fold _ _ inject rest => inject = false ∧ NoInjection rest

/-- Plonky3's schedule without inputs folds by Plonky3's arities of one input. -/
theorem arities_plonky3 (maxLogArity logFinal : ℕ) : ∀ fuel n,
    scheduleArities (Schedule.plonky3 maxLogArity logFinal fuel n []) =
      foldSchedule maxLogArity logFinal fuel [n]
  | 0, _ => rfl
  | fuel + 1, n => by
    by_cases hfin : n ≤ logFinal
    · simp only [Schedule.plonky3, hfin, ↓reduceIte, scheduleArities, foldSchedule]
    · simp only [Schedule.plonky3, hfin, ↓reduceIte, scheduleArities, foldSchedule,
        Schedule.logArity, List.headD_nil, List.head?_nil, reduceCtorEq, List.cons.injEq, true_and]
      exact arities_plonky3 maxLogArity logFinal fuel _

/-- Plonky3's schedule without inputs injects none. -/
theorem noInject_plonky3 (maxLogArity logFinal : ℕ) : ∀ fuel n,
    NoInjection (Schedule.plonky3 maxLogArity logFinal fuel n [])
  | 0, _ => trivial
  | fuel + 1, n => by
    by_cases hfin : n ≤ logFinal
    · simp only [Schedule.plonky3, hfin, ↓reduceIte, NoInjection]
    · simp only [Schedule.plonky3, hfin, ↓reduceIte, NoInjection, true_and]
      exact noInject_plonky3 maxLogArity logFinal fuel _

/-! ### Plonky3's folds along the extracted path -/

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- A domain of `2 ^ m` points that is the subgroup `⟨ω_m⟩` in natural order. -/
def IsSubgroupDomain {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) : Prop :=
  m ≤ twoAdicity F ∧ ∀ x : Fin (2 ^ m), D x = lift (twoAdicGen m) ^ (x : ℕ)

theorem isSubgroupDomain_subdomain {m : ℕ} (D : SmoothCosetFftDomain m 𝕂) (k : ℕ) (hk : k ≤ m)
    (hD : IsSubgroupDomain D) : IsSubgroupDomain (D.subdomain k) := by
  obtain ⟨hm, hD⟩ := hD
  refine ⟨by omega, fun y ↦ ?_⟩
  have hy : y.val < 2 ^ m :=
    lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
  have hfold : CosetFftDomainClass.sqFoldMapGen (i := k) (⟨y.val, hy⟩ : Fin (2 ^ m)) = y :=
    Fin.ext (Nat.mod_eq_of_lt y.isLt)
  have key : (D.subdomain k) y = D ⟨y.val, hy⟩ ^ 2 ^ k := by
    rw [← CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D), hfold]
  rw [key, hD, ← pow_mul, Nat.mul_comm, pow_mul]
  change (lift (twoAdicGen m) ^ 2 ^ k) ^ (y : ℕ) = lift (twoAdicGen (m - k)) ^ (y : ℕ)
  rw [lift_twoAdicGen_pow m k hk hm]

theorem isSubgroupDomain_friDomain (S : Setup EF) : IsSubgroupDomain S.friDomain :=
  ⟨S.valid.twoAdic, subgroupDomain_apply _ S.valid.twoAdic⟩

/-- The reduction of the top position `rev I` to `2 ^ m` points is the reversal of `I`'s high
bits. -/
theorem val_proj_finMod {top m : ℕ} (hm : m ≤ top) (I : ℕ) :
    (proj m (Fs.finMod top (reverseBits I top))).val = reverseBits (I >>> (top - m)) m := by
  have h := Fs.reverseBits_mod I top (top - m) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hm] at h
  simp only [proj, Fs.finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _)]
  exact h

/-- The point of `⟨ω_top⟩` at the reversal of `J < 2 ^ m` in `top` bits is the point of
`⟨ω_m⟩` at its reversal in `m` bits. -/
theorem lift_twoAdicGen_reverseBits {top m : ℕ} (hm : m ≤ top) (htop : top ≤ twoAdicity F)
    (J : ℕ) (hJ : J < 2 ^ m) :
    (lift (twoAdicGen top ^ reverseBits J top) : 𝕂) = lift (twoAdicGen m) ^ reverseBits J m := by
  obtain ⟨r, rfl⟩ : ∃ r, top = r + m := ⟨top - m, by omega⟩
  rw [reverseBits_low m r J hJ, pow_mul, Nat.add_comm r m,
    BaseField.twoAdicGen_pow m r (by omega), Fs.lift_pow]

section Fold
variable (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (ch : ℕ)

/-- **Plonky3's fold is ArkLib's on the subgroup.** An accepted fold at index `I` of the layer of
`2 ^ m` points, whose commitment binds, computes ArkLib's fold of the extracted word on the
subgroup `⟨ω_m⟩` at Plonky3's challenge, at the `2 ^ arity`-th power of the query's point. -/
theorem toSpec_foldStep {m : ℕ} (ω : SmoothCosetFftDomain m 𝕂) (hω : IsSubgroupDomain ω)
    (commit : Cap F) (x : EF × Fs.QueryFold EF) (e : EF) (I : ℕ) (hI : I < 2 ^ m)
    (ha : x.2.logArity ≤ m) (hok : Fs.StepOk H ch commit x (e, I, m))
    (hbind : Fs.CapBinding cache H commit) :
    Challenge.toSpec (Fs.foldStep x (e, I, m)).1 =
      ProximityGap.foldValue ω (friWordOf cache ch commit m x.2.logArity) x.2.logArity
        (1 * Challenge.toSpec x.1) (ω (Fs.finMod m (reverseBits I m)) ^ 2 ^ x.2.logArity) := by
  set a := x.2.logArity
  have hpos : I % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h := Fs.toSpec_foldRow_eq_foldValue_of ω 1 hω.1
    (fun z ↦ by rw [hω.2, one_mul, Fs.lift_pow]) (m - a) a (by omega)
    (friWordOf cache ch commit m a) (I >>> a) x.1
    (fun j ↦ if j < I % 2 ^ a then x.2.siblings.getD j 0
      else if j = I % 2 ^ a then e else x.2.siblings.getD (j - 1) 0)
    (fun k hk ↦ by
      have hg := Fs.friWordAt_group cache H ch commit x e I m hI ha hok hbind k hk
      rw [Fs.groupOf_getD _ _ _ _ hk] at hg
      rw [← hg, friWordOf, Fs.finMod_val (reverseBits_lt _ _)]) (I % 2 ^ a) hpos
  rw [Fs.shiftRight_mul_add_mod] at h
  exact h

end Fold

/-! ### The extracted FRI path -/

/-- FRI's execution path read off a proof from layer `j` of a schedule: layer `j`'s word
extracted under commitment `j` (`friWordOf`) and Plonky3's folding challenge `j`, then the final
polynomial `c` and the query positions `xs`. -/
noncomputable def friPath (cache : Merkle.Cache F (Digest F)) (ch : ℕ) (commits : List (Cap F))
    (betas : List EF) {top d t : ℕ} (c : Fin d → 𝕂) (xs : Fin t → Fin (2 ^ top)) :
    {m : ℕ} → (s : Schedule m) → ℕ → (Fri.Interaction.protocol 𝕂 top d t s).tree.ExecutionPath
  | _, .final, _ => ⟨c, xs, ⟨⟩⟩
  | m, .fold k _ _ rest, j => ⟨friWordOf cache ch (commits.getD j #[]) m k,
      Challenge.toSpec (betas.getD j 0), friPath cache ch commits betas c xs rest (j + 1)⟩

theorem friQueries_friPath (cache : Merkle.Cache F (Digest F)) (ch : ℕ) (commits : List (Cap F))
    (betas : List EF) {top d t : ℕ} (c : Fin d → 𝕂) (xs : Fin t → Fin (2 ^ top)) :
    ∀ {m : ℕ} (s : Schedule m) (j : ℕ),
      friQueries top d t s (friPath cache ch commits betas c xs s j) = xs
  | _, .final, _ => rfl
  | _, .fold _ _ _ rest, j => friQueries_friPath cache ch commits betas c xs rest (j + 1)

section Query
variable (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (ch : ℕ)
  (commits : List (Cap F)) (betas : List EF) (steps : List (Fs.QueryFold EF))
  (hbl : betas.length = steps.length) (hcl : commits.length = steps.length)
  (hbind : ∀ c ∈ commits, Fs.CapBinding cache H c) {top : ℕ} (htop : top ≤ twoAdicity F)
  (I : ℕ) (hI : I < 2 ^ top) (e0 : EF)
  (hsteps : ∀ (j : ℕ) (x : EF × Fs.QueryFold EF), (betas.zip steps)[j]? = some x →
    Fs.StepOk H ch (commits.getD j #[]) x (Fs.foldState (betas.zip steps) (e0, I, top) j))
  (coeffs : Array EF) {d : ℕ} (hd : coeffs.size = d)
  (hfinal : coeffs.foldr (fun c acc ↦ acc * Ext.ofBase (powF (twoAdicGen top)
      (reverseBits (Fs.foldState (betas.zip steps) (e0, I, top) (betas.zip steps).length).2.1
        top)) + c) 0 =
    (Fs.foldState (betas.zip steps) (e0, I, top) (betas.zip steps).length).1)
  {t : ℕ} (xs : Fin t → Fin (2 ^ top))

include hbl hcl hbind htop hI hsteps hd hfinal in
/-- **A query's Plonky3 folds pass along the extracted path.** From layer `j` of a schedule
without inputs that folds by Plonky3's remaining arities, on the subgroup of the layer's
`2 ^ m` points, where the verifier's word at the query's point `rev I` is Plonky3's running value,
FRI's checks pass at `rev I` along the path read off the proof, if every Plonky3 fold of the query
passes against binding commitments and its last value is the final polynomial's. -/
theorem passesAt_of_steps (inputs : (m : ℕ) → Fin (2 ^ m) → 𝕂) :
    ∀ {m : ℕ} (s : Schedule m) (j : ℕ) (ω : SmoothCosetFftDomain m 𝕂) (f : Word 𝕂 m),
    NoInjection s → IsSubgroupDomain ω → m ≤ top → j ≤ steps.length →
    ((betas.zip steps).drop j).map (·.2.logArity) = scheduleArities s →
    (Fs.foldState (betas.zip steps) (e0, I, top) j).2 = (I >>> (top - m), m) →
    f (proj m (Fs.finMod top (reverseBits I top))) =
      Challenge.toSpec (Fs.foldState (betas.zip steps) (e0, I, top) j).1 →
    PassesAt top d t inputs (Fs.finMod top (reverseBits I top)) ω s f
      (friPath cache ch commits betas (fun i ↦ Challenge.toSpec (coeffs.getD i 0)) xs s j) := by
  set l := betas.zip steps with hl
  have hll : l.length = steps.length := by rw [hl, List.length_zip, hbl, Nat.min_self]
  intro m s
  induction s with
  | @final m =>
    intro j ω f _ hω hm hj har hst hf
    have hdrop : l.drop j = [] := List.map_eq_nil_iff.mp har
    have hjl : j = l.length := le_antisymm (by omega) (List.drop_eq_nil_iff.mp hdrop)
    subst hjl
    have hIm : I >>> (top - m) < 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.sub_add_cancel hm]; exact hI)
    change f _ = evalCoeffs (fun i : Fin d ↦ Challenge.toSpec (coeffs.getD i 0)) _
    rw [hf, ← hfinal, hst, ← Array.foldr_toList, toSpec_horner_list, Array.length_toList, hd,
      hω.2, val_proj_finMod hm, Challenge.toSpec_ofBase', powF_eq]
    dsimp only
    rw [← lift, lift_twoAdicGen_reverseBits hm htop _ hIm, evalCoeffs, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Fs.toList_getD]
  | @fold m k hk inject rest ih =>
    intro j ω f hinj hω hm hj har hst hf
    obtain ⟨rfl, hinj⟩ := hinj
    have hjl : j < l.length := by
      by_contra hjl
      rw [List.drop_eq_nil_of_le (by omega)] at har
      simp only [List.map_nil, scheduleArities, reduceCtorEq] at har
    rw [List.drop_eq_getElem_cons hjl, List.map_cons] at har
    obtain ⟨hk', har⟩ := List.cons.inj har
    set st := Fs.foldState l (e0, I, top) j with hstdef
    have hst' : st = (st.1, I >>> (top - m), m) := Prod.ext rfl hst
    have hIm : I >>> (top - m) < 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.sub_add_cancel hm]; exact hI)
    have hok : Fs.StepOk H ch (commits.getD j #[]) l[j] (st.1, I >>> (top - m), m) :=
      hst' ▸ hsteps j l[j] (List.getElem?_eq_getElem hjl)
    have hbj : Fs.CapBinding cache H (commits.getD j #[]) :=
      hbind _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    have hbeta : l[j].1 = betas.getD j 0 := by
      simp only [hl, List.getElem_zip, List.getD_eq_getElem _ _ (by omega : j < betas.length)]
    subst hk'
    have hword : friWordOf cache ch (commits.getD j #[]) m l[j].2.logArity
        (proj m (Fs.finMod top (reverseBits I top))) = Challenge.toSpec st.1 := by
      rw [friWordOf, val_proj_finMod hm]
      exact Fs.friWordAt_eval cache H ch _ l[j] (st.1, I >>> (top - m), m) m rfl hIm hk hok hbj
    refine ⟨hf.trans hword.symm, ?_⟩
    refine ih (j + 1) _ _ hinj (isSubgroupDomain_subdomain ω _ hk hω) (by omega)
      (by omega) har ?_ ?_
    · rw [Fs.foldState_succ l _ j hjl, ← hstdef, hst']
      change ((I >>> (top - m)) >>> l[j].2.logArity, m - l[j].2.logArity) = _
      rw [← Nat.shiftRight_add]
      congr 2
      omega
    · show foldNext hk ω (friWordOf cache ch (commits.getD j #[]) m l[j].2.logArity)
          (Challenge.toSpec (betas.getD j 0)) (injected inputs (m - l[j].2.logArity) false)
          (proj (m - l[j].2.logArity) (Fs.finMod top (reverseBits I top))) = _
      rw [Fs.foldState_succ l _ j hjl, ← hstdef, hst',
        toSpec_foldStep cache H ch ω hω _ l[j] st.1 _ hIm hk hok hbj,
        Fri.Interaction.foldNext_apply, hbeta, one_mul]
      simp only [Fri.Interaction.injected, Pi.zero_apply, mul_zero, add_zero]
      change ProximityGap.foldValue _ _ _ _ (ω.subdomain _ _) = _
      have hpt : proj m (Fs.finMod top (reverseBits I top)) =
          Fs.finMod m (reverseBits (I >>> (top - m)) m) :=
        Fin.ext (by rw [val_proj_finMod hm, Fs.finMod_val (reverseBits_lt _ _)])
      rw [← Fri.Interaction.pow_proj, hpt]

end Query

/-! ### The proof's execution path -/

namespace Setup
variable (S : Setup EF)

/-- The STARK's execution path read off a proof, at the setup of its length: the trace and
quotient messages under the proof's commitments, extracted from `cache` (`traceMessageOf`,
`quotientMessageOf`), the challenges `α`, `ζ` and `a` of the run on `H`, the opened values, and
FRI's path (`friPath`): the layers' words under the proof's FRI commitments, the run's folding
challenges, the proof's final polynomial and the run's query positions. -/
noncomputable def proofPath (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F) :
    S.protocol.tree.ExecutionPath :=
  ⟨S.traceMessageOf cache proof.traceCommit,
    Challenge.toSpec (Fs.alphaOf H S.params S.air vk proof pis),
    S.quotientMessageOf cache proof.quotientCommit,
    Challenge.toSpec (Fs.zetaOf H S.params S.air vk proof pis),
    Fs.openingsOf S proof.opened,
    Challenge.toSpec (Fs.batchOf H S.params S.air vk proof pis),
    friPath cache S.params.capHeight proof.fri.commits.toList
      (Fs.betasOf H S.params S.air vk proof pis)
      (fun i : Fin (2 ^ S.params.logFinalPolyLen) ↦ Challenge.toSpec (proof.fri.finalPoly.getD i 0))
      (fun j ↦ queryPoint S (Fs.querySampleOf H S.params S.air vk proof pis j))
      (S.friSchedule []) 0⟩

set_option backward.isDefEq.respectTransparency false in
/-- The verifier's checks pass on a complete execution if the constraints hold at `ζ` and FRI's
terminal accepts, closed with the trace and quotient messages. -/
theorem eval_terminal_of_fri (publicValues : List F) (T : S.TraceMessage) (α : 𝕂)
    (Q : S.QuotientMessage) (ζ : 𝕂) (o : Openings S) (a : 𝕂)
    (p : (S.friProtocol []).tree.ExecutionPath) (hcons : ConstraintsHoldAt S publicValues α ζ o)
    (hfri : evalWithAnswerFn (ExecutionPath.closingImpl (tree := (S.friProtocol []).tree) p
        (S.friProtocol []).oracles S.quotientAccess (S.messagesImpl T Q))
      (Fri.Interaction.terminal (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.friDomain S.quotientAccess (S.deepReader α ζ o a) (S.friSchedule [])
        (ExecutionPath.toBranchPath (tree := (S.friProtocol []).tree) p)) = true) :
    evalWithAnswerFn (ExecutionPath.closingImpl (tree := S.protocol.tree) ⟨T, α, Q, ζ, o, a, p⟩
        S.protocol.oracles noAccess noImpl)
      (S.terminal publicValues
        (ExecutionPath.toBranchPath (tree := S.protocol.tree) ⟨T, α, Q, ζ, o, a, p⟩)) = true := by
  have h : (@decide _ (Classical.propDecidable (ConstraintsHoldAt S publicValues α ζ o)) &&
      evalWithAnswerFn (ExecutionPath.closingImpl (tree := (S.friProtocol []).tree) p
        (S.friProtocol []).oracles S.quotientAccess (S.messagesImpl T Q))
        (Fri.Interaction.terminal (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.friDomain S.quotientAccess (S.deepReader α ζ o a) (S.friSchedule [])
        (ExecutionPath.toBranchPath (tree := (S.friProtocol []).tree) p))) = true := by
    rw [hfri, Bool.and_true]
    exact @decide_eq_true _ (Classical.propDecidable _) hcons
  unfold evalWithAnswerFn at h ⊢
  rw [terminal, simulateQ_map]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **An accepted proof passes the interactive verifier's checks.** If Plonky3's verifier on pure
primitives `H` accepts a proof of `2 ^ logN` rows whose trace, quotient and FRI commitments bind
the rows extracted from `cache` (`Fs.CapBinding`), and under whose preprocessed commitment `cache`
holds the preprocessed trace's extension, the STARK's terminal accepts on the proof's execution
path (`proofPath`). -/
theorem terminal_of_verifyWith (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN)
    (htrace : Fs.CapBinding cache H proof.traceCommit)
    (hquot : Fs.CapBinding cache H proof.quotientCommit)
    (hfri : ∀ c ∈ proof.fri.commits, Fs.CapBinding cache H c)
    (hprepBind : ∀ k ∈ vk, Fs.CapBinding cache H k.commit)
    (hprep : ∀ k ∈ vk, ∀ j < S.air.preprocessedWidth,
      Fs.committedColumn S cache k.commit j = S.preprocessedWord j)
    (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    evalWithAnswerFn ((S.proofPath cache H vk proof pis).closingImpl S.protocol.oracles noAccess
        noImpl) (S.terminal pis (S.proofPath cache H vk proof pis).toBranchPath) = true := by
  obtain ⟨htl, htn, hqc, hq4, hshape, -, -, -, -, -, ⟨st, hfriOk⟩, hcheck⟩ :=
    Fs.verifyWith_ok H S.params S.air vk proof pis h
  rw [hdb] at hcheck hshape hqc
  have hL : Fs.friLogMax S.params proof = S.logSize := by
    simp only [Fs.friLogMax, hdb, Iop.Setup.logSize]
  have hh : ∀ x ∈ openingRounds S.air vk proof (Fs.zetaOf H S.params S.air vk proof pis),
      ∀ dp ∈ x.2, dp.1.logSize + S.params.logBlowup = S.logSize := by
    intro x hx dp hdp
    rw [← hL]
    simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      rfl
    · unfold preprocessedRound at hx
      split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        rw [List.mem_singleton] at hdp
        rw [hdp]
      · exact absurd hx List.not_mem_nil
  have hok := Fs.verifyFri_ok H S.params proof.fri _ _ _ hh _ _ hfriOk
  have hstart : Fs.friStart H S.params S.air vk proof pis =
      Fs.obsList H (Fs.stateFri H S.params S.air vk proof pis)
      (DomainSeparator.friSeed F EF (foldSchedule S.params.maxLogArity
        (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize])
        (2 ^ S.params.logFinalPolyLen) S.params.commitPowBits S.params.queryPowBits
        S.params.numQueries S.logSize S.params.logBlowup S.params.maxLogArity) := by
    rw [Fs.friStart, Fs.friSeedOf, Fs.friSchedule, hL]
  dsimp only at hok
  rw [← hstart] at hok
  obtain ⟨-, hfolds, hcs, -, hfp, -, hcrlen, hq⟩ := hok
  set ar := foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
    S.logSize [S.logSize] with har
  set T := S.traceMessageOf cache proof.traceCommit
  set Q := S.quotientMessageOf cache proof.quotientCommit
  set α := Challenge.toSpec (Fs.alphaOf H S.params S.air vk proof pis)
  set ζ := Challenge.toSpec (Fs.zetaOf H S.params S.air vk proof pis)
  set o := Fs.openingsOf S proof.opened
  set a := Challenge.toSpec (Fs.batchOf H S.params S.air vk proof pis)
  set W := deepWord (S.messageProver T Q o) α ζ a
  set betas := Fs.betasOf H S.params S.air vk proof pis
  refine S.eval_terminal_of_fri pis T α Q ζ o a _
    (Fs.constraintsHoldAt_of_check S pis proof.opened _ _ hqc hcheck) ?_
  refine eval_terminal_of_passes _ _ _ (S.deepInputs W) _ _ _ _ _ W (fun _ ↦ true)
    (S.reads_deepReader T Q α ζ o a) (fun _ ↦ rfl) _ fun j ↦ ⟨rfl, ?_⟩
  rw [friQueries_friPath]
  obtain ⟨hlen, hbatch, hsteps, -, hfinal⟩ := hq j.val j.isLt
  set index := (Fs.smpBits H S.logSize (Fs.sampleStates H (Fs.chkWit H S.params.queryPowBits
    proof.fri.queryWitness (Fs.obsExts H (Fs.commitReplay (EF := EF) H S.params
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
      (Fs.friStart H S.params S.air vk proof pis)).2 proof.fri.finalPoly.toList)).2 j.val)).1
    with hindex
  have hidx : index < 2 ^ S.logSize := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpt : queryPoint S (Fs.querySampleOf H S.params S.air vk proof pis j) =
      Fs.finMod S.logSize (reverseBits index S.logSize) := by
    apply Fin.ext
    simp only [queryPoint, Fs.finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _), hindex,
      Fs.smpBits, Fs.querySampleOf, Fs.queryState]
  have hflen : proof.fri.folds.toList.length = ar.length := by
    rw [Array.length_toList, hfolds]
  set steps := Fs.querySteps j.val ar proof.fri.folds.toList
  have hslen : steps.length = ar.length := Fs.length_querySteps j.val _ _ hflen
  have hbl : betas.length = steps.length := by rw [hslen]; exact hcrlen
  have hdeep := Fs.deepWord_eq S cache H vk proof (Fs.zetaOf H S.params S.air vk proof pis)
    (Fs.batchOf H S.params S.air vk proof pis) α hdb htl htn hqc (fun ch hc ↦ hq4 ch hc) hshape
    htrace hquot hprepBind hprep _ index hidx hlen hbatch
  rw [hpt]
  refine passesAt_of_steps cache H S.params.capHeight proof.fri.commits.toList betas steps hbl
    (by rw [Array.length_toList, hcs, hslen])
    (fun c hc ↦ hfri c (Array.mem_toList_iff.mp hc)) S.valid.twoAdic index hidx _ hsteps
    proof.fri.finalPoly hfp hfinal _ (S.deepInputs W) (S.friSchedule []) 0 S.friDomain W
    (noInject_plonky3 _ _ _ _) (isSubgroupDomain_friDomain S) le_rfl (Nat.zero_le _) ?_ ?_ ?_
  · have hsnd : (betas.zip steps).map Prod.snd = steps := List.map_snd_zip (by rw [hbl])
    rw [List.drop_zero, friSchedule, arities_plonky3,
      show (betas.zip steps).map (·.2.logArity) = ((betas.zip steps).map Prod.snd).map
        (·.logArity) by rw [List.map_map]; rfl,
      hsnd, Fs.map_logArity_querySteps _ _ _ hflen, har, Nat.add_comm S.params.logBlowup]
  · rw [Fs.foldState_zero, Nat.sub_self, Nat.shiftRight_zero]
  · rw [Fs.foldState_zero]
    have hproj : proj S.logSize (Fs.finMod S.logSize (reverseBits index S.logSize)) =
        Fs.finMod S.logSize (reverseBits index S.logSize) :=
      Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
    rw [hproj]
    exact hdeep

end Setup

end CompStark.Iop
