/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.BatchWords
public import CompStark.Iop.BatchStateRestoration

/-! # An accepted batch proof passes the batch IOP's checks

Plonky3's batch verifier `verifyInstancesWith` on pure primitives `H` accepts a proof only if the
batch IOP's checks (`Batch.Setup.terminal`) pass on the execution path read off the proof
(`Batch.Setup.proofPath`). That is `Batch.Setup.terminal_of_verifyWith`, under the binding of the
commitments (`Fs.CapBindingM` for the rounds of mixed heights, `Fs.CapBinding` for FRI's layers).

FRI's checks along the path are `PassesAt` with injected words: a query whose Plonky3 folds pass
against binding commitments, adding the reduced opening of each shorter height when its folds
reach it (`Fs.foldStateR`), passes along the extracted path (`passesAt_of_stepsR`), when the
injected words at the query's point are those reduced openings.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Fri CompStark.Sound Domain
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.TypeTree
open OracleComp OracleSpec
open Fri.Interaction (Schedule Word Reader proj foldNext injected evalCoeffs)

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The FRI domain of a STARK with lookups is the subgroup `⟨ω⟩` in natural order. -/
theorem isSubgroupDomain_friDomainL {lookups : List (Stark.Lookup F)} (S : Setup EF lookups) :
    IsSubgroupDomain S.friDomain :=
  ⟨S.valid.twoAdic, subgroupDomain_apply _ S.valid.twoAdic⟩

/-! ### One fold with an injected word -/

/-- An accepted fold at index `I` of the layer of `2 ^ m` points, whose commitment binds, adds to
Plonky3's folded value `β ^ 2 ^ k` times the injected word, at the folded point of a top position
over `I`: the verifier's next word there. -/
theorem foldNext_proj (cache : MixedMerkleTree.Cache (List F) (Digest F)) (H : Primitives F Id)
    (ch : ℕ)
    {top m : ℕ} (ω : SmoothCosetFftDomain m 𝕂) (hω : IsSubgroupDomain ω) (commit : Cap F)
    (x : EF × Fs.QueryFold EF) (e : EF) (I : ℕ) (hI : I < 2 ^ m) {k : ℕ} (hxk : x.2.logArity = k)
    (ha : k ≤ m) (hok : Fs.StepOk H ch commit x (e, I, m)) (hbind : Fs.CapBinding cache H commit)
    (pt : Fin (2 ^ top)) (hX : proj m pt = Fs.finMod m (reverseBits I m)) (g : Word 𝕂 (m - k)) :
    foldNext ha ω (friWordOf cache ch commit m k) (Challenge.toSpec x.1) g (proj (m - k) pt) =
      Challenge.toSpec (Fs.foldStep x (e, I, m)).1 +
        Challenge.toSpec x.1 ^ 2 ^ k * g (proj (m - k) pt) := by
  subst hxk
  rw [Fri.Interaction.foldNext_apply, toSpec_foldStep cache H ch ω hω commit x e I hI ha hok hbind,
    one_mul]
  congr 1
  change ProximityGap.foldValue _ _ _ _ (ω.subdomain _ _) = _
  rw [← Fri.Interaction.pow_proj, hX]

/-! ### A query's folds with injected words along the extracted path -/

section Query
variable (cache : MixedMerkleTree.Cache (List F) (Digest F)) (H : Primitives F Id) (ch : ℕ)
  (commits : List (Cap F)) (betas : List EF) (steps : List (Fs.QueryFold EF))
  (hbl : betas.length = steps.length) (hcl : commits.length = steps.length)
  (hbind : ∀ c ∈ commits, Fs.CapBinding cache H c) {top : ℕ} (htop : top ≤ twoAdicity F)
  (I : ℕ) (hI : I < 2 ^ top) (st0 : List (ℕ × EF) × EF × ℕ × ℕ)
  (hsteps : ∀ (j : ℕ) (x : EF × Fs.QueryFold EF), (betas.zip steps)[j]? = some x →
    Fs.StepOk H ch (commits.getD j #[]) x (Fs.foldStateR (betas.zip steps) st0 j).2)
  (coeffs : Array EF) {d : ℕ} (hd : coeffs.size = d)
  (hfinal : coeffs.foldr (fun c acc ↦ acc * Ext.ofBase (powF (twoAdicGen top)
      (reverseBits (Fs.foldStateR (betas.zip steps) st0 (betas.zip steps).length).2.2.1
        top)) + c) 0 =
    (Fs.foldStateR (betas.zip steps) st0 (betas.zip steps).length).2.1)
  {t : ℕ} (xs : Fin t → Fin (2 ^ top))

include hbl hcl hbind htop hI hsteps hd hfinal in
/-- **A query's Plonky3 folds with injections pass along the extracted path.** From layer `j` of
Plonky3's schedule injecting the heights `heights`, on the subgroup of the layer's `2 ^ m` points,
where the verifier's word at the query's point `rev I` is Plonky3's running value and the pending
reduced openings are those of `heights`, each the injected word at the query's point there, FRI's
checks pass at `rev I` along the path read off the proof, if every Plonky3 fold of the query
passes against binding commitments and its last value is the final polynomial's. -/
theorem passesAt_of_stepsR (inputs : (m : ℕ) → Fin (2 ^ m) → 𝕂) (ma lf : ℕ) :
    ∀ (fuel : ℕ) {m : ℕ} (heights : List ℕ) (j : ℕ)
    (ω : SmoothCosetFftDomain m 𝕂) (f : Word 𝕂 m),
    IsSubgroupDomain ω → m ≤ top → j ≤ steps.length →
    ((betas.zip steps).drop j).map (·.2.logArity) = foldSchedule ma lf fuel (m :: heights) →
    (Fs.foldStateR (betas.zip steps) st0 j).2.2 = (I >>> (top - m), m) →
    (Fs.foldStateR (betas.zip steps) st0 j).1.map (·.1) = heights →
    (∀ hv ∈ (Fs.foldStateR (betas.zip steps) st0 j).1,
      inputs hv.1 (proj hv.1 (Fs.finMod top (reverseBits I top))) = Challenge.toSpec hv.2) →
    f (proj m (Fs.finMod top (reverseBits I top))) =
      Challenge.toSpec (Fs.foldStateR (betas.zip steps) st0 j).2.1 →
    PassesAt top d t inputs (Fs.finMod top (reverseBits I top)) ω
      (Schedule.plonky3 ma lf fuel m heights) f
      (friPath cache ch commits betas (fun i ↦ Challenge.toSpec (coeffs.getD i 0)) xs
        (Schedule.plonky3 ma lf fuel m heights) j) := by
  set l := betas.zip steps with hl
  have hll : l.length = steps.length := by rw [hl, List.length_zip, hbl, Nat.min_self]
  set pt := Fs.finMod top (reverseBits I top) with hX
  -- The last layer: the final polynomial.
  have hterm : ∀ {m : ℕ} (j : ℕ) (ω : SmoothCosetFftDomain m 𝕂) (f : Word 𝕂 m),
      IsSubgroupDomain ω → m ≤ top → j ≤ steps.length → l.drop j = [] →
      (Fs.foldStateR l st0 j).2.2 = (I >>> (top - m), m) →
      f (proj m pt) = Challenge.toSpec (Fs.foldStateR l st0 j).2.1 →
      PassesAt top d t inputs pt ω .final f
        (friPath cache ch commits betas (fun i ↦ Challenge.toSpec (coeffs.getD i 0)) xs
          .final j) := by
    intro m j ω f hω hm hj hdrop hst hf
    have hjl : j = l.length := le_antisymm (by omega) (List.drop_eq_nil_iff.mp hdrop)
    subst hjl
    have hst2 := congrArg Prod.fst hst
    have hIm : I >>> (top - m) < 2 ^ m := Fs.shiftRight_lt hI m hm
    change f _ = evalCoeffs (fun i : Fin d ↦ Challenge.toSpec (coeffs.getD i 0)) _
    rw [hf, ← hfinal, hst2, ← Array.foldr_toList, toSpec_horner_list, Array.length_toList, hd,
      hω.2, val_proj_finMod hm, Challenge.toSpec_ofBase', powF_eq]
    dsimp only
    rw [← lift, lift_twoAdicGen_reverseBits hm htop _ hIm, evalCoeffs, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Fs.toList_getD]
  intro fuel
  induction fuel with
  | zero =>
    intro m heights j ω f hω hm hj har hst _ _ hf
    exact hterm j ω f hω hm hj (by simpa only [foldSchedule, List.map_eq_nil_iff] using har) hst hf
  | succ fuel ih =>
    intro m heights j ω f hω hm hj har hst hro hW hf
    by_cases hfin : m ≤ lf
    · have hs : Schedule.plonky3 ma lf (fuel + 1) m heights = .final := by
        simp only [Schedule.plonky3, hfin, ↓reduceIte]
      rw [hs]
      refine hterm j ω f hω hm hj ?_ hst hf
      rw [foldSchedule, ite_eq_left_of_eq_true _ _ (eq_true hfin)] at har
      exact List.map_eq_nil_iff.mp har
    obtain ⟨la, hladef⟩ : ∃ la, la = Schedule.logArity ma lf m heights := ⟨_, rfl⟩
    have hla : la ≤ m := hladef ▸ (Schedule.logArity_le _ _ _ _).trans (Nat.sub_le _ _)
    have hjl : j < l.length := by
      by_contra hjl
      rw [List.drop_eq_nil_of_le (by omega), foldSchedule,
        ite_eq_right_of_eq_false _ _ (eq_false hfin)] at har
      exact absurd har (by simp only [List.map_nil, reduceCtorEq, not_false_eq_true])
    rw [List.drop_eq_getElem_cons hjl, List.map_cons, foldSchedule,
      ite_eq_right_of_eq_false _ _ (eq_false hfin)] at har
    obtain ⟨hk', har⟩ := List.cons.inj har
    have hk : l[j].2.logArity = la := hk'.trans (by rw [hladef]; rfl)
    have har' : ((l.drop (j + 1)).map (·.2.logArity)) = foldSchedule ma lf fuel
        (if heights.head? = some (m - la) then (m - la) :: heights.tail else (m - la) :: heights) :=
      har.trans (by rw [hladef]; rfl)
    clear har hk'
    have hsucc := Fs.foldStateR_succ l st0 j hjl
    have hok0 := hsteps j l[j] (List.getElem?_eq_getElem hjl)
    have hbj : Fs.CapBinding cache H (commits.getD j #[]) :=
      hbind _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    have hbeta : l[j].1 = betas.getD j 0 := by
      simp only [hl, List.getElem_zip, List.getD_eq_getElem _ _ (by omega : j < betas.length)]
    rcases hS : Fs.foldStateR l st0 j with ⟨ro, e, im⟩
    rw [hS] at hst hro hW hf hsucc hok0
    dsimp only at hst
    subst hst
    dsimp only at hro hW hf hok0
    have hIm : I >>> (top - m) < 2 ^ m := Fs.shiftRight_lt hI m hm
    have hpt : proj m pt = Fs.finMod m (reverseBits (I >>> (top - m)) m) :=
      Fin.ext (by rw [val_proj_finMod hm, Fs.finMod_val (reverseBits_lt _ _)])
    have hword : friWordOf cache ch (commits.getD j #[]) m la (proj m pt) = Challenge.toSpec e := by
      rw [friWordOf, val_proj_finMod hm, ← hk]
      exact Fs.friWordAt_eval cache H ch _ l[j] (e, I >>> (top - m), m) m rfl hIm (hk ▸ hla) hok0
        hbj
    have hidx' : (I >>> (top - m)) >>> la = I >>> (top - (m - la)) := by
      rw [← Nat.shiftRight_add]
      congr 1
      omega
    have hnext := foldNext_proj cache H ch ω hω (commits.getD j #[]) l[j] e _ hIm hk hla hok0 hbj
      pt hpt
    rw [hbeta] at hnext
    have hω' := isSubgroupDomain_subdomain ω la hla hω
    have hfold : ∀ ro', Fs.foldStepR l[j] (ro', e, I >>> (top - m), m) =
        match ro' with
        | (h, r) :: rest => if (h == m - la) = true then
            (rest, (Fs.foldStep l[j] (e, I >>> (top - m), m)).1 + Ext.powTwo l[j].1 la * r,
              I >>> (top - (m - la)), m - la)
          else (ro', (Fs.foldStep l[j] (e, I >>> (top - m), m)).1, I >>> (top - (m - la)), m - la)
        | [] => ([], (Fs.foldStep l[j] (e, I >>> (top - m), m)).1, I >>> (top - (m - la)),
            m - la) := by
      intro ro'
      rw [← hidx', ← hk]
      rfl
    cases heights with
    | nil =>
      have hro0 : ro = [] := List.map_eq_nil_iff.mp hro
      subst hro0
      have hs : Schedule.plonky3 ma lf (fuel + 1) m [] =
          .fold la hla false (Schedule.plonky3 ma lf fuel (m - la) []) := by
        subst hladef
        simp only [Schedule.plonky3, hfin, ↓reduceIte]
      rw [hs]
      refine ⟨hf.trans hword.symm, ?_⟩
      rw [hfold] at hsucc
      refine ih [] (j + 1) _ _ hω' (by omega) (by omega) ?_ (by rw [hsucc]) (by rw [hsucc]; rfl)
        (by rw [hsucc]; exact fun _ h ↦ absurd h List.not_mem_nil) ?_
      · simpa only [List.head?_nil, reduceCtorEq, ↓reduceIte] using har'
      · rw [hsucc]
        refine (hnext _).trans ?_
        simp only [Fri.Interaction.injected, Pi.zero_apply, mul_zero, add_zero]
    | cons h rest =>
      obtain ⟨⟨h', v⟩, ro', rfl⟩ : ∃ hv ro', ro = hv :: ro' := by
        cases ro with
        | nil => exact absurd hro (by simp only [List.map_nil, reduceCtorEq, not_false_eq_true])
        | cons hv ro' => exact ⟨hv, ro', rfl⟩
      rw [List.map_cons, List.cons.injEq] at hro
      obtain ⟨rfl, hro⟩ := hro
      rw [hfold] at hsucc
      by_cases hh : h' = m - la
      · have hs : Schedule.plonky3 ma lf (fuel + 1) m (h' :: rest) =
            .fold la hla true (Schedule.plonky3 ma lf fuel (m - la) rest) := by
          subst hladef
          simp only [Schedule.plonky3, hfin, ↓reduceIte, ← hh]
        rw [hs]
        refine ⟨hf.trans hword.symm, ?_⟩
        simp only [hh, beq_self_eq_true, ↓reduceIte] at hsucc
        refine ih rest (j + 1) _ _ hω' (by omega) (by omega) ?_ (by rw [hsucc])
          (by rw [hsucc]; exact hro)
          (by rw [hsucc]; exact fun hv h ↦ hW hv (List.mem_cons_of_mem _ h))
          ?_
        · simpa only [List.head?_cons, hh, ↓reduceIte, List.tail_cons] using har'
        · rw [hsucc]
          refine (hnext _).trans ?_
          simp only [Fri.Interaction.injected, Challenge.toSpec_add, Challenge.toSpec_mul,
            Ext.toSpec_powTwo, hbeta]
          congr 1
          have hv := hW (h', v) List.mem_cons_self
          dsimp only at hv
          rw [← hv, hh]
      · have hs : Schedule.plonky3 ma lf (fuel + 1) m (h' :: rest) =
            .fold la hla false (Schedule.plonky3 ma lf fuel (m - la) (h' :: rest)) := by
          subst hladef
          simp only [Schedule.plonky3, hfin, ↓reduceIte, hh]
        rw [hs]
        refine ⟨hf.trans hword.symm, ?_⟩
        simp only [beq_eq_false_iff_ne.mpr hh, Bool.false_eq_true, ↓reduceIte] at hsucc
        refine ih (h' :: rest) (j + 1) _ _ hω' (by omega) (by omega) ?_ (by rw [hsucc])
          (by rw [hsucc, List.map_cons, hro]) (by rw [hsucc]; exact hW) ?_
        · simpa only [List.head?_cons, Option.some.injEq, hh, ↓reduceIte] using har'
        · rw [hsucc]
          refine (hnext _).trans ?_
          simp only [Fri.Interaction.injected, Pi.zero_apply, mul_zero, add_zero]

end Query

/-! ### The batch's terminal on the proof's execution path -/

namespace Batch.Setup
open CompStark.Fs

set_option backward.isDefEq.respectTransparency false in
/-- The batch's checks pass on a complete execution if the checks in the clear pass and FRI's
terminal accepts, closed with the trace, permutation and quotient messages. -/
theorem eval_terminal_of_fri (S : Setup EF) (publicValues : Fin S.k → List F) (T : S.TraceMessage)
    (l : 𝕂 × 𝕂) (P : S.PermMessage) (τ' : S.Terminals) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : S.OpeningsMessage) (a : 𝕂) (p : S.friProtocol.tree.ExecutionPath)
    (hchecks : S.Checks publicValues l.1 l.2 (S.extendTerminals τ') α ζ o)
    (hfri : evalWithAnswerFn (ExecutionPath.closingImpl (tree := S.friProtocol.tree) p
        S.friProtocol.oracles S.quotientAccess (S.messagesImpl T P Q))
      (Fri.Interaction.terminal (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.domainSetup.friDomain S.quotientAccess
        (S.deepReader l.1 l.2 (S.extendTerminals τ') α ζ o a)
        (S.domainSetup.friSchedule S.friHeights)
        (ExecutionPath.toBranchPath (tree := S.friProtocol.tree) p)) = true) :
    evalWithAnswerFn (ExecutionPath.closingImpl (tree := S.protocol.tree)
        ⟨T, l, P, τ', α, Q, ζ, o, a, p⟩ S.protocol.oracles noAccess noImpl)
      (S.terminal publicValues
        (ExecutionPath.toBranchPath (tree := S.protocol.tree) ⟨T, l, P, τ', α, Q, ζ, o, a, p⟩)) =
      true := by
  have h : (@decide _ (Classical.propDecidable
      (S.Checks publicValues l.1 l.2 (S.extendTerminals τ') α ζ o)) &&
      evalWithAnswerFn (ExecutionPath.closingImpl (tree := S.friProtocol.tree) p
        S.friProtocol.oracles S.quotientAccess (S.messagesImpl T P Q))
      (Fri.Interaction.terminal (S.logN S.top + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.domainSetup.friDomain S.quotientAccess
        (S.deepReader l.1 l.2 (S.extendTerminals τ') α ζ o a)
        (S.domainSetup.friSchedule S.friHeights)
        (ExecutionPath.toBranchPath (tree := S.friProtocol.tree) p))) = true := by
    rw [hfri, Bool.and_true]
    exact @decide_eq_true _ (Classical.propDecidable _) hchecks
  unfold evalWithAnswerFn at h ⊢
  rw [terminal, simulateQ_map]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **An accepted batch proof passes the batch IOP's checks.** If Plonky3's batch verifier on pure
primitives `H` accepts a proof whose commitments bind the rows extracted from `cache` (the main,
quotient, preprocessed and permutation commitments at their mixed heights, `CapBindingM`, FRI's
commitments `CapBinding`), and under whose preprocessed commitment `cache` holds the preprocessed
traces' extensions, the batch's terminal accepts on the proof's execution path (`proofPath`). -/
theorem terminal_of_verifyWith (S : Setup EF) (cache : MixedMerkleTree.Cache (List F) (Digest F))
    (H : Primitives F Id) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (publicValues : Fin S.k → List F)
    (hmain : CapBindingM cache H proof.mainCommit S.params.capHeight S.logTop S.mainHeights)
    (hquot : CapBindingM cache H proof.quotientCommit S.params.capHeight S.logTop (quotHeights S))
    (hfri : ∀ c ∈ proof.fri.commits, CapBinding cache H c)
    (hprepBind : ∀ root ∈ common.preprocessed,
      CapBindingM cache H root S.params.capHeight (prepLog S) (prepHeights S))
    (hprep : ∀ root ∈ common.preprocessed, ∀ i : Fin S.k, 0 < (S.air i).preprocessedWidth →
      ∀ j < (S.air i).preprocessedWidth, ∀ r < 2 ^ (S.logN i + S.params.logBlowup),
        Merkle.matColumnCap cache root.toList S.params.capHeight (prepLog S) (prepHeights S)
          (prepWidths S) (prepIndex S i) j (S.logN i + S.params.logBlowup) r =
        (S.instanceSetup i).preprocessedWord j
          (finMod _ (reverseBits r (S.logN i + S.params.logBlowup))))
    (hpermBind : ∀ root ∈ proof.permutationCommit,
      CapBindingM cache H root S.params.capHeight (permLog S) (permHeights S))
    (h : CompStark.Batch.verifyInstancesWith H S.params S.instances common proof
      (List.ofFn publicValues) = .ok ()) :
    evalWithAnswerFn ((S.proofPath cache H common proof (List.ofFn publicValues)).closingImpl
        S.protocol.oracles noAccess noImpl)
      (S.terminal publicValues
        (S.proofPath cache H common proof (List.ofFn publicValues)).toBranchPath) = true := by
  obtain ⟨hsum, hcons, -⟩ := bcsB S cache H common proof publicValues h
  set pis := List.ofFn publicValues with hpis
  obtain ⟨hsize, -, hlsize, hnsize, htsize, -, -, hshapeZ, hprepS, hlk, -, -, -, -,
    ⟨st, hfriOk⟩, -, -⟩ :=
    verifyInstancesWith_ok H S.params S.instances common proof pis h
  obtain ⟨hpshapes, hperm, -⟩ := lookupShapeOk_spec S.params S.instances proof hlk
  have hos : proof.opened.toList.length = S.k := by
    rw [Array.length_toList, hsize, length_instances]
  rw [length_instances] at hsize hlsize hnsize htsize
  have hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
      (proof.opened.toList.getD i noOpenings) = true := by
    intro i
    have hm := hshapeZ _ (zip_instances S _ hos ▸ List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)
    exact hm
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
  have hpw := permShapes S proof hlsize hnsize htsize hpshapes
  set zeta := zetaOfB H S.params S.instances common proof pis with hzeta
  have hD := descHeights_batchRounds S common proof zeta (by rw [hsize])
  have hok := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨-, -, -, -, hfolds, hcs, -, hfp, -, hcrlen, hq⟩ := hok
  set T := S.traceMessageOf cache proof.mainCommit
  set lα := Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).1
  set lβ := Challenge.toSpec (lookupRunB H S.params S.instances common proof pis).2
  set P := S.permMessageOf cache (permRoot proof)
  set τ' := S.terminalsOf proof
  set α := Challenge.toSpec (alphaOfB H S.params S.instances common proof pis)
  set Q := S.quotientMessageOf cache proof.quotientCommit
  set ζ := Challenge.toSpec zeta
  set o := S.openingsOf proof
  set a := Challenge.toSpec (batchOfB H S.params S.instances common proof pis)
  set τ := S.extendTerminals τ'
  -- The terminals of the instances without lookups are zero.
  have hτ : ∀ i, S.extendTerminals τ' i =
      Challenge.toSpec ((proof.lookupTerminals.getD i none).getD 0) := by
    intro i
    simp only [extendTerminals]
    split
    · rfl
    · rename_i hi
      have hl : S.lookups i = [] := by
        simpa only [lookupInstances, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] using hi
      have hn := (hpw i).2.2
      rw [hl, List.isEmpty_nil, Bool.not_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hn
      rw [hn, Option.getD_none, Challenge.toSpec_zero]
  set W := S.deepWords T lα lβ P τ α Q ζ o a
  refine eval_terminal_of_fri S publicValues T (lα, lβ) P τ' α Q ζ o a _ ⟨?_, fun i ↦ ?_⟩ ?_
  · simp only [hτ]
    exact hsum
  · rw [hτ]
    exact hcons i
  refine eval_terminal_of_passes _ _ _ W _ _ _ _ _ (W _) (fun _ ↦ true)
    (S.reads_deepReader T lα lβ P τ α Q ζ o a) (fun _ ↦ rfl) _ fun j ↦ ⟨rfl, ?_⟩
  rw [friQueries_friPath]
  set rounds := CompStark.Batch.batchRounds S.instances common proof zeta with hrounds
  set alpha := batchOfB H S.params S.instances common proof pis with halpha
  set index := (smpBits H S.logTop (sampleStates H (chkWit H S.params.queryPowBits
    proof.fri.queryWitness (queryStateB H S common proof pis)).2 j.val)).1 with hindex
  have hqj : QueryOkR H S.params S.logTop alpha rounds (commitReplayB H S common proof pis).1
      proof.fri.commits.toList S.friArities proof.fri.folds.toList proof.fri.inputs.toList
      proof.fri.finalPoly j index := hq j.val j.isLt
  have hidx : index < 2 ^ S.logTop := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpt : queryPoint S.domainSetup (querySampleOfB H S common proof pis j) =
      finMod S.logTop (reverseBits index S.logTop) := by
    apply Fin.ext
    simp only [queryPoint, finMod, Nat.mod_eq_of_lt (reverseBits_lt _ _), hindex, smpBits,
      querySampleOfB]
  unfold QueryOkR at hqj
  dsimp only at hqj
  rw [hD, List.tail_cons] at hqj
  obtain ⟨hrl, hbok, hsteps, hfin, hnil, hfinal⟩ := hqj
  set rows := proof.fri.inputs.toList.map fun b ↦ (b.values.getD j.val #[]).toList with hrows
  obtain ⟨rM, rQ, rP, rR, hrs⟩ : ∃ rM rQ rP rR, rows = [rM, rQ] ++
      (match common.preprocessed with | some _ => [rP] | none => []) ++
      (match proof.permutationCommit with | some _ => [rR] | none => []) := by
    have hl := hrl
    rw [hrounds, batchRounds_cases, prepRounds, permRounds] at hl
    cases hc : common.preprocessed with
    | none =>
      cases hp : proof.permutationCommit with
      | none =>
        simp only [hc, hp, List.append_nil, List.length_cons, List.length_nil] at hl
        exact ⟨_, _, [], [], List.eq_getElem_of_length_eq_two rows hl⟩
      | some r =>
        simp only [hc, hp, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        exact ⟨_, _, [], _, List.eq_getElem_of_length_eq_three rows hl⟩
    | some root =>
      cases hp : proof.permutationCommit with
      | none =>
        simp only [hc, hp, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        exact ⟨_, _, _, [], List.eq_getElem_of_length_eq_three rows hl⟩
      | some r =>
        simp only [hc, hp, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil] at hl
        obtain ⟨a, b, c, d, hr⟩ : ∃ a b c d, rows = [a, b, c, d] := by
          match rows, hl with
          | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
        exact ⟨a, b, c, d, hr⟩
  have hzip : rows.zip rounds = [(rM, proof.mainCommit, mainMats S proof zeta),
      (rQ, proof.quotientCommit, quotMats S proof zeta)] ++
      (match common.preprocessed with | some _ => [rP] | none => []).zip
        (prepRounds S proof zeta common) ++
      (match proof.permutationCommit with | some _ => [rR] | none => []).zip
        (permRounds S proof zeta) := by
    rw [hrs, hrounds, batchRounds_cases, List.zip_append (by
      rw [prepRounds]; cases common.preprocessed <;> rfl),
      List.zip_append (by simp only [List.length_cons, List.length_nil])]
    rfl
  have hbM : BatchOkR H S.params S.logTop index (rM, proof.mainCommit, mainMats S proof zeta) :=
    hbok _ (by rw [hzip]; exact List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  have hbQ : BatchOkR H S.params S.logTop index (rQ, proof.quotientCommit, quotMats S proof zeta) :=
    hbok _ (by rw [hzip]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hbP : ∀ root, common.preprocessed = some root →
      BatchOkR H S.params S.logTop index (rP, root, prepMats S proof zeta) := by
    intro root hc
    refine hbok _ ?_
    rw [hzip]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [prepRounds, hc, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
  have hbR : ∀ root, proof.permutationCommit = some root →
      BatchOkR H S.params S.logTop index (rR, root, permMats S proof zeta) := by
    intro root hc
    refine hbok _ ?_
    rw [hzip]
    refine List.mem_append_right _ ?_
    simp only [permRounds, hc, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
  have hdeep : ∀ m, Challenge.toSpec (reducedAt S.params S.logTop index alpha
      (queryMats (rows.zip rounds)) m).2 =
        S.deepWords T lα lβ P τ α Q ζ o a m
          (finMod m (reverseBits (index >>> (S.logTop - m)) m)) := by
    intro m
    rw [hrs, hrounds]
    refine reducedAt_eq_groupDeepWord S (S.messageProver T P τ Q o) lα lβ α ζ proof
      zeta S.logTop index m rfl (fun i ↦ rfl) hsize hshape hlsize hnsize
      (fun i ↦ ⟨(hpw i).1, (hpw i).2.1⟩) common hprepS hperm rM rQ rP rR (fun x hx ↦ ?_)
      (fun i j hj ↦ ?_) (fun i c e he ↦ ?_) (fun i hp j hj ↦ ?_) (fun i hl c hcw e he ↦ ?_) alpha
    · have hx' : x ∈ rows.zip rounds := by rw [hrs, hrounds]; exact hx
      obtain ⟨-, -, -, -, h3, h4⟩ := hbok x hx'
      exact ⟨h3, h4⟩
    · rw [main_rows H S cache proof zeta hsize (fun i ↦ (hsh i).1) index rM hbM hmain i j hj]
      show _ = Merkle.matColumnCap cache proof.mainCommit.toList S.params.capHeight S.logTop
        S.mainHeights S.mainWidths i j _ (reverseBits (instPoint S S.logTop index i).val _)
      rw [reverseBits_instPoint S index hidx i]
    · rw [quot_rows H S cache proof zeta hsize (fun i ↦ ⟨(hsh i).2.2.1.trans
        (congrArg (2 ^ ·) (logChunks_eq S i).symm), (hsh i).2.2.2.1⟩) index rQ hbQ hquot i c e he]
      show _ = Merkle.matColumnCap cache proof.quotientCommit.toList S.params.capHeight S.logTop
        (quotHeights S) (quotWidths S) _ e _ (reverseBits (instPoint S S.logTop index i).val _)
      rw [reverseBits_instPoint S index hidx i]
    · cases hc : common.preprocessed with
      | none =>
        rw [hc] at hprepS
        have hany : S.instances.any (0 < ·.air.preprocessedWidth) = true :=
          List.any_eq_true.mpr ⟨⟨S.air i, S.logN i, S.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩,
            decide_eq_true hp⟩
        rw [hany] at hprepS
        exact absurd hprepS Bool.false_ne_true
      | some root =>
        rw [prep_rows H S cache proof zeta hsize (fun i ↦ (hsh i).2.2.2.2.1) index root rP
          (hbP root hc) (hprepBind root hc) i hp j hj,
          hprep root hc i hp j hj _ (shiftRight_lt hidx _ (logTop_ge S i))]
        rfl
    · cases hc : proof.permutationCommit with
      | none =>
        rw [hc, Option.isSome_none] at hperm
        have hany : CompStark.Batch.hasLookups S.instances = true :=
          List.any_eq_true.mpr ⟨⟨S.air i, S.logN i, S.lookups i⟩, List.mem_ofFn.mpr ⟨i, rfl⟩, by
            rw [← lookups_eq]
            simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
              using hl⟩
        rw [hany] at hperm
        exact absurd hperm Bool.false_ne_true
      | some root =>
        have hj : c * Challenge.d EF + e < Challenge.d EF * (S.instanceSetup i).permWidth := by
          rw [Nat.mul_comm (Challenge.d EF)]
          calc c * Challenge.d EF + e < c * Challenge.d EF + Challenge.d EF := by omega
            _ = (c + 1) * Challenge.d EF := (Nat.succ_mul _ _).symm
            _ ≤ _ := Nat.mul_le_mul_right _ hcw
        rw [perm_rows H S cache proof zeta hlsize hnsize (fun i ↦ (hpw i).1) index root rR
          (hbR root hc) (hpermBind root hc) i hl _ hj]
        show _ = Merkle.matColumnCap cache (permRoot proof).toList S.params.capHeight (permLog S)
          (permHeights S) (permWidths S) (permIndex S i) (c * Challenge.d EF + e) _
          (reverseBits (instPoint S S.logTop index i).val _)
        rw [reverseBits_instPoint S index hidx i, permRoot, hc, Option.getD_some]
  set cr := commitReplayB H S common proof pis with hcr
  set l := cr.1.zip (querySteps j.val S.friArities proof.fri.folds.toList) with hl
  set ro := S.friHeights.map fun h ↦
    (h, (reducedAt S.params S.logTop index alpha (queryMats (rows.zip rounds)) h).2) with hro
  set e0 := (reducedAt S.params S.logTop index alpha (queryMats (rows.zip rounds)) S.logTop).2
    with he0
  have hfl : proof.fri.folds.toList.length = S.friArities.length := by
    rw [Array.length_toList, hfolds]
    rfl
  have hqs := length_querySteps j.val S.friArities _ hfl
  have hlar : l.map (·.2.logArity) = S.friArities := by
    show List.map ((fun x : QueryFold EF ↦ x.logArity) ∘ Prod.snd) _ = _
    rw [← List.map_map, List.map_snd_zip (by rw [hqs]; exact hcrlen.ge),
      map_logArity_querySteps _ _ _ hfl]
  have hrom : ro.map (·.1) = S.friHeights := by
    simp only [hro, List.map_map, Function.comp_def, List.map_id']
  rw [hpt]
  refine passesAt_of_stepsR cache H S.params.capHeight proof.fri.commits.toList cr.1
    (querySteps j.val S.friArities proof.fri.folds.toList) (by rw [hqs]; exact hcrlen)
    (by rw [Array.length_toList, hcs, hqs]; rfl) (fun c hc ↦ hfri c (Array.mem_toList_iff.mp hc))
    S.domainSetup.valid.twoAdic index hidx (ro, e0, index, S.logTop) hsteps proof.fri.finalPoly
    hfp hfinal _ W S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
    S.logTop S.friHeights 0 S.domainSetup.friDomain (W _) 
    (isSubgroupDomain_friDomainL S.domainSetup) le_rfl
    (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_
  · rw [List.drop_zero, hlar, Iop.Batch.Setup.friArities, Nat.add_comm S.params.logFinalPolyLen]
  · rw [foldStateR_zero, Nat.sub_self, Nat.shiftRight_zero]
  · rw [foldStateR_zero]
    exact hrom
  · rw [foldStateR_zero]
    intro hv hmem
    obtain ⟨h', hh, rfl⟩ := List.mem_map.mp hmem
    have hle : h' ≤ S.logTop := ((fits_friHeights S).2 h' hh).2.le
    rw [hdeep h']
    congr 1
    exact Fin.ext (by rw [val_proj_finMod hle, finMod_val (reverseBits_lt _ _)])
  · rw [foldStateR_zero, hdeep, Nat.sub_self, Nat.shiftRight_zero]
    exact congrArg (W _) (Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _)))

end Batch.Setup

end CompStark.Iop
