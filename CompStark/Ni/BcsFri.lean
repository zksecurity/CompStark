/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsFold
public import CompStark.Ni.BcsRun
public import CompStark.Merkle.Extract

/-! # FRI's committed oracles, extracted, and the query checks

The commit-phase trees of a proof, read back from a cache of hash queries, as ArkLib's FRI oracles
on `L` (`friOracles`): commitment `i`'s leaf `r` holds the group of `2 ^ arity` values of word `i`
at the indices `r 2 ^ arity + k` in bit-reversed order, and the final polynomial is the proof's,
substituted to the coset (`finalPoly`). ArkLib folds at `s_i β_i` where Plonky3 folds at `β_i`,
`s_i` the shift of word `i`'s domain (`foldChallenges`).

`query_checks`: if every fold of a query passes its checks, every accepted opening opens the
extracted rows (`Binding`), and the final polynomial matches, then every ArkLib round check passes
at the query's point and the initial oracle there is the query's batched value.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound Polynomial Montgomery.Native32 Fri.Spec

local notation "F" => KoalaBear.Fast.Field
local notation "𝔽" => KoalaBear.Field

variable {EF : Type} [Challenge EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Extraction -/

section Extract
variable (cache : Merkle.Cache F Digest)

/-- Accepted openings against `root` of matrices of one height open the rows extracted from
`cache`. -/
def Binding (H : Primitives Id) (root : Digest) : Prop :=
  ∀ (n k i : Nat) (values : List (List F)) (path : List Digest), 0 < n →
    verifyBatchH H root (List.replicate n (2 ^ k)) i values path = true →
      Merkle.extractRow cache k i root = some values.flatten

/-- The row extracted at leaf `i` of the depth-`k` tree under `root`, empty if there is none. -/
noncomputable def leafRow (k i : Nat) (root : Digest) : List F :=
  (Merkle.extractRow cache k i root).getD []

/-- The value at index `z` of a FRI word of size `2 ^ m` folded by `2 ^ a`, committed under `root`:
entry `rev z % 2 ^ a` of leaf `rev z >>> a`. -/
noncomputable def friWordAt (root : Digest) (m a z : Nat) : 𝕂 :=
  Challenge.toSpec ((unflatten (leafRow cache (m - a) (reverseBits z m >>> a) root)).getD
    (reverseBits z m % 2 ^ a) 0)

end Extract

variable (S : Iop.Setup EF)

/-- `log₂ |L|`. -/
abbrev _root_.CompStark.Iop.Setup.logSize : Nat := S.logN + S.params.logBlowup

/-- The shift of the final polynomial's domain: `g ^ 2 ^ (logN - logFinalPolyLen)`. -/
noncomputable def _root_.CompStark.Iop.Setup.finalShift : 𝕂 :=
  lift gen ^ 2 ^ (S.logN - S.params.logFinalPolyLen)

/-- The final polynomial on the coset: `∑ᵢ cᵢ (X / s) ^ i`, `s` the final domain's shift. -/
noncomputable def finalPoly (coeffs : Array EF) : 𝕂[X] :=
  ∑ i ∈ Finset.range coeffs.size,
    Polynomial.C (Challenge.toSpec (coeffs.getD i 0) * (S.finalShift)⁻¹ ^ i) * Polynomial.X ^ i

/-- The extracted FRI oracles of commitments `commits` and final polynomial `coeffs`. -/
noncomputable def friOracles (cache : Merkle.Cache F Digest) (commits : List Digest)
    (coeffs : Array EF) : ∀ j, FinalOracleStatement S.schedule S.domain j := fun j ↦
  if h : j.val = S.lastFold + 1 then
    cast (by simp only [FinalOracleStatement, h, ↓reduceIte])
      (CompPoly.CPolynomial.ringEquiv.symm (finalPoly S coeffs))
  else
    cast (by simp only [FinalOracleStatement, h, ↓reduceIte]; rfl) fun x ↦
      friWordAt (EF := EF) cache (commits.getD j 0) (S.logSize - foldingPrefix S.schedule j)
        (S.schedule ⟨j.val, by omega⟩)
        ((S.domain.subdomain (foldingPrefix S.schedule j)).equivToFinset.symm x).val

/-- The folding challenges of ArkLib's oracles: `s_j β_j`, `s_j = g ^ 2 ^ prefix_j` the shift of
word `j`'s domain. -/
noncomputable def foldChallenges (betas : List EF) : FinalStatement 𝕂 S.lastFold := fun j ↦
  lift gen ^ 2 ^ foldingPrefix S.schedule j.castSucc * Challenge.toSpec (betas.getD j 0)

theorem committedWord_friOracles (cache : Merkle.Cache F Digest) (commits : List Digest)
    (coeffs : Array EF) (i : Fin (S.lastFold + 1))
    (x : (S.domain.subdomain (foldingPrefix S.schedule i.castSucc)).toFinset) :
    committedWord S.schedule (friOracles S cache commits coeffs) i x =
      friWordAt cache (commits.getD i 0) (S.logSize - foldingPrefix S.schedule i.castSucc)
        (S.schedule i)
        ((S.domain.subdomain (foldingPrefix S.schedule i.castSucc)).equivToFinset.symm x).val := by
  unfold committedWord friOracles
  simp only [Fin.val_castSucc, show i.val ≠ S.lastFold + 1 by omega, ↓reduceDIte]
  exact congrFun (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))) x

theorem finalPolynomial_friOracles (cache : Merkle.Cache F Digest) (commits : List Digest)
    (coeffs : Array EF) :
    finalPolynomial S.schedule (friOracles S cache commits coeffs) =
      CompPoly.CPolynomial.ringEquiv.symm (finalPoly S coeffs) := by
  unfold finalPolynomial friOracles
  simp only [Fin.val_last, ↓reduceDIte]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- The extracted word `i` at the point of index `z` of its domain. -/
theorem committedFunction_friOracles (cache : Merkle.Cache F Digest) (commits : List Digest)
    (coeffs : Array EF) (i : Fin (S.lastFold + 1))
    (z : Fin (2 ^ (S.logSize - foldingPrefix S.schedule i.castSucc))) :
    committedFunction S.schedule (friOracles S cache commits coeffs) i.castSucc
        (S.domain.subdomain (foldingPrefix S.schedule i.castSucc) z) =
      friWordAt cache (commits.getD i 0) (S.logSize - foldingPrefix S.schedule i.castSucc)
        (S.schedule i) z.val := by
  rw [show S.domain.subdomain (foldingPrefix S.schedule i.castSucc) z =
    ((S.domain.subdomain (foldingPrefix S.schedule i.castSucc)).equivToFinset z).val from rfl,
    committedFunction_castSucc, committedWord_friOracles, Equiv.symm_apply_apply]

/-! ### A fold's opened group is the extracted word -/

theorem groupOf_getD (s : CommitStep EF) (index : Nat) (eval : EF) (k : Nat)
    (hk : k < 2 ^ s.logArity) :
    (groupOf s index eval).getD k 0 =
      if k < index % 2 ^ s.logArity then s.siblings.getD k 0
      else if k = index % 2 ^ s.logArity then eval else s.siblings.getD (k - 1) 0 := by
  rw [groupOf, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

theorem groupOf_pos (s : CommitStep EF) (index : Nat) (eval : EF) :
    (groupOf s index eval).getD (index % 2 ^ s.logArity) 0 = eval := by
  rw [groupOf_getD s index eval _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [lt_irrefl, ↓reduceIte]

theorem length_groupOf (s : CommitStep EF) (index : Nat) (eval : EF) :
    (groupOf s index eval).length = 2 ^ s.logArity := by
  rw [groupOf, List.length_map, List.length_range]

/-- **An accepted fold opens the extracted word.** If fold `x` passes its checks at index `I` of
height `2 ^ m` and its commitment binds, the extracted word holds the opened group around `I`. -/
theorem friWordAt_group (cache : Merkle.Cache F Digest) (H : Primitives Id)
    (x : (EF × Digest) × CommitStep EF) (e : EF) (I m : Nat) (hI : I < 2 ^ m)
    (ha : x.2.logArity ≤ m) (hok : StepOk H x (e, I, m)) (hbind : Binding cache H x.1.2)
    (k : Nat) (hk : k < 2 ^ x.2.logArity) :
    friWordAt cache x.1.2 m x.2.logArity
        (reverseBits ((I >>> x.2.logArity) * 2 ^ x.2.logArity + k) m) =
      Challenge.toSpec ((groupOf x.2 I e).getD k 0) := by
  set a := x.2.logArity
  have hshift : I >>> a < 2 ^ (m - a) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' ha]; exact hI)
  have hlt : (I >>> a) * 2 ^ a + k < 2 ^ m := by
    have : (I >>> a + 1) * 2 ^ a ≤ 2 ^ (m - a) * 2 ^ a := Nat.mul_le_mul_right _ hshift
    rw [← pow_add, Nat.sub_add_cancel ha, Nat.succ_mul] at this
    omega
  have hrow := hbind 1 (m - a) (I >>> a) _ _ Nat.one_pos hok.2
  have hdiv : ((I >>> a) * 2 ^ a + k) >>> a = I >>> a := by
    rw [Nat.shiftRight_eq_div_pow ((I >>> a) * 2 ^ a + k), Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hk, Nat.zero_add]
  have hmod : ((I >>> a) * 2 ^ a + k) % 2 ^ a = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  unfold friWordAt leafRow
  rw [Complete.reverseBits_reverseBits hlt, hdiv, hmod, hrow]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Option.getD_some,
    Complete.unflatten_flatMap]

theorem shiftRight_mul_add_mod (I a : Nat) : (I >>> a) * 2 ^ a + I % 2 ^ a = I := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]; exact Nat.div_add_mod I (2 ^ a)

theorem finMod_val {m r : Nat} (hr : r < 2 ^ m) : (finMod m r).val = r := Nat.mod_eq_of_lt hr

/-- An accepted fold's commitment holds the running value at the query's index. -/
theorem friWordAt_eval (cache : Merkle.Cache F Digest) (H : Primitives Id)
    (x : (EF × Digest) × CommitStep EF) (st : EF × Nat × Nat) (m : Nat) (hm : st.2.2 = m)
    (hI : st.2.1 < 2 ^ m) (ha : x.2.logArity ≤ m) (hok : StepOk H x st)
    (hbind : Binding cache H x.1.2) :
    friWordAt cache x.1.2 m x.2.logArity (reverseBits st.2.1 m) = Challenge.toSpec st.1 := by
  obtain ⟨e, I, m'⟩ := st
  dsimp only at hm hI ⊢
  subst hm
  have h := friWordAt_group cache H x e I m' hI ha hok hbind (I % 2 ^ x.2.logArity)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  rwa [shiftRight_mul_add_mod, groupOf_pos] at h

/-- An accepted fold computes ArkLib's fold of the extracted word, at the scaled challenge, at the
`2 ^ arity`-th power of the query's point. -/
theorem foldStep_eq_foldValue (cache : Merkle.Cache F Digest) (H : Primitives Id) (n : Nat)
    (hn : n ≤ 24) (p : Nat) (x : (EF × Digest) × CommitStep EF) (st : EF × Nat × Nat)
    (hm : st.2.2 = n - p) (hI : st.2.1 < 2 ^ (n - p)) (ha : p + x.2.logArity ≤ n)
    (hok : StepOk H x st) (hbind : Binding cache H x.1.2) :
    Challenge.toSpec (foldStep x st).1 =
      ProximityGap.foldValue ((cosetDomain (EF := EF) n hn).subdomain p)
        (fun z ↦ friWordAt cache x.1.2 (n - p) x.2.logArity z.val) x.2.logArity
        (lift gen ^ 2 ^ p * Challenge.toSpec x.1.1)
        ((cosetDomain (EF := EF) n hn).subdomain p (finMod (n - p) (reverseBits st.2.1 (n - p))) ^
          2 ^ x.2.logArity) := by
  obtain ⟨e, I, m'⟩ := st
  dsimp only at hm hI ⊢
  subst hm
  set a := x.2.logArity
  have hpos : I % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h := toSpec_foldRow_eq_foldValue n hn p (n - p - a) a (by omega) (by omega)
    (fun z ↦ friWordAt cache x.1.2 (n - p) a z.val) (I >>> a) x.1.1
    (fun j ↦ if j < I % 2 ^ a then x.2.siblings.getD j 0
      else if j = I % 2 ^ a then e else x.2.siblings.getD (j - 1) 0)
    (fun k hk ↦ by
      have hg := friWordAt_group cache H x e I (n - p) hI (by omega) hok hbind k hk
      rw [groupOf_getD _ _ _ _ hk] at hg
      rw [← hg, finMod_val (Complete.reverseBits_lt _ _)]) (I % 2 ^ a) hpos
  rw [shiftRight_mul_add_mod] at h
  exact h

/-! ### The schedule -/

theorem length_foldArities : S.foldArities.length = S.lastFold + 1 := by
  have := List.length_pos_of_ne_nil (Setup.foldArities_ne_nil S)
  unfold Iop.Setup.lastFold
  omega

theorem schedule_val (j : Nat) (hj : j < S.lastFold + 1) :
    (S.schedule ⟨j, hj⟩).val = (S.foldArities.map PNat.val)[j]'(by
      rw [List.length_map, length_foldArities]; exact hj) := by
  rw [List.getElem_map, Iop.Setup.schedule, List.getD_eq_getElem]

/-- The arities of the first `j` folds sum to ArkLib's folding prefix. -/
theorem sum_take_arities (l : List Nat) (hl : l = S.foldArities.map PNat.val) :
    ∀ (j : Nat) (hj : j < S.lastFold + 2),
      (l.take j).sum = foldingPrefix S.schedule ⟨j, hj⟩
  | 0, _ => by rw [List.take_zero, List.sum_nil]; exact (foldingPrefix_zero _).symm
  | j + 1, hj => by
    have hjl : j < l.length := by rw [hl, List.length_map, length_foldArities]; omega
    rw [List.sum_take_succ _ _ hjl, sum_take_arities l hl j (by omega),
      show (⟨j + 1, hj⟩ : Fin (S.lastFold + 2)) = (⟨j, by omega⟩ : Fin (S.lastFold + 1)).succ
        from rfl, foldingPrefix_succ, schedule_val S j (by omega)]
    simp only [hl]
    rfl

/-- FRI's folds halve `logN - logFinalPolyLen` times in total. -/
theorem foldingPrefix_last_eq :
    foldingPrefix S.schedule (Fin.last (S.lastFold + 1)) = S.logN - S.params.logFinalPolyLen := by
  rw [foldingPrefix_last, Setup.sum_schedule]

/-! ### The final polynomial -/

/-- The extracted final polynomial at the final domain's point of index `rev I` is Plonky3's
final polynomial at the subgroup's point. -/
theorem eval_finalPoly (coeffs : Array EF) (I : Nat)
    (hI : I < 2 ^ (S.params.logBlowup + S.params.logFinalPolyLen)) :
    (finalPoly S coeffs).eval (lift gen ^ 2 ^ (S.logN - S.params.logFinalPolyLen) *
        lift (twoAdicGen (S.params.logBlowup + S.params.logFinalPolyLen) ^
          reverseBits I (S.params.logBlowup + S.params.logFinalPolyLen))) =
      Challenge.toSpec (coeffs.foldr (fun c acc ↦
        acc * Ext.ofBase (powF (twoAdicGen S.logSize) (reverseBits I S.logSize)) + c) 0) := by
  set L := S.params.logBlowup + S.params.logFinalPolyLen
  have hn : S.logSize = (S.logN - S.params.logFinalPolyLen) + L := by
    have := S.folds; unfold Iop.Setup.logSize; omega
  have hpt : Challenge.toSpec (Ext.ofBase (powF (twoAdicGen S.logSize) (reverseBits I S.logSize)) :
      EF) = lift (twoAdicGen L ^ reverseBits I L) := by
    rw [Challenge.toSpec_ofBase', ← lift, Fast.powF_eq, hn, Complete.reverseBits_low L _ I hI,
      pow_mul, Nat.add_comm _ L,
      Fast.twoAdicGen_pow L _ (by have := S.valid.twoAdic; have := S.folds; omega)]
  rw [← Array.foldr_toList, Complete.toSpec_horner_list, Array.length_toList, hpt, finalPoly,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Iop.Setup.finalShift, Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, Array.getElem?_toList, mul_assoc, ← mul_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ lift_gen_ne_zero), one_mul]

/-! ### The query checks -/

/-- **The query checks.** A query at index `I` (its point of `L` is `rev I`) whose folds all pass
their checks from the batched value `e0`, against binding commitments, and whose last value is
the final polynomial at the last index, passes every ArkLib round check of the extracted oracles
at the extracted challenges, and the initial oracle holds `e0` at its point. -/
theorem query_checks (cache : Merkle.Cache F Digest) (H : Primitives Id) (betas : List EF)
    (commits : List Digest) (steps : List (CommitStep EF)) (coeffs : Array EF)
    (harity : steps.map (·.logArity) = S.foldArities.map PNat.val)
    (hbl : betas.length = steps.length) (hcl : commits.length = steps.length)
    (hbind : ∀ c ∈ commits, Binding cache H c) (I : Nat) (hI : I < 2 ^ S.logSize) (e0 : EF)
    (hsteps : ∀ j x, ((betas.zip commits).zip steps)[j]? = some x →
      StepOk H x (foldState ((betas.zip commits).zip steps) (e0, I, S.logSize) j))
    (hfinal : coeffs.foldr (fun c acc ↦ acc * Ext.ofBase (powF (twoAdicGen S.logSize)
        (reverseBits (foldState ((betas.zip commits).zip steps) (e0, I, S.logSize)
          steps.length).2.1 S.logSize)) + c) 0 =
      (foldState ((betas.zip commits).zip steps) (e0, I, S.logSize) steps.length).1) :
    finMod S.logSize (reverseBits I S.logSize) ∈
        acceptingQueries S.schedule (schedule_le S) (friOracles S cache commits coeffs)
          (foldChallenges S betas) ∧
      initialWord S.schedule (friOracles S cache commits coeffs)
        (finMod S.logSize (reverseBits I S.logSize)) = Challenge.toSpec e0 := by
  set l := (betas.zip commits).zip steps with hl
  set n := S.logSize
  set o := friOracles S cache commits coeffs
  set z0 : S.Point := finMod n (reverseBits I n)
  have hn : n ≤ 24 := S.valid.twoAdic
  have hnS : n = S.logN + S.params.logBlowup := rfl
  have hfolds := S.folds
  have hlenS : steps.length = S.lastFold + 1 := by
    rw [← List.length_map (f := (·.logArity)), harity, List.length_map, length_foldArities]
  have hlen : l.length = S.lastFold + 1 := by
    rw [hl, List.length_zip, List.length_zip, hbl, hcl, hlenS, Nat.min_self, Nat.min_self]
  have harr : l.map (·.2.logArity) = S.foldArities.map PNat.val := by
    have hsnd : l.map Prod.snd = steps :=
      List.map_snd_zip (by rw [List.length_zip, hbl, hcl, Nat.min_self])
    rw [← harity, ← hsnd, List.map_map]
    rfl
  -- The folds before fold `j`, and the state before it.
  set P : Nat → Nat := fun j ↦ ((l.take j).map (·.2.logArity)).sum with hPdef
  have hP : ∀ j (hj : j < S.lastFold + 2), P j = foldingPrefix S.schedule ⟨j, hj⟩ :=
    fun j hj ↦ by rw [hPdef]; dsimp only; rw [List.map_take]; exact sum_take_arities S _ harr j hj
  have hPle : ∀ j (hj : j < S.lastFold + 2), P j ≤ S.logN - S.params.logFinalPolyLen :=
    fun j hj ↦ by rw [hP j hj, ← Setup.sum_schedule]; exact foldingPrefix_le _ _
  have hst : ∀ j, (foldState l (e0, I, n) j).2.1 = I >>> P j ∧
      (foldState l (e0, I, n) j).2.2 = n - P j := fun j ↦ by
    rw [foldState_snd]; exact ⟨rfl, rfl⟩
  have hIlt : ∀ j, j < S.lastFold + 2 → I >>> P j < 2 ^ (n - P j) := fun j hj ↦ by
    have := hPle j hj
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' (by omega)]; exact hI)
  have hx : ∀ j (hj : j < l.length), l[j].1.2 = commits.getD j 0 ∧
      l[j].1.1 = betas.getD j 0 ∧ l[j].2.logArity = (S.schedule ⟨j, by omega⟩).val := by
    intro j hj
    have hjc : j < commits.length := by omega
    have hjb : j < betas.length := by omega
    have hjs : j < steps.length := by omega
    have harj : (l.map (·.2.logArity))[j]'(by rw [List.length_map]; exact hj) =
        (S.foldArities.map PNat.val)[j]'(by rw [List.length_map, length_foldArities]; omega) := by
      simp only [harr]
    rw [List.getElem_map] at harj
    refine ⟨?_, ?_, ?_⟩
    · simp only [hl, List.getElem_zip, List.getD_eq_getElem _ _ hjc]
    · simp only [hl, List.getElem_zip, List.getD_eq_getElem _ _ hjb]
    · rw [harj, schedule_val]
  have hPsucc : ∀ j (hj : j < l.length), P (j + 1) = P j + l[j].2.logArity := fun j hj ↦ by
    simp only [hPdef, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
  have hbindj : ∀ j (hj : j < l.length), Binding cache H l[j].1.2 := fun j hj ↦
    hbind _ (by rw [(hx j hj).1, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hokj : ∀ j (hj : j < l.length), StepOk H l[j] (foldState l (e0, I, n) j) := fun j hj ↦
    hsteps j _ (List.getElem?_eq_getElem hj)
  -- The query's point at each fold.
  have hpt : ∀ j (hj : j < S.lastFold + 2), S.domain z0 ^ 2 ^ P j =
      S.domain.subdomain (P j) (finMod (n - P j) (reverseBits (I >>> P j) (n - P j))) :=
    fun j hj ↦ domain_pow_eq n hn (P j) (by have := hPle j hj; omega) I
  -- Each fold's commitment holds the running value at the query's point.
  have hV : ∀ i : Fin (S.lastFold + 1), committedFunction S.schedule o i.castSucc
      (S.domain z0 ^ 2 ^ foldingPrefix S.schedule i.castSucc) =
        Challenge.toSpec (foldState l (e0, I, n) i.val).1 := by
    intro i
    have hi : i.val < l.length := by omega
    have hPi : P i.val = foldingPrefix S.schedule i.castSucc := hP i.val (by omega)
    have hpi := hpt i.val (by omega)
    rw [hPi] at hpi
    rw [hpi, committedFunction_friOracles, finMod_val (Complete.reverseBits_lt _ _),
      ← (hx i.val hi).1, show S.schedule i = S.schedule ⟨i.val, by omega⟩ from rfl,
      ← (hx i.val hi).2.2, ← hPi, ← (hst i.val).1]
    have ha : P i.val + l[i.val].2.logArity ≤ n := by
      have := hPle (i.val + 1) (by omega); rw [hPsucc i.val hi] at this; omega
    exact friWordAt_eval cache H l[i.val] _ (n - P i.val) (hst i.val).2
      ((hst i.val).1 ▸ hIlt i.val (by omega)) (by omega) (hokj i.val hi) (hbindj i.val hi)
  -- Each fold computes ArkLib's fold at the next point.
  have hF : ∀ i : Fin (S.lastFold + 1), ProximityGap.foldValue
      (S.domain.subdomain (foldingPrefix S.schedule i.castSucc))
      (fun z ↦ committedFunction S.schedule o i.castSucc
        (S.domain.subdomain (foldingPrefix S.schedule i.castSucc) z))
      (S.schedule i).val (foldChallenges S betas i)
      (S.domain z0 ^ 2 ^ foldingPrefix S.schedule i.succ) =
        Challenge.toSpec (foldState l (e0, I, n) (i.val + 1)).1 := by
    intro i
    have hi : i.val < l.length := by omega
    have hPi : P i.val = foldingPrefix S.schedule i.castSucc := hP i.val (by omega)
    have hPi' : P (i.val + 1) = foldingPrefix S.schedule i.succ := hP (i.val + 1) (by omega)
    have ha : P i.val + l[i.val].2.logArity ≤ n := by
      have := hPle (i.val + 1) (by omega); rw [hPsucc i.val hi] at this; omega
    have h := foldStep_eq_foldValue cache H n hn (P i.val) l[i.val] _ (hst i.val).2
      ((hst i.val).1 ▸ hIlt i.val (by omega)) ha (hokj i.val hi) (hbindj i.val hi)
    rw [← foldState_succ l _ _ hi, ← show S.domain = cosetDomain (EF := EF) n hn from rfl,
      (hst i.val).1,
      (hx i.val hi).2.2, (hx i.val hi).1, (hx i.val hi).2.1, hPi] at h
    have hpi := hpt i.val (by omega)
    rw [hPi] at hpi
    rw [← hpi, ← pow_mul, ← pow_add] at h
    simp only [Fin.eta] at h
    rw [← foldingPrefix_succ] at h
    rw [foldChallenges]
    refine (congrArg (fun f ↦ ProximityGap.foldValue _ f _ _ _) (funext fun z ↦ ?_)).trans h.symm
    exact committedFunction_friOracles S cache commits coeffs i z
  refine ⟨?_, ?_⟩
  · simp only [acceptingQueries, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [QueryRound.eval_checkRound_iff_schedule]
    change ProximityGap.foldValue _ _ _ _ (S.domain z0 ^ 2 ^ _) =
      committedFunction S.schedule o i.succ (S.domain z0 ^ 2 ^ _)
    rw [hF i]
    by_cases hlast : i.val < S.lastFold
    · have hs : i.succ = (⟨i.val + 1, by omega⟩ : Fin (S.lastFold + 1)).castSucc := rfl
      rw [hs, hV]
    · have hs : i.succ = Fin.last (S.lastFold + 1) := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_last]; omega)
      have hiK : i.val + 1 = l.length := by omega
      rw [hs, committedFunction_last, finalPolynomial_friOracles, CompPoly.CPolynomial.eval_toPoly,
        ← CompPoly.CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
      have hpl := hpt (S.lastFold + 1) (by omega)
      have hPK : P (S.lastFold + 1) = S.logN - S.params.logFinalPolyLen :=
        (hP _ (by omega)).trans (foldingPrefix_last_eq S)
      rw [show foldingPrefix S.schedule (Fin.last (S.lastFold + 1)) = P (S.lastFold + 1) from
        (hP _ (by omega)).symm, hpl]
      have hL : n - P (S.lastFold + 1) = S.params.logBlowup + S.params.logFinalPolyLen := by
        rw [hPK]; omega
      have hIfin := hIlt (S.lastFold + 1) (by omega)
      rw [show S.domain = cosetDomain (EF := EF) n hn from rfl, subdomain_finMod n hn _
        (by have := hPle (S.lastFold + 1) (by omega); omega) _ (Complete.reverseBits_lt _ _),
        hL, hPK]
      rw [hL, hPK] at hIfin
      rw [eval_finalPoly S coeffs _ hIfin, show i.val + 1 = S.lastFold + 1 by omega]
      have hf := hfinal
      rw [hlenS, (hst _).1, hPK] at hf
      rw [hf]
  · have h0 := hV 0
    rw [Fin.castSucc_zero, foldingPrefix_zero, pow_zero, pow_one, Fin.val_zero,
      foldState_zero] at h0
    exact h0

end CompStark.Ni
