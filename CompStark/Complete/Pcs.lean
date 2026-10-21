/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Fri
public import CompStark.Complete.Deep
public import CompStark.Stark.Verifier
public import CompStark.Stark.Prover

/-! # Honest openings of any heights verify

The commitment scheme's completeness for rounds of matrices of any heights (`verifyPcs_openPcs`):
when every committed matrix is the low-degree extension of polynomials onto its own height, at
least the final height, and is opened at points outside the base field, the verifier's
`verifyPcs` on the opened values accepts `openPcs`'s proof. The batched quotients are FRI's
inputs, one per distinct height, tallest first (`Fri.reduce`); FRI rolls each in at its height
(`verifyFri_proveFri`), the input openings are honest multi-openings of mixed heights
(`verifyInputs_honest`), and the verifier's batched quotients at a query are the prover's
(`reduceQuery_honest`).

The run lemmas both STARK layers share live here too: the prover's `openPcs` (`openPcs_run`) and
the verifier's `verifyPcs` up to the batching challenge (`verifyPcs_run`), the opened values
(`openedOf`, `honestItem_of`), and the transcript and grinding steps.
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.Complete

variable {F : Type} [BaseField F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

variable {EF : Type} [Challenge F EF]

/-- Two strictly decreasing lists of the same elements are equal. -/
theorem eq_of_pairwise_gt : ∀ (l₁ l₂ : List Nat), l₁.Pairwise (· > ·) → l₂.Pairwise (· > ·) →
    (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have hab : a = b := by
      have ha := (h a).mp List.mem_cons_self
      have hb := (h b).mpr List.mem_cons_self
      rcases List.mem_cons.mp ha with ha | ha
      · exact ha
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb.symm
      have := List.rel_of_pairwise_cons h₁ hb
      have := List.rel_of_pairwise_cons h₂ ha
      omega
    subst hab
    refine congrArg _ (eq_of_pairwise_gt l₁ l₂ h₁.of_cons h₂.of_cons fun x ↦ ?_)
    have h1 : ∀ x ∈ l₁, x < a := fun x hx ↦ List.rel_of_pairwise_cons h₁ hx
    have h2 : ∀ x ∈ l₂, x < a := fun x hx ↦ List.rel_of_pairwise_cons h₂ hx
    constructor
    · intro hx
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact absurd (h1 x hx) (Nat.lt_irrefl _)
      · exact hx'
    · intro hx
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact absurd (h2 x hx) (Nat.lt_irrefl _)
      · exact hx'

/-- Sorting tallest first and deduplicating gives a strictly decreasing list of the same
elements. -/
theorem pairwise_dedup_mergeSort (l : List Nat) :
    ((l.mergeSort fun a b ↦ b ≤ a).dedup).Pairwise (· > ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : Nat ↦ decide (b ≤ a))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hd := (hs.sublist (List.dedup_sublist _)).and (List.nodup_dedup _)
  exact hd.imp fun ⟨h1, h2⟩ ↦ by simp only [decide_eq_true_eq] at h1; omega

/-- A nonempty list has an element of largest key. -/
theorem exists_max {α : Type} (key : α → Nat) : ∀ l : List α, l ≠ [] →
    ∃ x ∈ l, ∀ y ∈ l, key y ≤ key x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_cons_self, fun y hy ↦ by rw [List.mem_singleton.mp hy]⟩
  | a :: b :: l, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max key (b :: l) (List.cons_ne_nil _ _)
    by_cases h : key a ≤ key x
    · exact ⟨x, List.mem_cons_of_mem _ hx, fun y hy ↦ by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact hmax y hy⟩
    · exact ⟨a, List.mem_cons_self, fun y hy ↦ by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · have := hmax y hy; omega⟩

theorem observeExts_append (t : Transcript F 24) (a b : List EF) :
    t.observeExts (a ++ b) = (t.observeExts a).observeExts b := by
  simp only [Transcript.observeExts, List.foldl_append]

theorem forM_observeExts (ov : List (Array EF)) (t : Transcript F 24) :
    (ov.forM fun ys ↦ pObserveExts ys.toList).run t =
      ((), t.observeExts (ov.flatMap (·.toList))) := by
  induction ov generalizing t with
  | nil => rfl
  | cons ys ov ih =>
    show (pObserveExts ys.toList >>= fun _ ↦ ov.forM fun ys ↦ pObserveExts ys.toList).run t = _
    rw [prun_bind, List.flatMap_cons, observeExts_append]
    exact ih _

/-- The values the specification opens of a matrix at its points. -/
def openedOf (b : Nat) (x : Mat F × List EF) : List (Array EF) := x.2.map (Fri.openedAt b x.1)

theorem flatMap_zip_openedOf (b : Nat) (m : Mat F) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).flatMap (·.2) =
      (openedOf b (m, zs)).flatMap (·.toList) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]

theorem mem_zip_map {α β : Type} (f : α → β) (zs : List α) :
    ∀ y ∈ zs.zip (zs.map f), y.1 ∈ zs ∧ y.2 = f y.1 := by
  induction zs with
  | nil => intro y hy; simp only [List.map_nil, List.zip_nil_right, List.not_mem_nil] at hy
  | cons z zs ih =>
    intro y hy
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := ih y hy
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- An LDE opened at points outside the base field is an honest item of the batched quotients. -/
theorem honestItem_of (b h : Nat) (m : Mat F) (zs : List EF) (ps : List (Polynomial F))
    (hm : CompStark.Mat.IsLde b h m ps) (hzs : ∀ z ∈ zs, Ext.OutsideBase z) :
    Deep.HonestItem b h (m, zs.zip (openedOf b (m, zs))) := by
  refine ⟨ps, hm, fun y hy ↦ ?_⟩
  obtain ⟨hz, hy2⟩ := mem_zip_map (Fri.openedAt b m) zs y hy
  obtain ⟨hs, hv⟩ := openedAt_isLde b h m ps y.1 hm (hzs _ hz)
  exact ⟨hzs _ hz, hy2 ▸ hs, fun j hj ↦ hy2 ▸ hv j hj⟩

theorem length_zip_openedOf (b : Nat) (m : Mat F) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).map (·.2.length) =
      (openedOf b (m, zs)).map (·.size) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, Array.length_toList] at ih ⊢
    rw [ih]

theorem forM_mats (b : Nat) (ms : List (Mat F × List EF)) (t : Transcript F 24) :
    ((ms.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))).forM
        fun x ↦ x.1.forM fun ys ↦ pObserveExts ys.toList : PM F 24 Unit).run t =
      ((), t.observeExts ((ms.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction ms generalizing t with
  | nil => rfl
  | cons x ms ih =>
    simp only [List.map_cons, List.forM]
    rw [prun_bind, forM_observeExts, ih, List.flatMap_cons,
      List.flatMap_append, observeExts_append]

theorem powTwo_ne_one {zeta : EF} (hz : Ext.OutsideBase zeta) {n : Nat} (hn : n ≤ twoAdicity F) :
    (Ext.powTwo zeta n - 1 != 0) = true := by
  rw [bne_iff_ne, ne_eq]
  intro he
  have hne := pow_ne_of_outsideBase hz (specDomain n hn) one_ne_zero
  rw [map_one, one_pow] at hne
  apply hne
  have h2 := congrArg Challenge.toSpec he
  rw [Challenge.toSpec_sub, Ext.toSpec_powTwo, Challenge.toSpec_one, Challenge.toSpec_zero,
    sub_eq_zero] at h2
  exact h2

theorem grind_canonical (t : Transcript F 24) (bits : Nat) :
    (bits != 0 || (t.grind bits).1 == 0) = true := by
  by_cases h : bits = 0
  · subst h
    simp only [Transcript.grind, ↓reduceIte, beq_self_eq_true, Bool.or_true]
  · rw [bne_iff_ne.mpr h, Bool.true_or]

/-- Maps of the commitments of rounds with the same commitments agree. -/
theorem map_fst_congr {C X Y β : Type} (g : C → β) :
    ∀ (rs : List (C × X)) (rs' : List (C × Y)),
      rs.map (·.1) = rs'.map (·.1) → (rs.map fun (c, _) ↦ g c) = rs'.map fun r ↦ g r.1
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (List.cons_ne_nil _ _).symm
  | _ :: _, [], h => absurd h (List.cons_ne_nil _ _)
  | (c, x) :: rs, (c', y) :: rs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons]
    rw [h.1, map_fst_congr g rs rs' h.2]

/-- A running maximum from at most `a` over values at most `a`, one of them `a`, is `a`. -/
theorem foldl_max_of_mem (a : Nat) : ∀ (l : List Nat) (acc : Nat), (∀ x ∈ l, x ≤ a) →
    (acc = a ∨ a ∈ l) → acc ≤ a → l.foldl max acc = a
  | [], _, _, h, _ => by
    rcases h with h | h
    · exact h
    · exact absurd h List.not_mem_nil
  | x :: l, acc, hle, h, hacc => by
    rw [List.foldl_cons]
    refine foldl_max_of_mem a l _ (fun y hy ↦ hle y (List.mem_cons_of_mem _ hy)) ?_
      (Nat.max_le.mpr ⟨hacc, hle x List.mem_cons_self⟩)
    rcases h with h | h
    · left; rw [h]; exact Nat.max_eq_left (hle x List.mem_cons_self)
    · rcases List.mem_cons.mp h with rfl | h
      · left; exact Nat.max_eq_right hacc
      · right; exact h

variable [Poseidon2Field F]

/-! ### Opening -/

theorem forM_rounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) (t : Transcript F 24) :
    ((rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))).forM
        fun os ↦ os.forM fun x ↦ x.1.forM fun ys ↦ pObserveExts ys.toList : PM F 24 Unit).run t =
      ((), t.observeExts
        ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList))) := by
  induction rounds generalizing t with
  | nil => rfl
  | cons r rounds ih =>
    simp only [List.map_cons, List.forM]
    rw [prun_bind]
    erw [forM_mats]
    rw [ih, List.flatMap_cons,
      List.flatMap_append, observeExts_append]

/-- The claimed evaluation counts of opened values: per round, per matrix, per point. -/
def countsOf (opened : List (List (List (Array EF) × Mat F × List (EF × Array EF)))) :
    List (List (List Nat)) :=
  opened.map (·.map fun x ↦ x.1.map (·.size))

theorem openPcs_run (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24) :
    (openPcs (specBackend EF) P rounds).run t =
      let opened := rounds.map fun r ↦ r.2.map fun x ↦
        (openedOf P.logBlowup x, x.1, x.2.zip (openedOf P.logBlowup x))
      let t1 := (t.observeList (DomainSeparator.pcsSeed F EF (countsOf opened)
        P.batchPowBits)).observeExts
          ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf P.logBlowup)).flatMap (·.toList))
      let g := t1.grind P.batchPowBits
      let fri := proveFri (specBackend EF) P rounds
        ((Fri.reduce (g.2.sampleExtValue : EF) (opened.flatten.map (·.2))).map (·.2)) g.1
      ((opened.map (·.map (·.1)), (fri.run (Transcript.sampleExtState EF g.2)).1),
        (fri.run (Transcript.sampleExtState EF g.2)).2) := by
  unfold openPcs
  simp only [prun_bind]
  erw [forM_rounds]
  rfl

/-! ### The verifier's observations -/

/-- The innermost body of `verifyPcs`'s observation loop. -/
def obsPts (p : EF × List EF) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) := do
  observeExts (poseidon2 F) p.2
  pure (ForInStep.yield PUnit.unit)

/-- The middle body of `verifyPcs`'s observation loop. -/
def obsMats (x : Domain F × List (EF × List EF)) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) :=
  do
  forIn x.2 PUnit.unit obsPts
  pure (ForInStep.yield PUnit.unit)

/-- The outer body of `verifyPcs`'s observation loop. -/
def obsRounds (r : Round F EF) (_ : PUnit) : M (poseidon2 F) (ForInStep PUnit) := do
  forIn r.2 PUnit.unit obsMats
  pure (ForInStep.yield PUnit.unit)

theorem verifyPcs_eq (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) : verifyPcs
    (poseidon2 F) P rounds proof = (do
      ensure (P.batchPowBits != 0 || proof.batchWitness == 0) "batch witness"
      observeList (poseidon2 F) (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits)
      forIn rounds PUnit.unit obsRounds
      ensure (← checkWitness (poseidon2 F) P.batchPowBits proof.batchWitness) "batch witness"
      let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      verifyFri (poseidon2 F) P proof rounds alpha) :=
  rfl

theorem forIn_obsPts (pts : List (EF × List EF)) (t : Transcript F 24) :
    forIn pts PUnit.unit obsPts t = .ok (PUnit.unit, t.observeExts (pts.flatMap (·.2))) := by
  induction pts generalizing t with
  | nil => rfl
  | cons p pts ih =>
    rw [forIn_cons_ok p pts _ PUnit.unit obsPts t (t.observeExts p.2)
      (bind_ok (observeExts_run t p.2)), ih,
      List.flatMap_cons, observeExts_append]

theorem forIn_obsMats (mats : List (Domain F × List (EF × List EF)))
    (t : Transcript F 24) : forIn mats PUnit.unit obsMats t =
      .ok (PUnit.unit, t.observeExts (mats.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  induction mats generalizing t with
  | nil => rfl
  | cons x mats ih =>
    have h : obsMats x PUnit.unit t =
        .ok (.yield PUnit.unit, t.observeExts (x.2.flatMap (·.2))) := by
      unfold obsMats
      rw [bind_ok (forIn_obsPts x.2 t)]
      rfl
    rw [forIn_cons_ok x mats _ PUnit.unit obsMats t _ h, ih, List.flatMap_cons,
      observeExts_append]

theorem forIn_obsRounds (rounds : List (Round F EF)) (t : Transcript F 24) :
    forIn rounds PUnit.unit obsRounds t =
      .ok (PUnit.unit,
        t.observeExts (rounds.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
  induction rounds generalizing t with
  | nil => rfl
  | cons r rounds ih =>
    have h : obsRounds r PUnit.unit t =
        .ok (.yield PUnit.unit, t.observeExts (r.2.flatMap fun x ↦ x.2.flatMap (·.2))) := by
      unfold obsRounds
      rw [bind_ok (forIn_obsMats r.2 t)]
      rfl
    rw [forIn_cons_ok r rounds _ PUnit.unit obsRounds t _ h, ih, List.flatMap_cons,
      observeExts_append]

theorem verifyPcs_run (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF)
    (t : Transcript F 24) (hbw : (P.batchPowBits != 0 || proof.batchWitness == 0) = true) :
    verifyPcs (poseidon2 F) P rounds proof t = (do
      ensure (← checkWitness (poseidon2 F) P.batchPowBits proof.batchWitness) "batch witness"
      let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      verifyFri (poseidon2 F) P proof rounds alpha)
      ((t.observeList (DomainSeparator.pcsSeed F EF (claimCounts rounds)
        P.batchPowBits)).observeExts (rounds.flatMap fun (r : Round F EF) ↦
          r.2.flatMap fun (x : Domain F × List (EF × List EF)) ↦
            x.2.flatMap fun (y : EF × List EF) ↦ y.2)) := by
  rw [verifyPcs_eq, hbw, ensure_true, pure_bind, bind_ok (observeList_run _ _),
    bind_ok (forIn_obsRounds rounds _)]

theorem observeList_bind {β : Type} (xs : List F) (f : Unit → M (poseidon2 F) β)
    (t : Transcript F 24) :
    (observeList (poseidon2 F) xs >>= f) t = f () (t.observeList xs) :=
  bind_ok (observeList_run t xs)

theorem sampleExt_bind {β : Type} (f : EF → M (poseidon2 F) β) (t : Transcript F 24) :
    ((sampleExt (poseidon2 F) : M (poseidon2 F) EF) >>= f) t = f (t.sampleExtValue : EF)
        (Transcript.sampleExtState EF t) := bind_ok (sampleExt_run t)

/-- The verifier's input checks accept the honest multi-openings of rounds of matrices of heights
`2 ^ h ≤ 2 ^ H ≤ 2 ^ logMax`, some of height `2 ^ H`. -/
theorem verifyInputs_honest (P : Params) (logMax : Nat) (indices : List Nat)
    (rounds : List (Committed F × List (Mat F × List (EF × Array EF))))
    (hidx : ∀ i ∈ indices, i < 2 ^ logMax)
    (hrounds : ∀ r ∈ rounds, r.2 ≠ [] ∧ r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧
      ∃ H ≤ logMax, (∃ x ∈ r.2, x.1.height = 2 ^ H) ∧
        ∀ x ∈ r.2, x.2 ≠ [] ∧ ∃ h ≤ H, Deep.HonestItem P.logBlowup h x)
    (t : Transcript F 24) :
    verifyInputs (poseidon2 F) P logMax indices
      (rounds.map fun r ↦ openMulti (specBackend EF) r.1
        (indices.map (· >>> (logMax - (specBackend EF).logHeight r.1))))
      (rounds.map fun r ↦ (r.1.root, r.2.map fun x ↦
        ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList))))
      t = .ok ((), t) := by
  unfold verifyInputs
  simp only [List.length_map, beq_self_eq_true, ensure_true, pure_bind, List.zip_map']
  refine (bind_ok (a := PUnit.unit) (t' := t) ?_).trans rfl
  induction rounds with
  | nil => rfl
  | cons r rounds ih =>
    obtain ⟨hne, hc, H, hH, htop, hits⟩ := hrounds r List.mem_cons_self
    rw [List.map_cons]
    refine (forIn_cons_ok _ _ _ PUnit.unit _ t t ?_).trans
      (ih fun r' hr' ↦ hrounds r' (List.mem_cons_of_mem _ hr'))
    obtain ⟨c, its⟩ := r
    dsimp only at hne hc hits htop ⊢
    subst hc
    have hmix : Fri.MixedHeights H (its.map (·.1)) := by
      refine ⟨fun m hm ↦ ?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
        obtain ⟨-, h, hh, ps, hl, -⟩ := hits x hx
        exact ⟨h, hh, hl.2.1⟩
      · obtain ⟨x, hx, hxH⟩ := htop
        exact ⟨x.1, List.mem_map_of_mem hx, hxH⟩
    have hmx : Nat.log2 (Committed.ofMats hashF compF (its.map (·.1))).maxHeight = H := by
      rw [Fri.maxHeight_mixed hmix, Nat.log2_two_pow]
    have hdims : ((its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).map fun x ↦
          (2 ^ (x.1.logSize + P.logBlowup), (x.2.headD default).2.length)) =
        (its.map (·.1)).map fun m ↦ (m.height, m.width) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨hpne, h, -, ps, hl, hpts⟩ := hits x hx
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hpne
      have hys := (hpts y (by rw [hy]; exact List.mem_cons_self)).2.1
      simp only [Function.comp_apply, hy, List.map_cons, List.headD_cons, Array.length_toList]
      rw [hys, ← hl.1, hl.2.1, Nat.log2_two_pow, Nat.sub_add_cancel hl.2.2.2.1]
    have hbatch : ((its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).map fun x ↦ x.1.logSize + P.logBlowup).foldl max 0 =
          H := by
      have hlog : ∀ x ∈ its, Nat.log2 x.1.height - P.logBlowup + P.logBlowup =
          Nat.log2 x.1.height := fun x hx ↦ by
        obtain ⟨-, h, -, ps, hl, -⟩ := hits x hx
        rw [hl.2.1, Nat.log2_two_pow, Nat.sub_add_cancel hl.2.2.2.1]
      refine foldl_max_of_mem H _ 0 (fun z hz ↦ ?_) (Or.inr ?_) (Nat.zero_le _)
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hz
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨-, h, hh, ps, hl, -⟩ := hits x hx
        dsimp only
        rw [hlog x hx, hl.2.1, Nat.log2_two_pow]; exact hh
      · obtain ⟨x, hx, hxH⟩ := htop
        refine List.mem_map.mpr ⟨_, List.mem_map_of_mem hx, ?_⟩
        dsimp only
        rw [hlog x hx, hxH, Nat.log2_two_pow]
    have hrows : ∀ i, ((Committed.ofMats hashF compF (its.map (·.1))).openAt i).values.size =
        its.length := fun i ↦ by
      rw [Fri.openAt_values_mixed hmix, List.size_toArray, List.length_map, List.length_map]
    have hpts : (its.map fun x ↦ ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F),
        x.2.map fun y ↦ (y.1, y.2.toList))).all (fun x ↦ !x.2.isEmpty) = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, List.map_eq_nil_iff]
      exact fun x hx ↦ (hits x hx).1
    simp only [hmx, openMulti, List.size_toArray, List.length_map, beq_self_eq_true, ensure_true,
      pure_bind, hdims, hbatch, hpts]
    set idx' := indices.map (· >>> (logMax - H)) with hidx'
    have hall : ((idx'.map
        (Committed.ofMats hashF compF (its.map (·.1))).openAt).map (·.values)).toArray.all
          (fun a ↦ a.size == its.length) 0 indices.length = true := by
      rw [show indices.length = ((idx'.map
        (Committed.ofMats hashF compF (its.map (·.1))).openAt).map (·.values)).toArray.size by
          simp only [hidx', List.size_toArray, List.length_map], List.all_toArray]
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq]
      exact fun i _ ↦ hrows i
    rw [hall, ensure_true, pure_bind]
    have hv := Fri.verifyMulti_openMulti hmix idx' fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact Deep.shiftRight_lt (hidx j hj) hH
    set C := Committed.ofMats hashF compF (its.map (·.1))
    have e1 : (((idx'.map ((specBackend EF).openAt C)).map (·.values)).map fun r ↦
        r.toList.map (·.toList)) =
        idx'.map fun i ↦ (C.openAt i).values.toList.map (·.toList) := by
      rw [List.map_map, List.map_map]; rfl
    have e2 : (idx'.map ((specBackend EF).openAt C)).map (·.path.toList) =
        idx'.map fun i ↦ (C.openAt i).path.toList := by
      rw [List.map_map]; rfl
    rw [bind_ok (checkMulti_eq _ _ _ _ _ t), e1, e2, hv]
    rfl


/-- The committed matrices with their points and opened values. -/
def honestRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    List (Committed F × List (Mat F × List (EF × Array EF))) :=
  rounds.map fun r ↦ (r.1, r.2.map fun x ↦ (x.1, x.2.zip (openedOf b x)))

/-- The verifier's rounds: the commitments' roots, every matrix on its trace domain with its
points and opened values. -/
def verifierRounds (b : Nat) (rounds : List (Committed F × List (Mat F × List (EF × Array EF)))) :
    List (Round F EF) :=
  rounds.map fun r ↦ (r.1.root, r.2.map fun x ↦
    ((⟨1, Nat.log2 x.1.height - b⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList)))

/-- Rounds the specification prover opens honestly: some round, each committing to a nonempty
list of matrices, each matrix the extension of polynomials onto a height not below FRI's final
height, opened at a nonempty list of points outside the base field. -/
structure HonestRounds (P : Params) (rounds : List (OpenRound (specBackend EF))) : Prop where
  nonempty : rounds ≠ []
  commits : ∀ r ∈ rounds, r.2 ≠ [] ∧ r.1 = Committed.ofMats hashF compF (r.2.map (·.1))
  points : ∀ r ∈ rounds, ∀ x ∈ r.2, x.2 ≠ [] ∧ ∀ z ∈ x.2, Ext.OutsideBase z
  lde : ∀ r ∈ rounds, ∀ x ∈ r.2, ∃ h ps, CompStark.Mat.IsLde P.logBlowup h x.1 ps ∧
    P.logBlowup + P.logFinalPolyLen ≤ h

/-- The verifier's claimed evaluation counts are the prover's. -/
theorem claimCounts_verifierRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    claimCounts (verifierRounds b (honestRounds b rounds)) =
      countsOf (rounds.map fun r ↦ r.2.map fun x ↦
        (openedOf b x, x.1, x.2.zip (openedOf b x))) := by
  simp only [claimCounts, verifierRounds, honestRounds, countsOf, List.map_map]
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  exact length_zip_openedOf b x.1 x.2

/-- The verifier observes the prover's opened values. -/
theorem flat_verifierRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    (verifierRounds b (honestRounds b rounds)).flatMap
        (fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
      (rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList) := by
  induction rounds with
  | nil => rfl
  | cons r rounds ih =>
    simp only [verifierRounds, honestRounds, List.map_cons, List.flatMap_cons,
      List.flatMap_append] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨c, ms⟩ := r
    dsimp only
    induction ms with
    | nil => rfl
    | cons x ms ihm =>
      simp only [List.map_cons, List.flatMap_cons, List.flatMap_append]
      rw [ihm, flatMap_zip_openedOf]

/-- The honest rounds' facts that the input checks and the batched quotients need. -/
theorem honestRounds_ok {P : Params} {rounds : List (OpenRound (specBackend EF))}
    (hr : HonestRounds P rounds) (logMax : Nat)
    (hmax : ∀ r ∈ rounds, ∀ x ∈ r.2, Nat.log2 x.1.height ≤ logMax) :
    ∀ r ∈ honestRounds P.logBlowup rounds, r.2 ≠ [] ∧
      r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧ ∃ H ≤ logMax,
        (∃ x ∈ r.2, x.1.height = 2 ^ H) ∧
          ∀ x ∈ r.2, x.2 ≠ [] ∧ ∃ h ≤ H, Deep.HonestItem P.logBlowup h x := by
  intro r' hr'
  obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hr'
  obtain ⟨hne, hc⟩ := hr.commits r hrm
  have hfst : (r.2.map fun x ↦ (x.1, x.2.zip (openedOf P.logBlowup x))).map (·.1) =
      r.2.map (·.1) := by rw [List.map_map]; rfl
  obtain ⟨xm, hxm, hmaxr⟩ := exists_max (fun x : Mat F × List EF ↦ Nat.log2 x.1.height) r.2 hne
  obtain ⟨hm, psm, hlm, -⟩ := hr.lde r hrm xm hxm
  refine ⟨by rwa [ne_eq, List.map_eq_nil_iff], by rw [hfst]; exact hc,
    Nat.log2 xm.1.height, hmax r hrm xm hxm,
    ⟨(xm.1, xm.2.zip (openedOf P.logBlowup xm)), List.mem_map_of_mem hxm,
      by rw [hlm.2.1, Nat.log2_two_pow]⟩, fun y hy ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hpne, hpts⟩ := hr.points r hrm x hx
  obtain ⟨h, ps, hl, -⟩ := hr.lde r hrm x hx
  have hz : x.2.zip (openedOf P.logBlowup x) ≠ [] := by
    obtain ⟨z, zs, hzs⟩ := List.exists_cons_of_ne_nil hpne
    simp only [openedOf, hzs, List.map_cons, List.zip_cons_cons, ne_eq, reduceCtorEq,
      not_false_eq_true]
  refine ⟨hz, h, ?_, honestItem_of _ _ _ _ ps hl hpts⟩
  have := hmaxr x hx
  rwa [hl.2.1, Nat.log2_two_pow] at this

/-- Without the flag after `openPcs`, there was none before it. -/
theorem flag_openPcs (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24)
    (h : ((openPcs (specBackend EF) P rounds).run t).2.grindFailed = false) :
    t.grindFailed = false := by
  rw [openPcs_run] at h
  dsimp only at h
  have h1 := flag_proveFri P rounds _ _ _ h
  rw [flag_sampleExt] at h1
  have h2 := flag_grind _ _ h1
  rwa [flag_observeExts, flag_observeList] at h2

/-- **Honest openings verify.** For rounds the specification prover opens honestly, the
verifier's `verifyPcs` on the opened values accepts `openPcs`'s proof from a transcript on
Plonky3's duplex, when the prover's grinder found its witnesses. -/
theorem verifyPcs_openPcs (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24) (hd : t.duplex = Poseidon2.duplex) (hr : HonestRounds P rounds)
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hgrind : ((openPcs (specBackend EF) P rounds).run t).2.grindFailed = false) :
    verifyPcs (poseidon2 F) P (verifierRounds P.logBlowup (honestRounds P.logBlowup rounds))
      ((openPcs (specBackend EF) P rounds).run t).1.2 t =
      .ok ((), ((openPcs (specBackend EF) P rounds).run t).2) := by
  rw [openPcs_run] at hgrind ⊢
  dsimp only at hgrind ⊢
  set b := P.logBlowup with hbdef
  set drs := honestRounds b rounds with hdrs
  set vr := verifierRounds (EF := EF) b drs with hvr
  set opened := rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))
    with hopened
  have hitems : opened.flatten.map (·.2) = drs.flatMap (·.2) := by
    rw [hopened, hdrs, honestRounds, List.flatMap_map, List.flatten_eq_flatMap,
      List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun r _ ↦ ?_
    simp only [id, List.map_map]; rfl
  set t1 := (t.observeList (DomainSeparator.pcsSeed F EF (countsOf opened)
    P.batchPowBits)).observeExts
      ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList)) with ht1
  set g := t1.grind P.batchPowBits with hg
  clear_value g
  set alpha : EF := g.2.sampleExtValue with halpha
  clear_value alpha
  rw [hitems] at hgrind ⊢
  set items := drs.flatMap (·.2) with hitemsdef
  -- the items
  have hmem : ∀ x ∈ items, ∃ r ∈ rounds, ∃ y ∈ r.2, x = (y.1, y.2.zip (openedOf b y)) := by
    intro x hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨r, hrm, y, hy, rfl⟩
  have hhon : ∀ x ∈ items, ∃ h, b + P.logFinalPolyLen ≤ h ∧ Deep.HonestItem b h x := by
    intro x hx
    obtain ⟨r, hrm, y, hy, rfl⟩ := hmem x hx
    obtain ⟨h, ps, hl, hh⟩ := hr.lde r hrm y hy
    exact ⟨h, hh, honestItem_of _ _ _ _ ps hl (hr.points r hrm y hy).2⟩
  have hpow : ∀ x ∈ items, x.1.height = 2 ^ Nat.log2 x.1.height := fun x hx ↦ by
    obtain ⟨h, -, ps, hl, -⟩ := hhon x hx
    rw [hl.2.1, Nat.log2_two_pow]
  obtain ⟨hpw, hkeys, hsize⟩ := reduce_heights alpha items hpow
  have hlow := reduce_lowDegree b alpha items fun x hx ↦ by
    obtain ⟨h, -, hit⟩ := hhon x hx; exact ⟨h, hit⟩
  have hkey : ∀ x ∈ items, Nat.log2 x.1.height ∈ (Fri.reduce alpha items).map (·.1) :=
    fun x hx ↦ (hkeys _).mpr ⟨x, hx, rfl⟩
  have hfin : ∀ k ∈ (Fri.reduce alpha items).map (·.1), b + P.logFinalPolyLen ≤ k := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := (hkeys k).mp hk
    obtain ⟨h, hh, ps, hl, -⟩ := hhon x hx
    rw [hl.2.1, Nat.log2_two_pow]; exact hh
  -- the inputs: one per height, tallest first
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr.nonempty
  obtain ⟨y0, hy0⟩ := List.exists_mem_of_ne_nil _ (hr.commits r0 hr0).1
  have hx0 : (y0.1, y0.2.zip (openedOf b y0)) ∈ items :=
    List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hr0, List.mem_map_of_mem hy0⟩
  obtain ⟨⟨h0, f0⟩, L, hL⟩ : ∃ e L, Fri.reduce alpha items = e :: L := by
    cases hc : Fri.reduce alpha items with
    | nil =>
      have := hkey _ hx0
      rw [hc] at this
      exact absurd this List.not_mem_nil
    | cons e L => exact ⟨e, L, rfl⟩
  rw [hL] at hpw hkeys hsize hlow hkey hfin hgrind ⊢
  have hs0 : Nat.log2 f0.size = h0 := by
    rw [hsize _ List.mem_cons_self, Nat.log2_two_pow]
  have hmaxk : ∀ k ∈ (List.map (·.1) ((h0, f0) :: L)), k ≤ h0 := fun k hk ↦ by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact le_rfl
    · exact le_of_lt (List.rel_of_pairwise_cons hpw hk)
  have hg0 : Good P (Nat.log2 f0.size) f0 := by
    rw [hs0]
    exact ⟨hfin h0 List.mem_cons_self, hlow _ List.mem_cons_self⟩
  have hLsz : ∀ y ∈ L, Nat.log2 y.2.size = y.1 := fun y hy ↦ by
    rw [hsize y (List.mem_cons_of_mem _ hy), Nat.log2_two_pow]
  have hLmap : (L.map (·.2)).map (Nat.log2 ·.size) = L.map (·.1) := by
    rw [List.map_map]; exact List.map_congr_left hLsz
  have hpend : Pending P (L.map (·.2)) := by
    refine ⟨by rw [hLmap]; exact hpw.of_cons, fun v hv ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    rw [hLsz y hy]
    exact ⟨hfin _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)),
      hlow y (List.mem_cons_of_mem _ hy)⟩
  have hlt : ∀ v ∈ L.map (·.2), Nat.log2 v.size < Nat.log2 f0.size := fun v hv ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    rw [hLsz y hy, hs0]
    exact List.rel_of_pairwise_cons hpw (List.mem_map_of_mem hy)
  simp only [List.map_cons] at hgrind ⊢
  -- the grinding flags and the duplexes
  have hgB : g.2.grindFailed = false := by
    have h1 := flag_proveFri P rounds (f0 :: L.map (·.2)) g.1 (Transcript.sampleExtState EF g.2)
    have h2 := h1 hgrind
    rwa [flag_sampleExt] at h2
  have hd1 : t1.duplex = Poseidon2.duplex := by
    rw [ht1, duplex_observeExts, duplex_observeList, hd]
  have hd2 : (Transcript.sampleExtState EF g.2).duplex = Poseidon2.duplex := by
    rw [duplex_sampleExt, hg, duplex_grind, hd1]
  -- the verifier's transcript before the batching challenge is the prover's
  have hT : (t.observeList (DomainSeparator.pcsSeed F EF (claimCounts vr)
      P.batchPowBits)).observeExts (vr.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
      t1 := by
    rw [hvr, hdrs, claimCounts_verifierRounds, flat_verifierRounds]
  have hbw : ((proveFri (specBackend EF) P rounds (f0 :: L.map (·.2)) g.1).run
      (Transcript.sampleExtState EF g.2)).1.batchWitness = g.1 := by
    rw [proveFri_run]
  have hcB : checkWitness (poseidon2 F) P.batchPowBits g.1 t1 = .ok (true, g.2) := by
    have hc := checkWitness_grind t1 P.batchPowBits (by rw [← hg]; exact hgB)
    rw [← hg] at hc
    exact (checkWitness_run _ _ _ hd1).trans (congrArg Except.ok hc)
  rw [verifyPcs_run _ _ _ _ (by rw [hbw, hg]; exact grind_canonical _ _), hT, hbw, bind_ok hcB,
    ensure_true, pure_bind, bind_ok (sampleExt_run _), ← halpha]
  -- FRI
  have hround := honestRounds_ok hr h0 fun r hrm x hx ↦ hmaxk _ (by
    exact hkey _ (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hrm, List.mem_map_of_mem hx⟩))
  have hfst : drs.map (·.1) = rounds.map (·.1) := by
    rw [hdrs, honestRounds, List.map_map]; rfl
  have hF := verifyFri_proveFri P rounds f0 (L.map (·.2)) g.1 vr alpha
    (Transcript.sampleExtState EF g.2) hd2 hg0 hpend hlt hP hq hb
  refine hF hgrind ?_ ?_ ?_ ?_
  · obtain ⟨hne0, -⟩ := hr.commits r0 hr0
    refine List.any_eq_true.mpr ⟨_, List.mem_map_of_mem (List.mem_map_of_mem hr0), ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
      List.map_eq_nil_iff]
    exact hne0
  · have hblog : ∀ x ∈ items, Nat.log2 x.1.height - b + b = Nat.log2 x.1.height := by
      intro x hx
      obtain ⟨h, -, ps, hl, -⟩ := hhon x hx
      rw [hl.2.1, Nat.log2_two_pow]; exact Nat.sub_add_cancel hl.2.2.2.1
    rw [List.map_cons, hs0, hLmap]
    refine eq_of_pairwise_gt _ _ (pairwise_dedup_mergeSort _) (by simpa only [List.map_cons]
      using hpw) fun a ↦ ?_
    rw [List.mem_dedup, List.mem_mergeSort]
    change _ ↔ a ∈ ((h0, f0) :: L).map (·.1)
    rw [hkeys]
    constructor
    · intro ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      obtain ⟨r', hr', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      have hxi : x ∈ items := List.mem_flatMap.mpr ⟨r, hr, hx⟩
      exact ⟨x, hxi, (hblog x hxi).symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
      refine List.mem_map.mpr ⟨_, List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hr,
        List.mem_map_of_mem hxr⟩, hblog x hx⟩
  · intro indices t' hidx
    rw [hs0] at hidx ⊢
    rw [← map_fst_congr (fun c ↦ openMulti (specBackend EF) c
      (indices.map (· >>> (h0 - (specBackend EF).logHeight c)))) drs rounds hfst]
    exact verifyInputs_honest P h0 indices drs hidx hround t'
  · intro index t' hidx
    rw [hs0] at hidx ⊢
    rw [← map_fst_congr (fun c ↦ ((specBackend EF).openAt c
      (index >>> (h0 - (specBackend EF).logHeight c))).values.toList) drs rounds hfst]
    have hD := reduceQuery_honest P h0 index alpha drs hidx fun r hr' ↦ by
      obtain ⟨h1, h2, H, hH, htop, hall⟩ := hround r hr'
      exact ⟨h1, h2, H, hH, htop, fun x hx ↦ (hall x hx).2⟩
    rw [hL] at hD
    refine (congrFun hD t').trans ?_
    simp only [List.map_cons, Nat.sub_self, Nat.shiftRight_zero, roOf, List.map_map]
    refine congrArg (fun x ↦ Except.ok (x, t')) (congrArg _ (List.map_congr_left fun y hy ↦ ?_))
    simp only [Function.comp_apply, hLsz y hy]

end CompStark.Stark
