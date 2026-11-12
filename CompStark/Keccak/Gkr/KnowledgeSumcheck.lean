/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgePrefix
public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge
public import ArkLib.ProofSystem.Sumcheck.Domain

/-! # Fixed-table prefix adapters to the sumcheck knowledge certificate -/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public section
open Interaction.Oracle.Security OracleComp
open scoped ENNReal BigOperators
namespace CompStark.Keccak.Gkr
open Sumcheck Sumcheck.Interaction Sumcheck.Interaction.SingleRound
  Sumcheck.Interaction.MultivariateRound

/-- The sumcheck certificate bounds successor witnesses bound to one committed GKR table.
An arbitrary prefix invariant can accompany the binding without changing the local error. -/
theorem sumcheck_boundWitness_prefix_bound {E : Type} [Field E] [Fintype E] {M : Type} {p n degree m : Nat}
    (q₀ : Witness p) (invariant : Witness p → Prop)
    (summand : Witness p → Sumcheck.Spec.OracleStatement E n degree ())
    (D : Fin m ↪ E) (i : Fin n) (stmt : Sumcheck.Spec.StatementRound E n i.castSucc)
    (ops : MessageOps E M) (model : MessageModel (Finset.univ.map D) ops degree)
    (sent : M) (check : ops.accept stmt.target sent = true) :
    Pr{let r ← uniformField E}[∃ w : Witness p, w = q₀ ∧ invariant w ∧
      ¬ closedRelation E n degree D i.castSucc
        ⟨stmt, (polynomialFamily E n degree).behaviorOfRealizations (fun _ => summand w)⟩ ∧
      closedRelation E n degree D i.succ
        ⟨⟨ops.evaluate stmt.target sent r, Fin.snoc stmt.challenges r⟩,
          (polynomialFamily E n degree).behaviorOfRealizations (fun _ => summand w)⟩] ≤
      (degree : ENNReal) / Fintype.card E := by
  classical
  let _ := SampleableType.ofFintype E
  let valid := fun w : Witness p => w = q₀ ∧ invariant w
  have binding : Knowledge.BindsSummand valid summand (summand q₀) := by
    intro w hw
    rw [hw.1]
  let count := n-(i.val+1)
  have finish : i.val+(count+1) = n := by dsimp only [count]; omega
  have bound := Knowledge.local_badChallenge_le ops D model
    valid summand (summand q₀) binding count i.val finish stmt true sent
  rw [Knowledge.nextChallenge, check, ite_eq_left rfl, prEvent_map] at bound
  refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
  intro r good
  obtain ⟨w, hw, hi, wrong, successor⟩ := good
  refine ⟨w, ?_, ?_⟩
  · intro known
    exact wrong known.2.2
  · exact ⟨by simp only [Bool.true_and, check], ⟨hw, hi⟩, successor⟩

/-- The Boolean sumcheck closed relation is the GKR residual at the same challenge prefix. -/
theorem sumcheck_closedRelation_residual {E : Type} [Field E] {n degree : Nat}
    (H : Sumcheck.Spec.OracleStatement E n degree ()) (i : Fin (n+1))
    (point : Fin n → E) (target : E) :
    closedRelation E n degree (_root_.boolEmbedding E) i
      ⟨⟨target, fun j => point ⟨j.val, by omega⟩⟩,
        (polynomialFamily E n degree).behaviorOfRealizations (fun _ => H)⟩ ↔
      target = residualSum (fun r => MvPolynomial.eval r H.val) point i.val := by
  classical
  rw [residualSum_eq_hypercubeSum H.val point i.val (by omega)]
  dsimp only [closedRelation, Interaction.Oracle.OracleFamily.behaviorOfRealizations,
    polynomialFamily, OracleInterface.answer, OracleInterface.instMvPolynomialDegreeLE]
  change (∑ r ∈ (_root_.boolDomain E (n-i.val)).cube,
    MvPolynomial.eval (Fin.append (fun j : Fin i.val => point ⟨j.val, by omega⟩) r ∘ Fin.cast (by omega)) H.val) =
      target ↔ _
  rw [_root_.sum_cube_boolDomain]
  have he : (∑ y : Fin (n-i.val) → Fin 2,
      MvPolynomial.eval
        (Fin.append (fun j : Fin i.val => point ⟨j.val, by omega⟩) (fun j => ((y j : Nat) : E)) ∘
          Fin.cast (by omega)) H.val) =
      MvPolynomial.hypercubeSum n H.val i.val (fun j => point ⟨j.val, by omega⟩) := by
    simp only [MvPolynomial.hypercubeSum, Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro y _
    apply congrArg (fun r : Fin n → E => MvPolynomial.eval r H.val)
    funext j
    simp only [Function.comp_apply, MvPolynomial.hypercubePoint]
    by_cases hj : j.val < i.val
    · have he : (Fin.cast (by omega : n = i.val+(n-i.val)) j) =
          Fin.castAdd (n-i.val) ⟨j.val, hj⟩ := Fin.ext rfl
      simp only [he, Fin.append_left, hj, dite_true]
    · have he : (Fin.cast (by omega : n = i.val+(n-i.val)) j) =
          Fin.natAdd i.val ⟨j.val-i.val, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd]
        omega
      simp only [he, Fin.append_right, hj, dite_false]
  rw [he]
  exact eq_comm

/-- The sumcheck knowledge certificate bounds one concrete GKR residual round. -/
theorem sumcheck_residual_certificate_bound {E : Type} [Field E] [Fintype E] [DecidableEq E]
    {M : Type} {p n degree : Nat} (q₀ : Witness p) (H : MvPolynomial (Fin n) E)
    (cap : ∀ j, H.degreeOf j ≤ degree) (i : Fin n) (point : Fin n → E)
    (ops : MessageOps E M) (model : MessageModel ({0,1} : Finset E) ops degree)
    (sent : M) (target : E)
    (wrong : target ≠ residualSum (fun r => MvPolynomial.eval r H) point i.val)
    (check : ops.accept target sent = true) :
    Pr{let r ← uniformField E}[ops.evaluate target sent r =
      residualSum (fun z => MvPolynomial.eval z H) (Function.update point i r) (i.val+1)] ≤
      (degree : ENNReal) / Fintype.card E := by
  classical
  let bounded : Sumcheck.Spec.OracleStatement E n degree () :=
    ⟨H, (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mpr cap⟩
  let stmt : Sumcheck.Spec.StatementRound E n i.castSucc :=
    ⟨target, fun j => point ⟨j.val, by omega⟩⟩
  have domain : Finset.univ.map (_root_.boolEmbedding E) = ({0,1} : Finset E) := by
    ext z
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.exists_fin_two,
      _root_.boolEmbedding_zero, _root_.boolEmbedding_one, Finset.mem_insert,
      Finset.mem_singleton, eq_comm]
  have bound := sumcheck_boundWitness_prefix_bound q₀ (fun _ => True) (fun _ => bounded)
    (_root_.boolEmbedding E) i stmt ops (domain ▸ model) sent check
  refine (prEvent_mono (uniformField E) _ _ ?_).trans bound
  intro r good
  refine ⟨q₀, rfl, trivial, ?_, ?_⟩
  · exact fun hc => wrong ((sumcheck_closedRelation_residual bounded i.castSucc point target).mp hc)
  · have h := (sumcheck_closedRelation_residual bounded i.succ
        (Function.update point i r) (ops.evaluate target sent r)).mpr good
    change closedRelation E n degree (_root_.boolEmbedding E) i.succ
      ⟨⟨ops.evaluate target sent r, fun j : Fin (i.val+1) => Function.update point i r ⟨j.val, by omega⟩⟩,
        (polynomialFamily E n degree).behaviorOfRealizations (fun _ => bounded)⟩ at h
    rw [updated_prefix] at h
    dsimp only [closedRelation, Interaction.Oracle.OracleFamily.behaviorOfRealizations,
      polynomialFamily, OracleInterface.answer, OracleInterface.instMvPolynomialDegreeLE,
      stmt] at h ⊢
    exact h

/-- The retained-table sumcheck certificate supplies the concrete cubic pack/segment bound. -/
theorem packSegment_knowledge_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E)
    (i : Fin (p+1)) (point : Fin (p+1) → E) (sent : CofactorMessage E) (target : E)
    (wrong : target ≠ residualSum (packSummand q d c s) point i.val)
    (check : (cofactorOps (c.point i)).accept target sent = true) :
    Pr{let r ← uniformField E}[(cofactorOps (c.point i)).evaluate target sent r =
      residualSum (packSummand q d c s) (Function.update point i r) (i.val+1)] ≤
      (3 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (packPolynomial q d c s)) = packSummand q d c s :=
    funext (packPolynomial_eval q d c s)
  simpa only [he, Nat.cast_ofNat] using sumcheck_residual_certificate_bound q (packPolynomial q d c s)
    (packPolynomial_degree q d c s) i point (cofactorOps (c.point i)) (cofactorModel (c.point i)) sent target
      (by simpa only [he] using wrong) check

/-- The retained-table sumcheck certificate supplies the concrete cubic position bound. -/
theorem position_knowledge_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p)
    (i : Fin 11) (point : Fin 11 → E) (sent : CompressedMessage E 2) (target : E)
    (wrong : target ≠ residualSum (positionSummand q d c t) point i.val)
    (check : (compressedOps 2).accept target sent = true) :
    Pr{let r ← uniformField E}[(compressedOps 2).evaluate target sent r =
      residualSum (positionSummand q d c t) (Function.update point i r) (i.val+1)] ≤
      (3 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (positionPolynomial q d c t)) = positionSummand q d c t :=
    funext (positionPolynomial_eval q d c t)
  simpa only [he, Nat.cast_ofNat] using sumcheck_residual_certificate_bound q (positionPolynomial q d c t)
    (positionPolynomial_degree q d c t) i point (compressedOps 2) (compressedModel 2) sent target
      (by simpa only [he] using wrong) check

/-- The retained-table sumcheck certificate supplies the concrete quadratic middle-opening bound. -/
theorem word_opening_knowledge_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (i : Fin 6) (point : Fin 6 → E)
    (sent : CompressedMessage E 1) (target : E)
    (wrong : target ≠ residualSum (wordSummand x q t) point i.val)
    (check : (compressedOps 1).accept target sent = true) :
    Pr{let r ← uniformField E}[(compressedOps 1).evaluate target sent r =
      residualSum (wordSummand x q t) (Function.update point i r) (i.val+1)] ≤
      (2 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (wordPolynomial x q t)) = wordSummand x q t :=
    funext (wordPolynomial_eval x q t)
  simpa only [he, Nat.cast_ofNat] using sumcheck_residual_certificate_bound q (wordPolynomial x q t)
    (wordPolynomial_degree x q t) i point (compressedOps 1) (compressedModel 1) sent target
      (by simpa only [he] using wrong) check

/-- The retained-table sumcheck certificate supplies the concrete quadratic input-opening bound. -/
theorem slice_opening_knowledge_bound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (i : Fin 10) (point : Fin 10 → E)
    (sent : CompressedMessage E 1) (target : E)
    (wrong : target ≠ residualSum (inputSummand q t) point i.val)
    (check : (compressedOps 1).accept target sent = true) :
    Pr{let r ← uniformField E}[(compressedOps 1).evaluate target sent r =
      residualSum (inputSummand q t) (Function.update point i r) (i.val+1)] ≤
      (2 : ENNReal) / Fintype.card E := by
  classical
  have he : (fun r => MvPolynomial.eval r (inputPolynomial q t)) = inputSummand q t :=
    funext (inputPolynomial_eval q t)
  simpa only [he, Nat.cast_ofNat] using sumcheck_residual_certificate_bound q (inputPolynomial q t)
    (inputPolynomial_degree q t) i point (compressedOps 1) (compressedModel 1) sent target
      (by simpa only [he] using wrong) check

end CompStark.Keccak.Gkr
