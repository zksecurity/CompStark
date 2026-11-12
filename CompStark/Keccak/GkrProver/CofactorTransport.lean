/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PositionSemantics

/-! Field transport of equality-factored honest pack strategies. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 32768

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64 Polynomial
open scoped BigOperators

/-- The RMFE basis evaluation commutes with coefficient-field homomorphisms. -/
theorem muAt_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) (s : F) (i : Fin 16) : e (muAt s i)=muAt (e s) i := by
  rw [muAt_eq_eval, muAt_eq_eval]
  rw [← Polynomial.eval_map_apply e s,Polynomial.map_map]
  have hcast : e.comp (ZMod.castHom (dvd_refl 2) F)=ZMod.castHom (dvd_refl 2) G := by
    ext z
    exact zmod_cast_map e z
  rw [hcast]

/-- The equality-free committed pack cofactor transports to the verifier field. -/
theorem packCofactor_toField {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim) (s : W)
    (point : Fin (p+1) → W) :
    WordExt3.ringEquiv (MvPolynomial.eval point (packCofactorPolynomial q d (claim.toWordProtocol p) s)) =
      MvPolynomial.eval (fun i => WordExt3.ringEquiv (point i))
        (packCofactorPolynomial q d (claim.toProtocol p) s.toField) := by
  change WordExt3.ringEquiv.toRingHom (MvPolynomial.eval point (packCofactorPolynomial q d (claim.toWordProtocol p) s)) = _
  simp only [packCofactorPolynomial_value,map_sum,map_mul,map_add,linearAtPack_map,muAt_map,
    Claim.toWordProtocol,Claim.toProtocol]
  rfl

/-- The unique honest quadratic cofactor transports by a ring equivalence. -/
theorem honestCofactorPolynomial_equiv {F G : Type} [CommRing F] [CharP F 2]
    [CommRing G] [CharP G 2] [IsDomain G] [Fintype G] (e : F ≃+* G) {n : Nat}
    (f : (Fin (n+1) → F) → F) (g : (Fin (n+1) → G) → G)
    (hf : CoordinateDegree f 2) (hg : CoordinateDegree g 2)
    (h : ∀ point,e (f point)=g (fun i => e (point i))) (hcard : 2<Fintype.card G) (point : Fin n → F) :
    (honestCofactorPolynomial g hg (fun i => e (point i))).val =
      (honestCofactorPolynomial f hf point).val.map e.toRingHom := by
  have hdeg : ((honestCofactorPolynomial f hf point).val.map e.toRingHom).degree≤2 :=
    Polynomial.degree_map_le.trans (Polynomial.mem_degreeLE.mp (honestCofactorPolynomial f hf point).property)
  have he := honestCofactorPolynomial_eq g hg (fun i => e (point i)) hcard
    ⟨(honestCofactorPolynomial f hf point).val.map e.toRingHom,Polynomial.mem_degreeLE.mpr hdeg⟩ (by
      intro r
      obtain ⟨s,rfl⟩ := e.surjective r
      change Polynomial.eval (e.toRingHom s) ((honestCofactorPolynomial f hf point).val.map e.toRingHom) = _
      rw [Polynomial.eval_map_apply,honestCofactorPolynomial_eval]
      apply booleanSum_equiv e
      intro rest
      rw [map_mul]
      apply congrArg₂ (·*·) (eqEval_map e.toRingHom point rest)
      rw [h]
      apply congrArg g
      funext i
      exact Fin.cases rfl (fun _ => rfl) i)
  exact congrArg Subtype.val he

/-- All honest cofactor-tail messages transport coefficient by coefficient under a ring equivalence. -/
theorem honestCofactorRounds_equiv {F G : Type} [CommRing F] [CharP F 2]
    [CommRing G] [CharP G 2] [IsDomain G] [Fintype G] (e : F ≃+* G) {n : Nat}
    (f : (Fin n → F) → F) (g : (Fin n → G) → G)
    (hf : CoordinateDegree f 2) (hg : CoordinateDegree g 2)
    (h : ∀ point,e (f point)=g (fun i => e (point i))) (hcard : 2<Fintype.card G)
    (entering sampled : Fin n → F) (i : Fin n) :
    (e (honestCofactorRounds f hf entering sampled i).1,
      fun k => e ((honestCofactorRounds f hf entering sampled i).2 k)) =
      honestCofactorRounds g hg (fun j => e (entering j)) (fun j => e (sampled j)) i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [honestCofactorRounds,Fin.cons_zero]
      have hp := honestCofactorPolynomial_equiv e f g hf hg h hcard (fun j => entering j.succ)
      simp only [hp,Polynomial.coeff_map]
      rfl
    · simp only [honestCofactorRounds,Fin.cons_succ]
      apply ih
      intro rest
      change e ((1+entering 0+sampled 0)*f (Fin.cons (sampled 0) rest)) = _
      rw [map_mul,map_add,map_add,map_one,h]
      congr 1
      apply congrArg g
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- The complete honest pack strategy transports from native words to the verifier field. -/
theorem honestPackRounds_toField {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim)
    (s : W) (point : Fin (p+1) → W) (i : Fin (p+1)) :
    (WordExt3.ringEquiv (honestPackRounds q d (claim.toWordProtocol p) s point i).1,
      fun k => WordExt3.ringEquiv ((honestPackRounds q d (claim.toWordProtocol p) s point i).2 k)) =
      honestPackRounds q d (claim.toProtocol p) s.toField (fun j => WordExt3.ringEquiv (point j)) i := by
  let : Fintype E := Fintype.ofFinite E
  have hcard : 2<Fintype.card E := by rw [BF64.card_ext3]; decide
  unfold honestPackRounds
  exact honestCofactorRounds_equiv WordExt3.ringEquiv _ _ _ _ (packCofactor_toField q d claim s) hcard _ point i

end CompStark.Keccak.GkrProver
