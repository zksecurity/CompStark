/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Honest

/-! Field transport of multilinear evaluations and honest sumcheck strategies. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr
open scoped BigOperators

/-- Equality weights commute with ring homomorphisms. -/
theorem eqWeight_map {F G : Type} [CommRing F] [CommRing G] (e : F →+* G)
    {n : Nat} (point : Fin n → F) (index : Nat) :
    e (eqWeight point index) = eqWeight (fun i => e (point i)) index := by
  simp only [eqWeight,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp only [map_sub,map_one]

/-- Multilinear table evaluations commute with ring homomorphisms. -/
theorem mle_map {F G : Type} [CommRing F] [CommRing G] (e : F →+* G)
    {n : Nat} (table : Fin (2^n) → F) (point : Fin n → F) :
    e (mle table point) = mle (fun i => e (table i)) (fun i => e (point i)) := by
  simp only [mle,map_sum,map_mul,eqWeight_map]

/-- Binary-field casts commute with ring homomorphisms between characteristic-two rings. -/
theorem zmod_cast_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) (a : ZMod 2) :
    e (ZMod.castHom (dvd_refl 2) F a) = ZMod.castHom (dvd_refl 2) G a := by
  simp only [ZMod.castHom_apply,ZMod.cast_eq_val,map_natCast]

/-- Recombining binary lane coordinates commutes with ring homomorphisms. -/
theorem laneValue_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) (x : F) (bits : Fin 64 → ZMod 2) :
    e (laneValue x bits) = laneValue (e x) bits := by
  simp only [laneValue,map_sum,map_mul,map_pow,zmod_cast_map]

/-- Boolean-cube sums commute with a ring equivalence and the induced change of coordinates. -/
theorem booleanSum_equiv {F G : Type} [CommRing F] [CommRing G] (e : F ≃+* G)
    {n : Nat} (f : (Fin n → F) → F) (g : (Fin n → G) → G)
    (h : ∀ point,e (f point) = g (fun i => e (point i))) :
    e (booleanSum f) = booleanSum g := by
  simp only [booleanSum,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  simpa only [map_natCast] using h (fun i => (b i).val)

/-- Coordinate degree bounds transfer through a ring equivalence and its change of coordinates. -/
theorem coordinateDegree_equiv {F G : Type} [CommRing F] [CommRing G] (e : F ≃+* G)
    {n degree : Nat} (f : (Fin n → F) → F) (g : (Fin n → G) → G)
    (h : ∀ point,e (f point) = g (fun i => e (point i))) (hf : CoordinateDegree f degree) :
    CoordinateDegree g degree := by
  intro i point
  let source : Fin n → F := fun j => e.symm (point j)
  obtain ⟨P,hP,heval⟩ := hf i source
  refine ⟨P.map e.toRingHom,Polynomial.degree_map_le.trans hP,?_⟩
  intro s
  obtain ⟨r,rfl⟩ := e.surjective s
  calc
    Polynomial.eval (e r) (P.map e.toRingHom) = e (P.eval r) := Polynomial.eval_map_apply e.toRingHom r
    _ = e (f (Function.update source i r)) := congrArg e (heval r)
    _ = g (fun j => e (Function.update source i r j)) := h _
    _ = g (Function.update point i (e r)) := by
      apply congrArg g
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hj,source,e.apply_symm_apply]

/-- The unique honest first polynomial transports by a ring equivalence. -/
theorem firstHonestPolynomial_equiv {F G : Type} [CommRing F] [CommRing G]
    [IsDomain G] [Fintype G] (e : F ≃+* G) {n degree : Nat}
    (f : (Fin (n+1) → F) → F) (g : (Fin (n+1) → G) → G)
    (hf : CoordinateDegree f degree) (hg : CoordinateDegree g degree)
    (h : ∀ point,e (f point) = g (fun i => e (point i)))
    (hcard : degree < Fintype.card G) :
    (firstHonestPolynomial g hg).val =
      (firstHonestPolynomial f hf).val.map e.toRingHom := by
  have hP : ((firstHonestPolynomial f hf).val.map e.toRingHom).degree ≤ degree :=
    Polynomial.degree_map_le.trans (Polynomial.mem_degreeLE.mp (firstHonestPolynomial f hf).property)
  have he := firstHonestPolynomial_eq g hg hcard
    ⟨(firstHonestPolynomial f hf).val.map e.toRingHom,Polynomial.mem_degreeLE.mpr hP⟩ (by
      intro r
      obtain ⟨s,rfl⟩ := e.surjective r
      change Polynomial.eval (e.toRingHom s)
        ((firstHonestPolynomial f hf).val.map e.toRingHom) = _
      rw [Polynomial.eval_map_apply,firstHonestPolynomial_eval]
      apply booleanSum_equiv e
      intro rest
      convert h (Fin.cons s rest) using 2
      funext i
      refine Fin.cases rfl (fun _ => rfl) i)
  exact congrArg Subtype.val he

/-- Every honest compressed message transports coefficient by coefficient under a ring equivalence. -/
theorem honestCompressedRounds_equiv {F G : Type} [CommRing F] [CommRing G]
    [IsDomain G] [Fintype G] (e : F ≃+* G) {n degree : Nat}
    (f : (Fin n → F) → F) (g : (Fin n → G) → G)
    (hf : CoordinateDegree f (degree+1)) (hg : CoordinateDegree g (degree+1))
    (h : ∀ point,e (f point) = g (fun i => e (point i)))
    (hcard : degree+1 < Fintype.card G) (point : Fin n → F) (i : Fin n) :
    (e (honestCompressedRounds f hf point i).1,
      fun k => e ((honestCompressedRounds f hf point i).2 k)) =
      honestCompressedRounds g hg (fun j => e (point j)) i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [honestCompressedRounds,Fin.cons_zero]
      have hp := firstHonestPolynomial_equiv e f g hf hg h hcard
      simp only [Sumcheck.compress,hp,Polynomial.coeff_map]
      rfl
    · simp only [honestCompressedRounds,Fin.cons_succ]
      apply ih
      intro rest
      convert h (Fin.cons (point 0) rest) using 2
      funext i
      refine Fin.cases rfl (fun _ => rfl) i

end CompStark.Keccak.GkrProver
