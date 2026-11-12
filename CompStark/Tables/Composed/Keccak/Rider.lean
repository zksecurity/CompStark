/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Table
public import CompStark.Pcs.RingSwitch.Fields

/-! The Keccak table's rider on the table sumcheck's draws: the Keccak-f GKR's initial discrepancy,
a multilinear table on the instance and segment/lane coordinates, restricted on the instance
coordinates the table sumcheck has drawn, highest first. A false rider becomes true at one more draw
with probability at most `1 / |E|` (`rider_local_le`); before any draw it is the Keccak-f relation of
the stack's middle lanes (`rider_nil_iff`); after every draw it is the GKR's start relation at the
table's point (`rider_complete_iff`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open OracleComp

noncomputable section

/-- Polynomial-basis lane powers are independent after embedding into the extension field. -/
theorem independentLanePowers : Keccak.Gkr.IndependentLanePowers (ofK g) := by
  intro coefficients zero
  have bits (z : Fin 64) : ZMod.castHom (dvd_refl 2) E (coefficients z) = 0 ∨
      ZMod.castHom (dvd_refl 2) E (coefficients z) = 1 := by
    have bit_cases (value : ZMod 2) : value = 0 ∨ value = 1 := by
      fin_cases value
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases bit_cases (coefficients z) with h | h
    · exact Or.inl (h ▸ map_zero _)
    · exact Or.inr (h ▸ map_one _)
  have frobenius (z : Fin 64) (k : ℕ) :
      ZMod.castHom (dvd_refl 2) E (coefficients z) ^ 2 ^ k =
        ZMod.castHom (dvd_refl 2) E (coefficients z) := by
    rcases bits z with h | h <;> rw [h]
    · exact zero_pow (Nat.two_pow_pos _).ne'
    · exact one_pow _
  have vanishes := Pcs.RingSwitch.ringSwitch_injective
    (fun z => ZMod.castHom (dvd_refl 2) E (coefficients z)) (fun k _ => by
      simp only [frobenius]
      change (∑ i : Fin 64, (algebraMap K E) (g ^ i.val) *
        ZMod.castHom (dvd_refl 2) E (coefficients i)) = 0
      change (∑ i : Fin 64, ZMod.castHom (dvd_refl 2) E (coefficients i) *
        (algebraMap K E) g ^ i.val) = 0 at zero
      simpa only [map_pow, mul_comm] using zero)
  intro z
  exact (ZMod.castHom (dvd_refl 2) E).injective (by
    rw [map_zero]
    exact vanishes z)

/-- A scalar identity vanishes at every point compatible with a fixed partial assignment. -/
def ZeroOn {F : Type} [Zero F] {n : ℕ} (value : (Fin n → F) → F)
    (fixed : Fin n → Option F) : Prop :=
  ∀ point, (∀ coordinate scalar, fixed coordinate = some scalar → point coordinate = scalar) →
    value point = 0

/-- Fixing one unused coordinate can hide a false affine identity at only one field element. -/
theorem zeroOn_coordinate_le {F : Type} [Field F] [Fintype F] {n : ℕ}
    (value : (Fin n → F) → F) (degree : Keccak.Gkr.CoordinateDegree value 1)
    (fixed : Fin n → Option F) (coordinate : Fin n) :
    Pr{let scalar ← Keccak.Gkr.uniformField F}[
      ¬ ZeroOn value fixed ∧ ZeroOn value (Function.update fixed coordinate (some scalar))] ≤
      (1 : ENNReal) / Fintype.card F := by
  classical
  by_cases known : ZeroOn value fixed
  · exact (prEvent_mono _ _ (fun _ => False) (fun _ bad => bad.1 known)).trans
      (by simp only [prEvent_false, zero_le])
  · obtain ⟨point, agrees, nonzero⟩ : ∃ point,
        (∀ index scalar, fixed index = some scalar → point index = scalar) ∧ value point ≠ 0 := by
      by_contra absent
      apply known
      intro point agrees
      by_contra nonzero
      exact absent ⟨point, agrees, nonzero⟩
    obtain ⟨polynomial, cap, evaluate⟩ := degree coordinate point
    have nonzero_poly : polynomial ≠ 0 := by
      intro zero
      have equality := evaluate (point coordinate)
      rw [zero, Polynomial.eval_zero, Function.update_eq_self] at equality
      exact nonzero equality.symm
    refine (prEvent_mono _ _ (fun scalar => polynomial.eval scalar = (0 : Polynomial F).eval scalar)
      ?_).trans (by simpa only [Nat.cast_one] using
        Keccak.Gkr.polynomial_collision_bound polynomial 0 nonzero_poly cap (by simp))
    intro scalar event
    rw [evaluate, Polynomial.eval_zero]
    apply event.2
    intro index other assigned
    by_cases equal : index = coordinate
    · subst index
      rw [Function.update_self] at assigned ⊢
      exact Option.some.inj assigned
    · rw [Function.update_of_ne equal] at assigned ⊢
      exact agrees index other assigned

/-- The standalone Keccak sampler and any uniform sampler have the same event probabilities. -/
theorem uniformField_prEvent {F : Type} [Fintype F] [Nonempty F] [SampleableType F]
    (event : F → Prop) :
    Pr{let r ← Keccak.Gkr.uniformField F}[event r] = Pr{let r ← ($ᵗ F)}[event r] :=
  SampleableType.prEvent_uniformSample_inst_irrel (SampleableType.ofFintype F) inferInstance event

/-- The GKR's initial point from instance and segment/lane coordinates. -/
def initialPoint {F : Type} {p : ℕ} (point : Fin (p + 4) → F) (rest : Fin 6 → F) : Fin (p + 10) → F :=
  fun i => if h : i.val < p + 4 then point ⟨i.val, h⟩ else rest ⟨i.val - (p + 4), by omega⟩

/-- Every full GKR point decomposes into its instance and six segment/lane coordinates. -/
theorem initialPoint_decompose {F : Type} {p : ℕ} (full : Fin (p + 10) → F) :
    initialPoint (fun i => full ⟨i.val, by omega⟩)
      (fun i => full ⟨p + 4 + i.val, by omega⟩) = full := by
  funext i
  simp only [initialPoint]
  split
  · rfl
  · apply congrArg full
    apply Fin.ext
    dsimp only
    omega

/-- The instance coordinates the table sumcheck's draws fix, highest first. -/
def riderFixed (height p : ℕ) (draws : List E) : Fin (p + 10) → Option E :=
  fun coordinate => if coordinate.val < p + 4 ∧ height - 1 - coordinate.val < draws.length then
      some (draws.getD (height - 1 - coordinate.val) 0) else none

variable {S : System K} {L : Layout S.tables.length} {M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The Keccak table's outputs read off a stack. -/
def outputs (q : Whir.Table K M) : Fin (2 ^ (kt.p + 4)) → Fin 25 → E :=
  witnessOutputs kt.p (kt.interpret q) kt.table kt.output

/-- The rider: the initial discrepancy vanishes wherever the drawn instance coordinates agree. -/
def rider (draws : List E) (q : Whir.Table K M) : Prop :=
  ∀ point : Fin (kt.p + 4) → E,
    (∀ i, TableSumcheck.maxHeight S L - 1 - i.val < draws.length →
      point i = draws.getD (TableSumcheck.maxHeight S L - 1 - i.val) 0) →
    ∀ rest : Fin 6 → E, Keccak.Gkr.initialIdentity (ofK g) (kt.outputs q) (kt.bits q) (initialPoint point rest)

/-- The rider is a restriction of the fixed multilinear discrepancy table. -/
theorem rider_iff_zeroOn (draws : List E) (q : Whir.Table K M) :
    kt.rider draws q ↔
      ZeroOn (Keccak.Gkr.mle (Keccak.Gkr.initialTable (ofK g) (kt.outputs q) (kt.bits q)))
        (riderFixed (TableSumcheck.maxHeight S L) kt.p draws) := by
  constructor
  · intro rider full agrees
    apply (Keccak.Gkr.initialIdentity_iff_zero (ofK g) (kt.outputs q) (kt.bits q) full).mp
    rw [← initialPoint_decompose full]
    apply rider
    intro coordinate bounded
    exact agrees ⟨coordinate.val, by omega⟩ _ (by
      simp only [riderFixed, coordinate.isLt, bounded, and_self, ite_true])
  · intro known point agrees rest
    apply (Keccak.Gkr.initialIdentity_iff_zero (ofK g) (kt.outputs q) (kt.bits q) _).mpr
    apply known
    intro coordinate scalar assigned
    dsimp only [riderFixed] at assigned
    split at assigned
    · rename_i bounded
      have scalar_eq := Option.some.inj assigned
      change initialPoint point rest coordinate = scalar
      simp only [initialPoint, bounded.1, dite_true]
      exact (agrees ⟨coordinate.val, bounded.1⟩ bounded.2).trans scalar_eq
    · contradiction

end KeccakTable

/-- The initial discrepancy vanishes pointwise on a valid Keccak witness. -/
theorem initialError_of_input {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (good : Keccak.Gkr.InputRelation x output q) (b : Fin (2 ^ (p + 4))) (slot : Fin 64) :
    Keccak.Gkr.initialError x output q b slot = 0 := by
  have chain (lane : Fin 25) : Keccak.Gkr.laneValue x (q b ⟨25 + lane.val, by omega⟩) =
      Keccak.Gkr.segmentLane x q b 0 lane := by
    apply congrArg (Keccak.Gkr.laneValue x)
    funext z
    have bits := good.1 b ⟨64 * lane.val + z.val, by omega⟩
    have div : (64 * lane.val + z.val) / 64 = lane.val := by omega
    have mod : (64 * lane.val + z.val) % 64 = z.val := by omega
    simpa only [Keccak.Gkr.startState, Fin.val_one, mul_one, div, mod] using bits.symm
  have outputLane (lane : Fin 25) : output b lane = Keccak.Gkr.segmentLane x q b 1 lane := by
    apply (good.2 b lane).trans
    apply congrArg (Keccak.Gkr.laneValue x)
    funext z
    exact congrArg (Keccak.Gkr.segmentState q b 1 12 (by omega))
      (Fin.ext (Nat.add_comm z.val (64 * lane.val)))
  unfold Keccak.Gkr.initialError
  split
  · rename_i real
    split
    · exact sub_eq_zero.mpr (chain ⟨slot.val / 2, real⟩)
    · exact sub_eq_zero.mpr (outputLane ⟨slot.val / 2, real⟩)
  · rfl

/-- A valid Keccak witness satisfies the initial identity at every point. -/
theorem initialIdentity_of_input {F : Type} [CommRing F] [CharP F 2] {p : ℕ}
    (x : F) (output : Fin (2 ^ (p + 4)) → Fin 25 → F) (q : Keccak.Gkr.Witness p)
    (good : Keccak.Gkr.InputRelation x output q) (point : Fin (p + 10) → F) :
    Keccak.Gkr.initialIdentity x output q point := by
  apply (Keccak.Gkr.initialIdentity_iff_zero x output q point).mpr
  have zero : Keccak.Gkr.initialTable x output q = fun _ => 0 := by
    funext b
    exact initialError_of_input x output q good _ _
  rw [zero]
  simp only [Keccak.Gkr.mle, mul_zero, Finset.sum_const_zero]

namespace KeccakTable

/-- Before the first table draw the rider is the Keccak-f relation of the stack's GKR witness. -/
theorem rider_nil_iff (q : Whir.Table K M) :
    kt.rider [] q ↔ Keccak.Gkr.InputRelation (ofK g) (kt.outputs q) (kt.bits q) := by
  constructor
  · intro rider
    apply Keccak.Gkr.initialIdentity_all_input (ofK g) independentLanePowers (kt.outputs q) (kt.bits q)
    intro full
    rw [← initialPoint_decompose full]
    exact rider _ (by intro i impossible; cases impossible) _
  · intro good point _ rest
    exact initialIdentity_of_input (ofK g) (kt.outputs q) (kt.bits q) good _

/-- A true rider stays true at more draws. -/
theorem rider_append (draws more : List E) (q : Whir.Table K M) (known : kt.rider draws q) :
    kt.rider (draws ++ more) q := by
  intro point agrees rest
  apply known point _ rest
  intro i bounded
  rw [← List.getD_append draws more 0 _ bounded]
  exact agrees i (by simp only [List.length_append]; omega)

end KeccakTable

/-- A table draw above the Keccak instance height leaves the rider unchanged. -/
theorem riderFixed_append_high (height p : ℕ) (draws : List E) (r : E)
    (high : draws.length < height - (p + 4)) :
    riderFixed height p (draws ++ [r]) = riderFixed height p draws := by
  funext i
  unfold riderFixed
  by_cases instCoord : i.val < p + 4
  · have unused : ¬ height - 1 - i.val < (draws ++ [r]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have old : ¬ height - 1 - i.val < draws.length := by omega
    simp only [unused, old, and_false, ite_false]
  · simp only [instCoord, false_and, ite_false]

/-- A table draw within the Keccak height fixes the same descending instance coordinate. -/
theorem riderFixed_append_low (height p : ℕ) (draws : List E) (r : E)
    (hheight : p + 4 ≤ height) (low : height - (p + 4) ≤ draws.length)
    (remaining : draws.length < height) :
    riderFixed height p (draws ++ [r]) = Function.update (riderFixed height p draws)
      ⟨height - 1 - draws.length, by omega⟩ (some r) := by
  classical
  funext i
  by_cases equal : i = (⟨height - 1 - draws.length, by omega⟩ : Fin (p + 10))
  · subst i
    rw [Function.update_self]
    have inverse : height - 1 - (height - 1 - draws.length) = draws.length := by omega
    simp only [riderFixed, inverse, List.length_append, List.length_singleton]
    have instCoord : height - 1 - draws.length < p + 4 := by omega
    simp only [instCoord, Nat.lt_succ_self, and_self, ite_true,
      List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  · rw [Function.update_of_ne equal]
    have distinct : i.val ≠ height - 1 - draws.length := fun h => equal (Fin.ext h)
    unfold riderFixed
    by_cases instCoord : i.val < p + 4
    · have same : height - 1 - i.val < (draws ++ [r]).length ↔
          height - 1 - i.val < draws.length := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [instCoord, true_and, same]
      split
      · rename_i fixed
        rw [List.getD_append _ _ _ _ fixed]
      · rfl
    · simp only [instCoord, false_and, ite_false]

namespace KeccakTable

/-- A false rider becomes true at one more table draw with probability at most `1 / |E|`. -/
theorem rider_local_le (draws : List E) (q : Whir.Table K M)
    (remaining : draws.length < TableSumcheck.maxHeight S L) :
    Pr{let r ← ($ᵗ E)}[¬ kt.rider draws q ∧ kt.rider (draws ++ [r]) q] ≤ overE 1 := by
  simp_rw [kt.rider_iff_zeroOn]
  by_cases high : draws.length < TableSumcheck.maxHeight S L - (kt.p + 4)
  · have empty (r : E) : ¬ (¬ ZeroOn (Keccak.Gkr.mle (Keccak.Gkr.initialTable (ofK g) (kt.outputs q) (kt.bits q)))
        (riderFixed (TableSumcheck.maxHeight S L) kt.p draws) ∧
        ZeroOn (Keccak.Gkr.mle (Keccak.Gkr.initialTable (ofK g) (kt.outputs q) (kt.bits q)))
          (riderFixed (TableSumcheck.maxHeight S L) kt.p (draws ++ [r]))) := by
      rw [riderFixed_append_high _ kt.p draws r high]
      exact fun bad => bad.1 bad.2
    simp only [empty, prEvent_false, zero_le]
  · simp_rw [riderFixed_append_low _ kt.p draws _ kt.height_le (by omega) remaining]
    rw [← uniformField_prEvent]
    simp only [overE, Nat.cast_one]
    apply zeroOn_coordinate_le
    simpa only [Keccak.Gkr.mle_eq_eval] using
      Keccak.Gkr.coordinateDegree_eval
        (MvPolynomial.MLE' (Keccak.Gkr.initialTable (ofK g) (kt.outputs q) (kt.bits q)))
        (Keccak.Gkr.tablePolynomial_degree _)

end KeccakTable

end

end CompStark.Tables.Composed
