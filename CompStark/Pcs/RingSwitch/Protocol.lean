/-
Adapted from Verified-zkEVM/leanerVM (Apache-2.0):
  LeanerVM/Protocol/ToArkLib/Flock/RingSwitch.lean
  LeanerVM/Protocol/ToArkLib/Flock/Security.lean
-/
module

public import CompStark.Pcs.RingSwitch.Frobenius
public import CompStark.Pcs.RingSwitch.Fields
public import ArkLib.ProofSystem.Whir.Certificate
public import CompStark.Pcs.Weights

/-!
# Annex A ring switching on a fixed committed stack

The six verifier challenges have shifts 32, 16, 8, 4, 2, 1. The input values are fixed
before these challenges. Every state binds its witness to the same stack. The output is
an E-valued `Whir.Claim` on its K-valued entries, suitable for a subsequent PCS opening.
The certificate does not extract a stack from a commitment; that is the PCS's obligation.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
open CompStark.BinaryFields

namespace CompStark.Pcs.RingSwitch

/-- Uniform base-field sampling uses the wire bit pattern directly. -/
instance sampleableK : SampleableType K :=
  haveI : NeZero (2 ^ 64) := ⟨by decide⟩
  SampleableType.ofEquiv
    { toFun := fun i : Fin (2 ^ 64) => BF64.ofBitVec (BitVec.ofFin i)
      invFun := fun x : K => x.toBitVec.toFin
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Uniform extension-field sampling draws the three limbs independently. -/
instance sampleableE : SampleableType E :=
  SampleableType.ofEquiv
    { toFun := fun v : Vector K 3 => CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
      invFun := fun x : E => CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The packed Keccak region and its coordinate lift into the committed stack. -/
structure Layout (n stackVars : ℕ) where
  /-- The packed region read from a stack. -/
  packed : Whir.Table K stackVars → Whir.Table K n
  /-- The 64 Boolean slices read from the same stack. -/
  slices : Whir.Table K stackVars → Fin 64 → Whir.Table E n
  /-- The point lift reading the region's MLE from the stack's MLE. -/
  lift : (Fin n → E) → (Fin stackVars → E)
  /-- Every slice entry is a bit. -/
  boolean : ∀ stack i u, slices stack i u = 0 ∨ slices stack i u = 1
  /-- The bit slices pack with the polynomial-basis weights `g^i`. -/
  packing : ∀ stack u, ofK (packed stack u) =
    ∑ i : Fin 64, ofK (g ^ i.val) * slices stack i u
  /-- Evaluating the region is evaluating the stack at the lifted point. -/
  read : ∀ stack point, Whir.mle (fun u => ofK (packed stack u)) point =
    Whir.mle (fun u => ofK (stack u)) (lift point)

/-- The 64 alleged bit-slice values at their shared extension-field point. -/
structure Statement (n : ℕ) where
  /-- The common point coming from the Keccak GKR reduction. -/
  point : Fin n → E
  /-- The alleged evaluations, bound before the first ring-switching challenge. -/
  values : Fin 64 → E

/-- The first `p` stages, with the Annex A shift order. -/
def ringStages {p : ℕ} (fs : Vector E p) : List (ℕ × E) :=
  List.ofFn fun i : Fin p => (2 ^ (5 - i.val), fs[i])

/-- Appending a coefficient appends precisely its Frobenius stage. -/
theorem ringStages_push {p : ℕ} (fs : Vector E p) (x : E) :
    ringStages (fs.push x) = ringStages fs ++ [(2 ^ (5 - p), x)] := by
  rw [ringStages, List.ofFn_succ_last]
  simp [ringStages]

/-- Applying one further coefficient acts on the output of all preceding stages. -/
theorem frobMap_ringStages_push {p : ℕ} (fs : Vector E p) (x a : E) :
    frobMap (ringStages (fs.push x)) a =
      frobMap (ringStages fs) a + x * frobMap (ringStages fs) a ^ 2 ^ 2 ^ (5 - p) := by
  rw [ringStages_push, frobMap_append]
  rfl

/-- The error of a slice claim on a particular stack. -/
def sliceError {n m : ℕ} (layout : Layout n m) (statement : Statement n)
    (stack : Whir.Table K m) (i : Fin 64) : E :=
  statement.values i - Whir.mle (layout.slices stack i) statement.point

/-- The target of the weighted stack opening after all six challenges. -/
def ringTarget {n : ℕ} (statement : Statement n) (fs : Vector E 6) : E :=
  ∑ i : Fin 64, ofK (g ^ i.val) * frobMap (ringStages fs) (statement.values i)

/-- The MLE-friendly weight: a linear combination of equality weights at lifted twists. -/
def ringWeight {n m : ℕ} (layout : Layout n m) (statement : Statement n)
    (fs : Vector E 6) : Whir.Table E m := fun u =>
  ((frobTerms (ringStages fs)).map fun t =>
    t.1 * Whir.eqWeight (layout.lift (fun i => statement.point i ^ 2 ^ t.2)) u).sum

/-- Shared tensor images of every lifted Frobenius term. -/
@[macro_inline] def ringWeightWith {n m : ℕ} (lift : (Fin n → E) → (Fin m → E))
    (statement : Statement n) (fs : Vector E 6) : Whir.Table E m :=
  Pcs.tensorCombination ((frobTerms (ringStages fs)).map fun term =>
    (term.1, lift (fun i => statement.point i ^ 2 ^ term.2)))

/-- Shared tensor images preserve each lifted Frobenius contribution. -/
theorem ringWeightWith_eq {n m : ℕ} (lift : (Fin n → E) → (Fin m → E))
    (statement : Statement n) (fs : Vector E 6) (u : Whir.Cube m) :
    ringWeightWith lift statement fs u =
      ((frobTerms (ringStages fs)).map fun term =>
        term.1 * Whir.eqWeight (lift (fun i => statement.point i ^ 2 ^ term.2)) u).sum := by
  simp only [ringWeightWith, Pcs.tensorCombination_eq, List.map_map, Function.comp_def]

/-- The physical ring layout supplies its lift to the shared tensor evaluator. -/
@[macro_inline] def ringWeightFast {n m : ℕ} (layout : Layout n m) (statement : Statement n)
    (fs : Vector E 6) : Whir.Table E m := ringWeightWith layout.lift statement fs

/-- Compiled ring weights use the exactly equal shared tensor evaluator. -/
@[csimp] theorem ringWeight_code : @ringWeight = @ringWeightFast := by
  funext n m layout statement fs u
  exact (ringWeightWith_eq layout.lift statement fs u).symm

/-- The exact claim interface consumed by the WHIR opening certificate. -/
def outputClaim {n m : ℕ} (layout : Layout n m) (statement : Statement n)
    (fs : Vector E 6) : Whir.Claim E m :=
  ⟨ringWeight layout statement fs, ringTarget statement fs⟩

/-- A stack-bound input relation: all 64 slice claims refer to this committed table. -/
def inputState {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) : KnowledgeState where
  Witness := Whir.Table K m
  holds stack := stack = committed ∧
    ∀ i, statement.values i = Whir.mle (layout.slices stack i) statement.point

/-- The shrinking family of Frobenius equations, with the witness fixed to the commitment. -/
def stageState {n m p : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) (fs : Vector E p) : KnowledgeState where
  Witness := Whir.Table K m
  holds stack := stack = committed ∧ ∀ k < 2 ^ (6 - p),
    frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
      (fun i => frobMap (ringStages fs) (sliceError layout statement stack i)) k = 0

/-- The terminal witness is the committed stack satisfying the WHIR weighted claim. -/
def outputState {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) (fs : Vector E 6) : KnowledgeState where
  Witness := Whir.Table K m
  holds stack := stack = committed ∧ (outputClaim layout statement fs).Holds (fun u => ofK (stack u))

/-- Six independent public verifier moves, with no prover message between them. -/
def draws : ℕ → Protocol
  | 0 => .done
  | count + 1 => .public .receiver E fun _ => draws count

/-- The public-coin presentation samples each coefficient uniformly in E. -/
def publicCoin [SampleableType E] : (count : ℕ) → PublicCoin (draws count)
  | 0 => .done
  | count + 1 => .challenge (publicCoin count)

/-- Total backward maps retain the same committed stack through every challenge. -/
def stageExtractor {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) : (count p : ℕ) → (fs : Vector E p) →
      RoundExtractor (draws count).tree (stageState layout committed statement fs)
  | 0, _, _ => PUnit.unit
  | count + 1, p, fs => fun x =>
      ⟨stageState layout committed statement (fs.push x), id,
        stageExtractor layout committed statement count (p + 1) (fs.push x)⟩

open scoped Classical in
/-- A nonzero family at a fixed prefix escapes the next stage at one coefficient at most.
This is the ring-switching part of leanerVM's `ringDrawSecurity`. -/
theorem card_bad_stage_le_one [Fintype E] {n m p : ℕ} (layout : Layout n m)
    (committed : Whir.Table K m) (statement : Statement n) (fs : Vector E p) (hp : p < 6) :
    (Finset.univ.filter fun x : E => ∃ stack,
      ¬ (stageState layout committed statement fs).holds stack ∧
        (stageState layout committed statement (fs.push x)).holds stack).card ≤ 1 := by
  classical
  by_cases good : (stageState layout committed statement fs).holds committed
  · have empty : ∀ x : E, ¬ ∃ stack,
        ¬ (stageState layout committed statement fs).holds stack ∧
          (stageState layout committed statement (fs.push x)).holds stack := by
      rintro x ⟨stack, bad, next⟩
      exact bad (next.1.symm ▸ good)
    simp only [empty, Finset.filter_false, Finset.card_empty, Nat.zero_le]
  · have nonzero : ∃ k < 2 * 2 ^ (5 - p),
        frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
          (fun i => frobMap (ringStages fs) (sliceError layout statement committed i)) k ≠ 0 := by
      have hpow : 2 ^ (6 - p) = 2 * 2 ^ (5 - p) := by
        rw [show 6 - p = (5 - p) + 1 by omega, pow_succ, mul_comm]
      by_contra hn
      apply good
      refine ⟨rfl, fun k hk => ?_⟩
      by_contra hk0
      exact hn ⟨k, hpow ▸ hk, hk0⟩
    refine (Finset.card_le_card fun x hx => ?_).trans
      (card_stage_zero_le_one Finset.univ _ _ (2 ^ (5 - p)) nonzero)
    obtain ⟨stack, _, next⟩ := (Finset.mem_filter.mp hx).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun k hk => ?_⟩
    have hnext := next.2 k (by rwa [show 6 - (p + 1) = 5 - p by omega])
    rw [next.1] at hnext
    simpa only [frobMap_ringStages_push] using hnext

/-- At zero stages, conjugate injectivity identifies the invariant with the input claims. -/
theorem input_iff_stage_zero {n m : ℕ} (layout : Layout n m)
    (committed stack : Whir.Table K m) (statement : Statement n) :
    (inputState layout committed statement).holds stack ↔
      (stageState layout committed statement #v[]).holds stack := by
  constructor
  · rintro ⟨hbind, hclaims⟩
    refine ⟨hbind, fun k _ => ?_⟩
    have herr : ∀ i, sliceError layout statement stack i = 0 := fun i => by
      rw [sliceError, hclaims i, sub_self]
    simp only [ringStages, List.ofFn_zero, frobMap, frobPair, herr,
      zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, Finset.sum_const_zero]
  · rintro ⟨hbind, hzero⟩
    refine ⟨hbind, fun i => sub_eq_zero.mp ?_⟩
    exact ringSwitch_injective (sliceError layout statement stack)
      (fun k hk => by simpa only [ringStages, List.ofFn_zero, frobMap, frobPair] using hzero k hk) i

/-- Prover preservation is structural: ring switching has only verifier moves. -/
theorem stageExtractor_preserving {n m : ℕ} (layout : Layout n m)
    (committed : Whir.Table K m) (statement : Statement n) (count p : ℕ) (fs : Vector E p) :
    (stageExtractor layout committed statement count p fs).IsProverPreserving (draws count).roles := by
  induction count generalizing p with
  | zero => trivial
  | succ count ih =>
    constructor
    · intro x h
      cases h
    · intro x
      exact ih (p + 1) (fs.push x)

/-- The certificate's named extractor starts with the actual slice-claim relation. -/
def extractor {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) :
    RoundExtractor (draws 6).tree (inputState layout committed statement) :=
  (stageExtractor layout committed statement 6 0 #v[]).changeInputState
    (inputState layout committed statement) (Equiv.refl _)

/-- Each authored challenge has the per-stage `1 / |E|` error of Annex A. -/
noncomputable def challenges [SampleableType E] : (count : ℕ) →
    RoundExtractor.ChallengeSchedule (draws count).tree (draws count).roles
  | 0 => PUnit.unit
  | count + 1 => ⟨($ᵗ E, (1 : ENNReal) / 2 ^ 192), fun _ => challenges count⟩

/-- Every fixed-prefix challenge has at most one bad extension in the remaining six stages. -/
theorem stageExtractor_bounded [SampleableType E] {n m : ℕ} (layout : Layout n m)
    (committed : Whir.Table K m) (statement : Statement n) (count p : ℕ) (fs : Vector E p)
    (hp : count + p ≤ 6) :
    (stageExtractor layout committed statement count p fs).IsLocallyBounded
      (draws count).roles (challenges count) := by
  classical
  induction count generalizing p with
  | zero => trivial
  | succ count ih =>
      constructor
      · apply Whir.localGame_bounded
        change Pr{let x ← $ᵗ E}[∃ stack,
          ¬ (stageState layout committed statement fs).holds stack ∧
            (stageState layout committed statement (fs.push x)).holds stack] ≤
          (1 : ENNReal) / 2 ^ 192
        let : Fintype E := Fintype.ofFinite E
        have bound := (SampleableType.prEvent_uniformSample_le_div_iff
          (fun x : E => ∃ stack,
            ¬ (stageState layout committed statement fs).holds stack ∧
              (stageState layout committed statement (fs.push x)).holds stack) (c := 1)).mpr
          (card_bad_stage_le_one layout committed statement fs (by omega))
        simpa only [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using bound
      · intro x
        exact ih (p + 1) (fs.push x) (by omega)

/-- Named extraction and the six per-stage errors for the fixed committed stack. -/
noncomputable def certificate [SampleableType E] {n m : ℕ} (layout : Layout n m)
    (committed : Whir.Table K m) (statement : Statement n) :
    KnowledgeCertificate (draws 6).tree (draws 6).roles (inputState layout committed statement) where
  extractor := extractor layout committed statement
  challenges := challenges 6
  prover_preserving := (stageExtractor layout committed statement 6 0 #v[]).isProverPreserving_changeInputState (inputState layout committed statement) (Equiv.refl _)
      (fun stack => input_iff_stage_zero layout committed stack statement) _
      (stageExtractor_preserving layout committed statement 6 0 #v[])
  local_bound := (stageExtractor layout committed statement 6 0 #v[]).isLocallyBounded_changeInputState
    (inputState layout committed statement) (Equiv.refl _)
    (fun stack => input_iff_stage_zero layout committed stack statement) _ _
    (stageExtractor_bounded layout committed statement 6 0 #v[] (by omega))

/-- Collect the six challenges in their chronological order. -/
def coefficients : (count : ℕ) → (draws count).tree.ExecutionPath → Vector E count
  | 0, _ => #v[]
  | count + 1, path => Vector.ofFn (Fin.cons (path.1 : E) (fun i => (coefficients count path.2)[i]))

/-- Named identification of the terminal stack carrier; no witness is chosen by existence. -/
def terminalWitnessEquiv {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) (path : (draws 6).tree.ExecutionPath) :
    ((extractor layout committed statement).terminalState path).Witness ≃ Whir.Table K m :=
  Equiv.refl _

/-- Equality weights commute with characteristic-two Frobenius powers. -/
theorem eqWeight_frobenius {n : ℕ} (point : Fin n → E) (u : Whir.Cube n) (k : ℕ) :
    Whir.eqWeight point u ^ 2 ^ k = Whir.eqWeight (fun i => point i ^ 2 ^ k) u := by
  simp only [Whir.eqWeight, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  cases u i <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_pow_char_pow, one_pow]

/-- A Boolean table's MLE twists only its evaluation point under Frobenius. -/
theorem mle_boolean_frobenius {n : ℕ} (f : Whir.Table E n)
    (boolean : ∀ u, f u = 0 ∨ f u = 1) (point : Fin n → E) (k : ℕ) :
    Whir.mle f point ^ 2 ^ k = Whir.mle f (fun i => point i ^ 2 ^ k) := by
  simp only [Whir.mle, sum_pow_char_pow, mul_pow, eqWeight_frobenius]
  apply Finset.sum_congr rfl
  intro u _
  rcases boolean u with h | h <;>
    simp only [h, zero_pow (pow_ne_zero _ two_ne_zero), one_pow]

/-- Packing the Boolean slices commutes with multilinear evaluation. -/
theorem packing_mle {n m : ℕ} (layout : Layout n m) (stack : Whir.Table K m)
    (point : Fin n → E) :
    (∑ i : Fin 64, ofK (g ^ i.val) * Whir.mle (layout.slices stack i) point) =
      Whir.mle (fun u => ofK (layout.packed stack u)) point := by
  simp only [Whir.mle, layout.packing, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every Frobenius-sum term becomes an equality-weight opening on the lifted stack point. -/
theorem frobenius_terms_weighted {n m : ℕ} (layout : Layout n m) (stack : Whir.Table K m)
    (point : Fin n → E) (terms : List (E × ℕ)) :
    (∑ i : Fin 64, ofK (g ^ i.val) *
      (terms.map fun t => t.1 * Whir.mle (layout.slices stack i) point ^ 2 ^ t.2).sum) =
    ∑ u, (terms.map fun t =>
      t.1 * Whir.eqWeight (layout.lift (fun j => point j ^ 2 ^ t.2)) u).sum * ofK (stack u) := by
  induction terms with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, zero_mul, Finset.sum_const_zero]
  | cons t terms ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, add_mul, Finset.sum_add_distrib]
      refine congrArg₂ (fun a b : E => a + b) ?_ ih
      calc
        _ = t.1 * ∑ i : Fin 64, ofK (g ^ i.val) *
            Whir.mle (layout.slices stack i) (fun j => point j ^ 2 ^ t.2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [mle_boolean_frobenius (n := n) (layout.slices stack i)
            (layout.boolean stack i) point t.2]
          ring
        _ = t.1 * Whir.mle (fun u => ofK (layout.packed stack u))
            (fun j => point j ^ 2 ^ t.2) := by rw [packing_mle]
        _ = _ := by
          rw [layout.read]
          simp only [Whir.mle, Finset.mul_sum, mul_assoc]

/-- The transformed true slice values give precisely the weighted stack inner product. -/
theorem transformed_slices_eq_weighted {n m : ℕ} (layout : Layout n m)
    (stack : Whir.Table K m) (statement : Statement n) (fs : Vector E 6) :
    (∑ i : Fin 64, ofK (g ^ i.val) *
      frobMap (ringStages fs) (Whir.mle (layout.slices stack i) statement.point)) =
      ∑ u, ringWeight layout statement fs u * ofK (stack u) := by
  simp only [frobMap_eq_sum, ringWeight]
  exact frobenius_terms_weighted layout stack statement.point (frobTerms (ringStages fs))

/-- The last stage's single zero-error equation is the weighted WHIR claim. -/
theorem stage_six_iff {n m : ℕ} (layout : Layout n m) (committed stack : Whir.Table K m)
    (statement : Statement n) (fs : Vector E 6) :
    (stageState layout committed statement fs).holds stack ↔
      (outputState layout committed statement fs).holds stack := by
  have errorSum :
      frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
        (fun i => frobMap (ringStages fs) (sliceError layout statement stack i)) 0 =
      ringTarget statement fs - ∑ u, ringWeight layout statement fs u * ofK (stack u) := by
    simp only [frobPair, pow_zero, pow_one, sliceError]
    change (∑ i : Fin 64, ofK (g ^ i.val) *
      (frobMapHom (ringStages fs)) (statement.values i -
        Whir.mle (layout.slices stack i) statement.point)) = _
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
    change ringTarget statement fs - (∑ i : Fin 64, ofK (g ^ i.val) *
      frobMap (ringStages fs) (Whir.mle (layout.slices stack i) statement.point)) = _
    rw [transformed_slices_eq_weighted]
  simp only [stageState, outputState, Nat.sub_self, pow_zero, Nat.lt_one_iff,
    forall_eq, errorSum, sub_eq_zero, outputClaim, Whir.Claim.Holds]
  exact and_congr_right fun _ => eq_comm

/-- The terminal predicate is exactly the weighted claim on the same committed stack. -/
theorem terminal_iff {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) (path : (draws 6).tree.ExecutionPath)
    (witness : ((extractor layout committed statement).terminalState path).Witness) :
    ((extractor layout committed statement).terminalState path).holds witness ↔
      (outputState layout committed statement (coefficients 6 path)).holds
        (terminalWitnessEquiv layout committed statement path witness) := by
  let fs : Vector E 6 := #v[path.1, path.2.1, path.2.2.1, path.2.2.2.1,
    path.2.2.2.2.1, path.2.2.2.2.2.1]
  have hfs : fs = coefficients 6 path := by
    apply Vector.ext
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst i <;> rfl
  change (stageState layout committed statement fs).holds witness ↔
    (outputState layout committed statement (coefficients 6 path)).holds witness
  rw [hfs]
  exact stage_six_iff layout committed witness statement (coefficients 6 path)


/-- Weighted WHIR claims over a publicly fixed committed stack. -/
def weightedClaimFamily (m : ℕ) : ClaimFamily (Whir.Table K m) :=
  ⟨fun _ => Whir.Claim E m⟩

/-- The PCS endpoint retains the stack binding as well as the weighted claim. -/
def weightedClaimProblem (m : ℕ) : Problem (weightedClaimFamily m) where
  Witness _ _ := Whir.Table K m
  admissible _ _ := True
  rel committed claim stack := stack = committed ∧ claim.Holds (fun u => ofK (stack u))
  rel_admissible _ _ _ _ := trivial

/-- The certificate terminates at the weighted WHIR claim on its named stack witness. -/
def terminalRelation {n m : ℕ} (layout : Layout n m) (committed : Whir.Table K m)
    (statement : Statement n) :
    TerminalRelation (extractor layout committed statement) (weightedClaimProblem m)
      (fun _ => committed) (fun path => outputClaim layout statement (coefficients 6 path)) where
  witnessEquiv := terminalWitnessEquiv layout committed statement
  knowledge_iff := terminal_iff layout committed statement

end CompStark.Pcs.RingSwitch
