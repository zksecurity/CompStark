/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.RingSwitch.Protocol
public import ArkLib.Interaction.Oracle.Security.WitnessRefinement

/-! Executable candidate-list bad events for the six Frobenius batching stages. -/

@[expose] public section
namespace CompStark.Pcs.RingSwitch
open CompStark.BinaryFields OracleComp Interaction.Oracle.Security
open scoped ENNReal

/-- A nonzero Frobenius family vanishes after one affine stage. -/
def BadRingFamily (width : ℕ) (family : Fin 64 → E) (x : E) : Prop :=
  (∃ k : Fin (2 * width),
    frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val)) family k ≠ 0) ∧
    ∀ k : Fin width, frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val))
      (fun i => family i + x * family i ^ 2 ^ width) k = 0

/-- Retain each slice error once before evaluating its Frobenius moments. -/
@[noinline, nospecialize] def cacheFamily (family : Fin 64 → E) : Vector E 64 :=
  Vector.ofFn family

/-- Materializing the finite family preserves every slice error exactly. -/
theorem cacheFamily_eq (family : Fin 64 → E) :
    (fun i : Fin 64 => (cacheFamily family)[i.val]) = family := by
  funext i
  simp only [cacheFamily, Vector.getElem_ofFn]

/-- Finite Frobenius vanishing is decided from shared candidate values. -/
instance (width : ℕ) (family : Fin 64 → E) (x : E) :
    Decidable (BadRingFamily width family x) := by
  let values := cacheFamily family
  let cached := fun i : Fin 64 => values[i.val]
  have same : cached = family := cacheFamily_eq family
  have result : Decidable (BadRingFamily width cached x) := by
    unfold BadRingFamily
    infer_instance
  exact same ▸ result

/-- A prefix-fixed candidate family disappears at the sampled ring-switching coefficient. -/
def BadRingSwitch (width : ℕ) (candidates : List (Fin 64 → E)) (x : E) : Prop :=
  ∃ family ∈ candidates, BadRingFamily width family x

/-- Check only the decoded candidate families at this ring-switching prefix. -/
def checkBadRingSwitch (width : ℕ) (candidates : List (Fin 64 → E)) (x : E) : Bool :=
  candidates.any fun family => decide (BadRingFamily width family x)

/-- The ring-switching checker decides the explicit Frobenius event. -/
theorem checkBadRingSwitch_iff (width : ℕ) (candidates : List (Fin 64 → E)) (x : E) :
    checkBadRingSwitch width candidates x = true ↔ BadRingSwitch width candidates x := by
  simp only [checkBadRingSwitch, List.any_eq_true, decide_eq_true_eq, BadRingSwitch]

/-- Hiding columns only removes candidate families and cannot create this event. -/
theorem BadRingSwitch.mono {width : ℕ} {small large : List (Fin 64 → E)}
    (subset : small ⊆ large) {x : E} (bad : BadRingSwitch width small x) :
    BadRingSwitch width large x := by
  obtain ⟨family, member, bad⟩ := bad
  exact ⟨family, subset member, bad⟩

/-- One nonzero family has at most one bad coefficient. -/
theorem prob_badRingFamily_le (width : ℕ) (family : Fin 64 → E) :
    Pr{let x ←$ᵗ E}[BadRingFamily width family x] ≤ (1 : ENNReal) / Fintype.card E := by
  classical
  by_cases nonzero : ∃ k : Fin (2 * width),
      frobPair Finset.univ (fun i : Fin 64 => ofK (g ^ i.val)) family k ≠ 0
  · have count := card_stage_zero_le_one Finset.univ
      (fun i : Fin 64 => ofK (g ^ i.val)) family width
      (by obtain ⟨k, hk⟩ := nonzero; exact ⟨k, k.isLt, hk⟩)
    have cardinal : (Finset.univ.filter (fun x => BadRingFamily width family x)).card ≤ 1 := by
      apply (Finset.card_le_card ?_).trans count
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro k hk
      exact (Finset.mem_filter.mp hx).2.2 ⟨k, hk⟩
    have bound := (SampleableType.prEvent_uniformSample_le_div_iff
      (fun x => BadRingFamily width family x) (c := 1)).mpr cardinal
    simpa only [Nat.cast_one] using bound
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => nonzero h.1)).le.trans zero_le

/-- Zero-fill candidate inclusion preserves the original list-times-one-over-field bound. -/
theorem prob_badRingSwitch_le (width : ℕ) (masked completed : List (Fin 64 → E))
    (subset : masked ⊆ completed) :
    Pr{let x ←$ᵗ E}[BadRingSwitch width masked x] ≤
      (completed.length : ENNReal) * ((1 : ENNReal) / Fintype.card E) := by
  classical
  refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => BadRingSwitch.mono subset bad)).trans ?_
  clear subset masked
  induction completed with
  | nil =>
      simp only [BadRingSwitch, List.not_mem_nil, false_and, exists_false, prEvent_false,
        List.length_nil, Nat.cast_zero, zero_mul]
      exact le_rfl
  | cons a rest ih =>
      simp only [BadRingSwitch, List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      simpa only [BadRingSwitch, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        using add_le_add (prob_badRingFamily_le width a) ih

/-- The fixed stack's transformed slice errors are the executable family at this prefix. -/
def candidateFamily {n m p : ℕ} (layout : Layout n m) (statement : Statement n)
    (fs : Vector E p) (stack : Whir.Table K m) : Fin 64 → E :=
  fun i => frobMap (ringStages fs) (sliceError layout statement stack i)

/-- A retained-stack escape is contained in the candidate-family event on the same coefficient. -/
theorem stage_escape_subset_badRingSwitch {n m p count : ℕ} (layout : Layout n m)
    (statement : Statement n) (fs : Vector E p) (hp : p < 6)
    (committed : Whir.Table K m) (candidates : List (Whir.Table K m))
    (member : committed ∈ candidates) (x : E)
    (escape : RoundExtractor.badChallenge
      (stageExtractor layout committed statement (count + 1) p fs) x) :
    BadRingSwitch (2 ^ (5 - p)) (candidates.map (candidateFamily layout statement fs)) x := by
  obtain ⟨stack, bad, same, good⟩ := escape
  change stack = committed at same
  subst stack
  refine ⟨candidateFamily layout statement fs committed, List.mem_map.mpr ⟨committed, member, rfl⟩,
    ?_, ?_⟩
  · by_contra absent
    apply bad
    refine ⟨rfl, fun k hk => ?_⟩
    have size : 2 ^ (6 - p) = 2 * 2 ^ (5 - p) := by
      rw [show 6 - p = (5 - p) + 1 by omega, pow_succ, mul_comm]
    by_contra nonzero
    exact absent ⟨⟨k, size ▸ hk⟩, nonzero⟩
  · intro k
    have next := good k.val (by simpa only [show 6 - (p + 1) = 5 - p by omega] using k.isLt)
    simpa only [candidateFamily, frobMap_ringStages_push] using next

open StandardBcs

/-- One fixed ring-family input has the Annex A one-root bound. -/
def ringSchema (width : ℕ) : BadSchema E where
  Input := Fin 64 → E
  equality := inferInstance
  isQuery := false
  MaskLE small large := small = large
  Bad := BadRingFamily width
  check family x := decide (BadRingFamily width family x)
  check_iff _ _ := decide_eq_true_iff
  monotone _ _ same _ _ bad := same ▸ bad
  error := Erased.mk ((1 : ENNReal) / Fintype.card E)
  bad_bound family := by
    simpa only [Erased.out_mk] using prob_badRingFamily_le width family

/-- The ring classifier marks all six public draws as algebraic. -/
def ringSchemas : (count p : ℕ) → BadSchemas (publicCoin count)
  | 0, _ => PUnit.unit
  | count + 1, p => ⟨ringSchema (2 ^ (5 - p)), ringSchemas count (p + 1)⟩

/-- Every retained ring stage is annotated by its actual transformed slice-error family. -/
def ringStageAnnotation {n m : ℕ} (layout : Layout n m)
    (statement : Statement n) (committed : Whir.Table K m) : (count p : ℕ) → (fs : Vector E p) →
    count + p ≤ 6 → BadAnnotation (publicCoin count) (ringSchemas count p)
      (stageExtractor layout committed statement count p fs)
  | 0, _, _, _ => PUnit.unit
  | count + 1, p, fs, bound =>
      ⟨candidateFamily layout statement fs committed,
        (fun x escape => by
          have bad := stage_escape_subset_badRingSwitch layout statement fs (by omega)
            committed [committed] (List.mem_singleton_self _) x escape
          obtain ⟨family, member, bad⟩ := bad
          cases List.mem_singleton.mp member
          exact bad),
        fun x => ringStageAnnotation layout statement committed count (p + 1) (fs.push x) (by omega)⟩

end CompStark.Pcs.RingSwitch
