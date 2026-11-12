/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.ExactDecoder
public import CompStark.Pcs.Parameters

/-! The production WHIR ladder: six initial variables, four subsequent variables,
at most five plaintext variables, and inverse-rate exponents `r`, `r + 3`, `r + 6`, ... . -/

@[expose] public section

namespace CompStark.Pcs

open CompStark.BinaryFields

open CompStark.Pcs (johnsonSlack)

/-- One level's integer Johnson search result; `gap` is the upper slack condition of `Whir.LevelSecurity.Valid`. -/
structure JohnsonChoice (vars rate : ℕ) where
  /-- Integer selected by the reduced-rate Johnson search. -/
  m : ℕ
  /-- The interpolation multiplicity is positive. -/
  positive_m : 0 < m
  /-- The certified finite selector searches this multiplicity. -/
  bounded_m : m ≤ 2 ^ (vars + rate)
  /-- The analysis radius is positive. -/
  gap : johnsonSlack vars rate m <
    1 - Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate))

/-- Search results are needed only at positive-rate levels with at least two variables. -/
abbrev JohnsonChoices := ∀ vars rate : ℕ, 2 ≤ vars → 0 < rate → JohnsonChoice vars rate

/-- The level's reduced-rate security parameter. -/
noncomputable def JohnsonChoice.security {vars rate : ℕ} (choice : JohnsonChoice vars rate) :
    Whir.LevelSecurity := Pcs.johnsonLevelSecurity vars rate choice.m

/-- An admissible search result discharges the level security contract. -/
theorem JohnsonChoice.valid {vars rate : ℕ} (choice : JohnsonChoice vars rate)
    (hv : 0 < vars) (hr : 0 < rate) (hd : vars + rate ≤ 64) :
    choice.security.Valid (Pcs.encoding vars rate hd) :=
  ⟨hv, hr, hd, Pcs.johnsonSlack_pos rate hv choice.positive_m, choice.gap⟩

/-- The converted security parameter has exactly the production reduced-rate radius. -/
theorem JohnsonChoice.radius {vars rate : ℕ} (choice : JohnsonChoice vars rate)
    (hd : vars + rate ≤ 64) :
    Whir.radius (Pcs.encoding vars rate hd) choice.security =
      1 - Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) -
        Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) / (choice.m : ℝ) := by
  dsimp [Whir.radius, Whir.reducedRate, JohnsonChoice.security, Pcs.johnsonLevelSecurity, johnsonSlack, Pcs.encoding]

/-- The cutoff has exact integer coverage and makes the finite GS selector succeed. -/
theorem JohnsonChoice.cutoff_spec {vars rate : ℕ} (choice : JohnsonChoice vars rate)
    (hv : 2 ≤ vars) :
    let cutoff := Pcs.agreementCutoff (2 ^ vars) (2 ^ (vars + rate)) choice.m
    cutoff ≤ 2 ^ (vars + rate) ∧
      (CompPoly.GuruswamiSudan.finiteGSParamSelector.choose (2 ^ vars) (2 ^ (vars + rate))
        (2 ^ (vars + rate) - cutoff)).isSome ∧
      Pcs.CutoffCorrect vars rate cutoff
        (1 - (1 + 1 / (choice.m : ℝ)) *
          Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate))) := by
  let length := 2 ^ (vars + rate)
  have hk : 1 < 2 ^ vars := (by decide : 1 < 2 ^ 2).trans_le
    (Nat.pow_le_pow_right (by decide) hv)
  have hlen : 0 < length := Nat.two_pow_pos _
  have realBound : (1 + 1 / (choice.m : ℝ)) *
      Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / length) ≤ 1 := by
    have gap := choice.gap
    dsimp only [johnsonSlack] at gap
    dsimp only [length]
    push_cast
    have : (1 + 1 / (choice.m : ℝ)) * Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) =
        Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) +
          Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) / choice.m := by ring
    linarith
  have full : Pcs.johnsonAgreement (2 ^ vars) length choice.m length :=
    (Pcs.johnsonAgreement_iff_real _ _ _ _ choice.positive_m hlen).mpr
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right realBound
        (show (0 : ℝ) ≤ length by positivity)))
  let cutoff := Pcs.agreementCutoff (2 ^ vars) length choice.m
  have le : cutoff ≤ length :=
    (Pcs.agreementCutoff_le_iff _ _ _ full length le_rfl).mpr full
  have good : Pcs.johnsonAgreement (2 ^ vars) length choice.m cutoff :=
    (Pcs.agreementCutoff_le_iff _ _ _ full cutoff le).mp le_rfl
  have pos : 0 < cutoff := by
    by_contra h
    have hz : cutoff = 0 := by omega
    have positive : 0 < (choice.m + 1) ^ 2 * (2 ^ vars - 1) * length :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) hlen
    unfold Pcs.johnsonAgreement at good
    rw [hz, Nat.zero_pow (by decide), Nat.mul_zero] at good
    omega
  exact ⟨le, Pcs.finiteGSParamSelector_isSome _ _ _ _ hk hlen choice.positive_m
    choice.bounded_m pos le good, Pcs.johnsonCutoff_correct vars rate choice.m choice.positive_m full⟩

/-- The GS list at the discrete Johnson cutoff has the exact analytical WHIR contract. -/
theorem JohnsonChoice.decoder_correct {S : Type} [Field S] [BEq S] [LawfulBEq S]
    [DecidableEq S] [Fintype S] [Algebra (ZMod 2) S]
    {vars rate : ℕ} (choice : JohnsonChoice vars rate) (hv : 2 ≤ vars) (hr : 0 < rate)
    (hd : vars + rate ≤ 64) (phi : K →+* S)
    (ctx : Pcs.GsScalarDecoder S) (lanes : ℕ) :
    (Pcs.gsListDecoder phi vars rate lanes hd ctx
      (Pcs.agreementCutoff (2 ^ vars) (2 ^ (vars + rate)) choice.m)).Correct phi
      (Whir.radius (Pcs.encoding vars rate hd) choice.security)
      (Whir.listBound (Pcs.encoding vars rate hd) choice.security) := by
  obtain ⟨le, selected, cutoff⟩ := choice.cutoff_spec hv
  obtain ⟨params, selected⟩ := Option.isSome_iff_exists.mp selected
  apply Pcs.gsListDecoder_correct phi vars rate lanes hd ctx _ le params selected choice.security
    (choice.valid (by omega) hr hd)
  have radius : Whir.radius (Pcs.encoding vars rate hd) choice.security =
      1 - (1 + 1 / (choice.m : ℝ)) *
        Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) := by
    rw [choice.radius]
    ring
  rw [radius]
  exact cutoff

/-- Exact codeword recognition preserves the certified base-field proximity decoder. -/
theorem JohnsonChoice.checked_decoder_correct {vars rate : ℕ} (choice : JohnsonChoice vars rate)
    (hv : 2 ≤ vars) (hr : 0 < rate) (hd : vars + rate ≤ 64) (lanes : ℕ) :
    (Pcs.checkedBaseDecoder vars rate lanes hd
      (Pcs.agreementCutoff (2 ^ vars) (2 ^ (vars + rate)) choice.m)).Correct (RingHom.id K)
      (Whir.radius (Pcs.encoding vars rate hd) choice.security)
      (Whir.listBound (Pcs.encoding vars rate hd) choice.security) := by
  rw [Pcs.checkedBaseDecoder_eq]
  exact choice.decoder_correct hv hr hd (RingHom.id K) Pcs.baseGsContext lanes

/-- Inverse-rate exponent of the first encoded level. -/
def scheduleRate : {vars : ℕ} → Whir.Schedule K vars → ℕ
  | _, .last _ _ encoding _ => encoding.rate
  | _, .more _ encoding _ _ => encoding.rate

/-- The query counts consumed by each level, in transcript order. -/
def scheduleQueries : {vars : ℕ} → Whir.Schedule K vars → List ℕ
  | _, .last _ _ _ queries => [queries]
  | _, .more _ _ queries next => queries :: scheduleQueries next

/-- Transporting a schedule's dimension preserves its query ladder. -/
@[simp] theorem scheduleQueries_cast {a b : ℕ} (h : a = b) (schedule : Whir.Schedule K a) :
    scheduleQueries (h ▸ schedule) = scheduleQueries schedule := by
  subst b
  rfl

/-- An encoded schedule with certified GS decoders at every level and fold row count. -/
structure CertifiedSchedule (vars rate : ℕ) where
  /-- The actual nonempty WHIR schedule. -/
  schedule : Whir.Schedule K vars
  /-- Integer Johnson choice at every level. -/
  johnson : Pcs.JohnsonParameters schedule
  /-- All encoded levels satisfy WHIR's contracts. -/
  valid : schedule.Valid (algebraMap K E) (Pcs.johnsonSecurity schedule johnson)
  /-- The initial inverse-rate exponent. -/
  headRate : scheduleRate schedule = rate
  /-- Certified GS proximity decoder at the first encoded level. -/
  decoder : Whir.InitialDecoder schedule
  /-- Exact list coverage and real Johnson list bound. -/
  correct : Whir.InitialDecoder.Correct decoder (Pcs.johnsonSecurity schedule johnson)
  /-- Extension-field GS decoders at every encoded level and intermediate row count. -/
  decoders : Whir.DecoderFamily (E := E) schedule
  /-- Exact suffix coverage and list bounds for all row counts. -/
  familyCorrect : Whir.DecoderFamily.Correct (algebraMap K E) schedule decoders
    (Pcs.johnsonSecurity schedule johnson)

/-- Analytical security associated with the runtime schedule's integer choices. -/
noncomputable def CertifiedSchedule.security {vars rate : ℕ} (schedule : CertifiedSchedule vars rate) :=
  Pcs.johnsonSecurity schedule.schedule schedule.johnson

/-- Transporting a certified dimension preserves the consumed query counts. -/
@[simp] theorem certifiedScheduleQueries_cast {a b rate : ℕ} (h : a = b)
    (schedule : CertifiedSchedule a rate) :
    scheduleQueries ((h ▸ schedule).schedule) = scheduleQueries schedule.schedule := by
  subst b
  rfl

/-- Build a production level, increasing the inverse-rate exponent by three when recursing.
Its domain loses one variable at every transition; `63` is the production NTT cap. -/
def ladder (choices : JohnsonChoices) (queries : ℕ → ℕ) (vars fold rate : ℕ)
    (hvars : fold + 2 ≤ vars) (hfold : 0 < fold) (hrate : 0 < rate)
    (hdim : vars - fold + rate ≤ 63) : CertifiedSchedule vars rate := by
  let tail := vars - fold
  have htail : 2 ≤ tail := by dsimp [tail]; omega
  have heq : fold + tail = vars := by dsimp [tail]; omega
  have hd : tail + rate ≤ 64 := by dsimp [tail]; omega
  let enc := Pcs.encoding tail rate hd
  let choice := choices tail rate htail hrate
  have hv := choice.valid (by omega) hrate hd
  have hb := Pcs.baseEncodingContract tail rate hd hrate
  have he := Pcs.extensionEncodingContract tail rate hd hrate
  let cutoff := Pcs.agreementCutoff (2 ^ tail) (2 ^ (tail + rate)) choice.m
  let decoder := Pcs.checkedBaseDecoder tail rate fold hd cutoff
  let decoders := fun lanes => Pcs.gsListDecoder (algebraMap K E) tail rate lanes hd
    Pcs.extensionGsContext cutoff
  have familyCorrect (lanes : ℕ) : (decoders lanes).Correct (algebraMap K E)
      (Whir.radius enc choice.security) (Whir.listBound enc choice.security) := by
    let : Fintype E := Fintype.ofFinite E
    let : Algebra (ZMod 2) E := ZMod.algebra E 2
    exact choice.decoder_correct htail hrate hd (algebraMap K E) Pcs.extensionGsContext lanes
  by_cases last : tail ≤ 5
  · have result : CertifiedSchedule (fold + tail) rate :=
      { schedule := .last fold tail enc (queries rate)
        johnson := choice.m
        valid := ⟨hfold, hv, hb, he⟩
        headRate := rfl
        decoder := decoder
        correct := choice.checked_decoder_correct htail hrate hd fold
        decoders := decoders
        familyCorrect := familyCorrect }
    exact heq ▸ result
  · have nextdim : tail - 4 + (rate + 3) ≤ 63 := by dsimp [tail] at *; omega
    let next := ladder choices queries tail 4 (rate + 3) (by omega) (by decide) (by omega) nextdim
    have result : CertifiedSchedule (fold + tail) rate :=
      { schedule := .more fold enc (queries rate) next.schedule
        johnson := (choice.m, next.johnson)
        valid := ⟨hfold, hv, hb, he, next.valid⟩
        headRate := rfl
        decoder := decoder
        correct := choice.checked_decoder_correct htail hrate hd fold
        decoders := (decoders, next.decoders)
        familyCorrect := ⟨familyCorrect, next.familyCorrect⟩ }
    exact heq ▸ result
termination_by vars
decreasing_by omega

/-- The first encoded domain obeys the ladder's explicit rate and dimension cap. -/
theorem ladder_headRate (choices : JohnsonChoices) (queries : ℕ → ℕ)
    (vars fold rate : ℕ) (hvars : fold + 2 ≤ vars) (hfold : 0 < fold)
    (hrate : 0 < rate) (hdim : vars - fold + rate ≤ 63) :
    scheduleRate (ladder choices queries vars fold rate hvars hfold hrate hdim).schedule = rate :=
  (ladder choices queries vars fold rate hvars hfold hrate hdim).headRate

/-- One ladder level consumes its rate-indexed query count before the recursive tail. -/
theorem ladder_scheduleQueries (choices : JohnsonChoices) (queries : ℕ → ℕ)
    (vars fold rate : ℕ) (hvars : fold + 2 ≤ vars) (hfold : 0 < fold)
    (hrate : 0 < rate) (hdim : vars - fold + rate ≤ 63) :
    scheduleQueries (ladder choices queries vars fold rate hvars hfold hrate hdim).schedule =
      if last : vars - fold ≤ 5 then [queries rate]
      else queries rate :: scheduleQueries (ladder choices queries (vars - fold) 4 (rate + 3)
        (by omega) (by decide) (by omega) (by omega)).schedule := by
  rw [ladder]
  split <;> simp only [certifiedScheduleQueries_cast, scheduleQueries]

/-- Exact query ladders from the pinned production verifier, indexed by `r - 1` and `n - 15`. -/
def productionQueries : Fin 4 → Fin 14 → List ℕ :=
  ![![[222, 55], [223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22], [223, 56, 32, 22], [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17], [224, 56, 32, 23, 17], [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14]],
    ![[111, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20], [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13]],
    ![[75, 37], [75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13]],
    ![[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17], [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12]]]

/-- A reached production level's query count; levels beyond the ladder have no queries. -/
def productionQuery (r : Fin 4) (n : Fin 14) (level : ℕ) : ℕ :=
  (productionQueries r n).getD level 0

/-- The finite table has the same number of levels as the six-then-four folding ladder. -/
theorem productionQueries_length (r : Fin 4) (n : Fin 14) :
    (productionQueries r n).length = (n.val + 9 - 2) / 4 + 1 := by
  fin_cases r <;> fin_cases n <;> decide

/-- An in-range query lookup is exactly the corresponding tabulated entry. -/
theorem productionQuery_eq (r : Fin 4) (n : Fin 14) (level : ℕ)
    (h : level < (productionQueries r n).length) :
    productionQuery r n level = (productionQueries r n)[level] := by
  exact List.getD_eq_getElem _ _ h

/-- The checked production setup gives an initial encoded domain between ten and twenty-six bits. -/
theorem productionDomain_bounds (vars rate : ℕ)
    (hvars : 15 ≤ vars ∧ vars ≤ 28) (hrate : 1 ≤ rate ∧ rate ≤ 4) :
    10 ≤ vars - 6 + rate ∧ vars - 6 + rate ≤ 26 := by omega

/-- Production schedule at a checked initial inverse-rate exponent and stacked dimension. -/
def productionSchedule (choices : JohnsonChoices) (vars rate : ℕ)
    (hvars : 15 ≤ vars ∧ vars ≤ 28) (hrate : 1 ≤ rate ∧ rate ≤ 4) :
    CertifiedSchedule vars rate :=
  ladder choices (fun currentRate => productionQuery
    ⟨rate - 1, by omega⟩ ⟨vars - 15, by omega⟩ ((currentRate - rate) / 3))
    vars 6 rate (by omega) (by decide) (by omega)
      ((productionDomain_bounds vars rate hvars hrate).2.trans (by decide))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- Every reached schedule level consumes exactly the pinned production query table. -/
theorem productionSchedule_queries (choices : JohnsonChoices) (vars rate : ℕ)
    (hvars : 15 ≤ vars ∧ vars ≤ 28) (hrate : 1 ≤ rate ∧ rate ≤ 4) :
    scheduleQueries (productionSchedule choices vars rate hvars hrate).schedule =
      productionQueries ⟨rate - 1, by omega⟩ ⟨vars - 15, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n : Fin 14, vars = n.val + 15 := ⟨⟨vars - 15, by omega⟩, by change vars = (vars - 15) + 15; omega⟩
  obtain ⟨r, rfl⟩ : ∃ r : Fin 4, rate = r.val + 1 := ⟨⟨rate - 1, by omega⟩, by change rate = (rate - 1) + 1; omega⟩
  unfold productionSchedule
  fin_cases n <;> fin_cases r <;>
    simp only [ladder_scheduleQueries, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceDIte] <;>
    rfl

/-- The checked production schedule starts at the announced inverse-rate exponent. -/
theorem productionSchedule_headRate (choices : JohnsonChoices) (vars rate : ℕ)
    (hvars : 15 ≤ vars ∧ vars ≤ 28) (hrate : 1 ≤ rate ∧ rate ≤ 4) :
    scheduleRate (productionSchedule choices vars rate hvars hrate).schedule = rate :=
  (productionSchedule choices vars rate hvars hrate).headRate


end CompStark.Pcs
