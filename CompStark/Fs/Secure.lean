/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkBcs
public import CompStark.Fs.BatchBcs
public import CompStark.Sound.Calculator

/-! # The calculator's bound on Plonky3's duplex challenger

A duplex-challenger theorem bounds the verifier's failure by `chainError q + maxError · q +
sumError` of the node errors, each times its draw's ratio. Every such node error is one of the
calculator's round terms (`Setup.roundErrorTerms`): constraint folding at `α`, the grinding's
`powFraction` times the out-of-domain and batching terms, times FRI's largest fold at each fold
(`friRatio_mul_nodeErrors_le`, with the folds of Plonky3's schedule bounded by the plan's level
bounds, `foldErrorsLE_plonky3`), and at the queries
`powFraction · (1 - δ + #folds · loss + 1/p) ^ numQueries`, the query positions' slack `1/p`
inside the query error (`Setup.ratio_mul_nodeErrors_le`). So the
largest is at most the round error's bound, and a path of at most `maxChallenges` challenges sums
to at most `maxChallenges` times it. The calculator's certificate per oracle answer
(`Statement.SecureRo`) then bounds the STARK's knowledge soundness with Merkle commitments by
`chainError q + hashBadError + (q + maxChallenges) 2 ^ (-bits)`
(`Statement.knowledgeSoundness_bcs_of_secureRo`), which `Statement.bcsBound` evaluates with the
round error's bound in place of `2 ^ (-bits)`. The batch's nodes are the batch calculator's
round terms alike (`Batch.Setup.ratio_mul_nodeErrors_le`), the lookup challenges' with their
grinding, or without lookups LogUp's error `0` (`Batch.Setup.lookupError_eq_zero`), so the batch
calculator's certificate (`Batch.Statement.SecureRo`) bounds the batch STARK's knowledge soundness
with Merkle commitments by the same expression
(`Batch.Statement.knowledgeSoundness_bcs_of_secureRo`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Sound CompStark.Iop
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security.StateRestoration
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Every fold of a schedule from the domain `ω` has error at most `E`. -/
def foldErrorsLE (d : ℕ) (δ loss : ℝ) (E : ENNReal) :
    {n : ℕ} → Domain.SmoothCosetFftDomain n 𝕂 → Fri.Interaction.Schedule n → Prop
  | _, _, .final => True
  | _, ω, .fold k _ inject rest =>
      Fri.Interaction.Schedule.roundError ω k (rest.degree d) δ loss inject ≤ E ∧
        foldErrorsLE d δ loss E (ω.subdomain k) rest

/-- Fold errors at most `E` are at most any larger bound. -/
theorem foldErrorsLE_mono (d : ℕ) (δ loss : ℝ) {E E' : ENNReal} (hEE : E ≤ E') :
    ∀ {n : ℕ} (ω : Domain.SmoothCosetFftDomain n 𝕂) (s : Fri.Interaction.Schedule n),
      foldErrorsLE d δ loss E ω s → foldErrorsLE d δ loss E' ω s
  | _, _, .final, _ => trivial
  | _, _, .fold _ _ _ rest, h => ⟨h.1.trans hEE, foldErrorsLE_mono d δ loss hEE _ rest h.2⟩

/-- **FRI's node errors, each times its draw's ratio.** On a schedule whose folds have errors at
most `E`, every node of FRI's public coin is at most the larger of the folds' `E` times the commit
grinding's fraction and the query error times the query grinding's. -/
theorem friRatio_mul_nodeErrors_le (top d t commitBits queryBits : ℕ) (δ loss : ℝ)
    (slack E : ENNReal) :
    ∀ {n : ℕ} (ω : Domain.SmoothCosetFftDomain n 𝕂) (s : Fri.Interaction.Schedule n) (j : ℕ),
      foldErrorsLE d δ loss E ω s →
      ∀ node, friRatio (F := F) top d t commitBits queryBits s node *
          Fri.Interaction.nodeErrors top d t δ loss slack ω s j node ≤
        max (Iop.powFraction F commitBits * E) (Iop.powFraction F queryBits *
          (ENNReal.ofReal (Fri.Interaction.threshold δ loss (j + s.numFolds)) + slack) ^ t)
  | _, _, .final, j, _, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : (_ : Fin d → 𝕂) × (PUnit ⊕ (PUnit × Empty)))
    · exact le_max_right _ _
    · exact node.elim
  | n, ω, .fold k _ _ rest, j, h, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : Fri.Interaction.Word 𝕂 n × (PUnit ⊕ (PUnit ×
      Prefix PUnit (Fri.Interaction.publicCoin 𝕂 top d t rest))))
    · exact le_max_of_le_left (mul_le_mul_right h.1 _)
    · refine (friRatio_mul_nodeErrors_le top d t commitBits queryBits δ loss slack E
        (ω.subdomain k) rest (j + 1) h.2 node).trans (le_of_eq ?_)
      rw [Fri.Interaction.Schedule.numFolds, Nat.add_assoc, Nat.add_comm 1]

open FriGame in
/-- The folds of Plonky3's schedule at rate `1/c` (`c d = 2 ^ logFinal`) have errors at most the
largest bound `g` on the folds of its plan, over `|𝕂|`. -/
theorem foldErrorsLE_plonky3 (c : ℕ) (a : ℕ) (ha : 0 < a) (d logFinal : ℕ)
    (hd : c * d = 2 ^ logFinal) (δ loss : ℝ) (g : ℕ × ℕ × Bool → ℝ) :
    ∀ (fuel n : ℕ) (ω : Domain.SmoothCosetFftDomain n 𝕂) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Rounds.Fits logFinal n heights →
      FoldBounds 𝕂 c δ loss g (Rounds.plan a logFinal fuel n heights) →
      foldErrorsLE d δ loss
        (ENNReal.ofReal (planMax g (Rounds.plan a logFinal fuel n heights) / Fintype.card 𝕂)) ω
        (Fri.Interaction.Schedule.plonky3 a logFinal fuel n heights)
  | 0, _, _, _, _, _, _, _ => trivial
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, hg => by
    by_cases hfin : n ≤ logFinal
    · simp only [Fri.Interaction.Schedule.plonky3, ite_eq_left hfin]
      trivial
    have h1 := Rounds.one_le_logArity ha (by omega) hfit
    have h2 := Rounds.logArity_le a logFinal n heights
    have hK : (0 : ℝ) < Fintype.card 𝕂 := by exact_mod_cast Fintype.card_pos
    -- one fold onto `2 ^ (n - la)` points, and the rest
    have hstep (la : ℕ) (hla1 : 1 ≤ la) (hla2 : la ≤ n - logFinal) (hla : la ≤ n) (inj : Bool)
        (h : List ℕ) (hf : Rounds.Fits logFinal (n - la) h)
        (hg : FoldBounds 𝕂 c δ loss g
          ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h)) :
        foldErrorsLE d δ loss (ENNReal.ofReal (planMax g
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂)) ω
          (.fold la hla inj (Fri.Interaction.Schedule.plonky3 a logFinal fuel (n - la) h)) := by
      have hdeg : c * (Fri.Interaction.Schedule.plonky3 a logFinal fuel (n - la) h).degree d =
          2 ^ (n - la) := by
        rw [Fri.Interaction.Schedule.degree_plonky3 ha d fuel _ h (by omega) (by omega) hf,
          mul_left_comm, hd, ← pow_add]
        congr 1
        omega
      obtain ⟨hg0, hlevel⟩ := hg _ List.mem_cons_self
      have hle : ENNReal.ofReal (planMax g (Rounds.plan a logFinal fuel (n - la) h) /
          Fintype.card 𝕂) ≤ ENNReal.ofReal (planMax g
            ((la, n - la, inj) :: Rounds.plan a logFinal fuel (n - la) h) / Fintype.card 𝕂) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_right _ _) hK.le)
      refine ⟨?_, foldErrorsLE_mono d δ loss hle _ _ (foldErrorsLE_plonky3 c a ha d logFinal hd
        δ loss g fuel (n - la) (ω.subdomain la) h (by omega) (by omega) hf
        fun f hf ↦ hg f (List.mem_cons_of_mem _ hf))⟩
      refine le_trans ?_ (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (le_max_left _ _) hK.le))
      have hw := hlevel (ω.subdomain la : Fin (2 ^ (n - la)) ↪ 𝕂) _ hdeg
      cases inj
      · rw [foldWords_false] at hw
        exact hw
      · rw [foldWords_true] at hw
        exact hw
    simp only [Fri.Interaction.Schedule.plonky3, ite_eq_right hfin]
    match heights, hfit, h1, h2, hg with
    | [], hfit, h1, h2, hg =>
      simp only [Rounds.plan, ite_eq_right hfin] at hg ⊢
      exact hstep _ h1 h2 _ false [] (Rounds.fits_nil _ _) hg
    | m :: rest, hfit, h1, h2, hg =>
      have h3 := Rounds.logArity_le_cons a logFinal n m rest
      have hm' : (m = n - Fri.Interaction.Schedule.logArity a logFinal n (m :: rest)) =
          (m = n - Rounds.logArity a logFinal n (m :: rest)) := rfl
      by_cases hm : m = n - Rounds.logArity a logFinal n (m :: rest)
      · simp only [hm', ite_eq_left hm, Rounds.plan, ite_eq_right hfin] at hg ⊢
        exact hstep _ h1 h2 _ true rest (Rounds.fits_of_eq hfit hm) hg
      · simp only [hm', ite_eq_right hm, Rounds.plan, ite_eq_right hfin] at hg ⊢
        exact hstep _ h1 h2 _ false _ (Rounds.fits_cons_of_ne hfit h3 hm) hg

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security.StateRestoration
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-- FRI along Plonky3's schedule folds as many times as its plan has folds. -/
theorem numFolds_friSchedule {lookups : List (Lookup F)} (S : Setup EF lookups)
    (heights : List ℕ) :
    (S.friSchedule heights).numFolds = (S.friPlan heights).length := by
  rw [friSchedule, friPlan, ← FriGame.Rounds.numFolds_schedule _ _ (fun _ _ ↦ (0 : 𝕂))]
  exact ((foldError_schedule_eq S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
    1 0 0 (fun _ _ ↦ (0 : 𝕂)) _ _ S.friDomain heights).2.1).symm

/-- **The calculator bounds every node of the duplex-challenger theorem.** For `|F| = p` and an
analysis that fits the setup with an MCA bound that holds, every node error with the query
positions' slack `1/p`, times its draw's ratio, is at most the calculator's round error bound. -/
theorem ratio_mul_nodeErrors_le (S : Setup EF) (hp : Nat.card F = p) {B : McaBound}
    (hB : B.Holds) (A : Analysis) (hA : S.Fits B A) (δ δ' loss : ℝ≥0) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') (hloss : (loss : ℝ) = A.loss) (node : Prefix PUnit S.publicCoin) :
    S.ratio node * S.nodeErrors δ δ' loss (1 / Nat.card F) node ≤
      ENNReal.ofReal (S.roundErrorBound p B A : ℝ) := by
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p B A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  obtain ⟨_, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, node⟩⟩⟩⟩ := (node : S.TraceMessage × (PUnit ⊕
    (PUnit × (S.QuotientMessage × (PUnit ⊕ (PUnit × ((_ : Openings S) × (PUnit ⊕
      (PUnit × S.FriPrefix)))))))))
  · change 1 * foldingError S δ' ≤ _
    rw [one_mul]
    exact (foldingError_le_calc S A hp hA.1 δ' hδ').trans (hT (.head _))
  · exact (powFraction_mul_le_ofReal hp _ (outOfDomainError_le_calc S A hp hA.1 δ' hδ')).trans
      (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _
      (batchingErrorOf_le_calc S A hp B hB S.numOpened hA.1 hA.2.1 δ δ' hδ hδ')).trans
      (hT (.tail _ (.tail _ (.head _))))
  have hfin := S.valid.finalPolyFits
  have hfolds := foldErrorsLE_plonky3 (2 ^ S.params.logBlowup) S.params.maxLogArity S.valid.folds
    (2 ^ S.params.logFinalPolyLen) (S.params.logFinalPolyLen + S.params.logBlowup)
    (by rw [← pow_add, Nat.add_comm]) δ loss _ (S.logN + S.params.logBlowup)
    (S.logN + S.params.logBlowup) S.friDomain [] (by omega) (Nat.sub_le _ _)
    (FriGame.Rounds.fits_nil _ _) (foldBounds_calc A B hB _ hA.1 δ loss hδ hloss _ hA.2.2)
  refine (friRatio_mul_nodeErrors_le (F := F) (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.params.commitPowBits
    S.params.queryPowBits δ loss _ _ S.friDomain (S.friSchedule []) 0 hfolds node).trans
    (max_le ?_ ?_)
  · refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.head _)))))
    rw [← cast_maxQ_map, ofReal_div_card_eq' hp]
    rfl
  · have hq0 := queryDensity_nonneg S A hA.1 []
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [Rat.cast_pow, ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0)), Rat.cast_add,
      ENNReal.ofReal_add (Rat.cast_nonneg.mpr hq0) (Rat.cast_nonneg.mpr hp0)]
    congr 2
    · rw [Fri.Interaction.threshold, Nat.zero_add, numFolds_friSchedule, Iop.Setup.queryDensity,
        hδ, hloss]
      push_cast
      rfl
    · rw [hp, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
        ENNReal.ofReal_div_of_pos (by exact_mod_cast hp ▸ Nat.card_pos), ENNReal.ofReal_one,
        ENNReal.ofReal_natCast]

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.StateRestoration
open _root_.Interaction.Oracle.Security.HashChain
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

/-- **Knowledge soundness with Merkle commitments from the calculator.** If the calculator
certifies `bits` bits per oracle answer for the statement `C` at `A` with an MCA bound that holds
(`C.SecureRo EF p B A bits`), on a base field of at least `2 ^ 8` elements with two-adicity below
`2 ^ 64`, an adversary making at most `Q` duplex calls and `q` oracle calls in all gets Plonky3's
verifier to accept while no trace of the proof's length within `δ' = A.δ'` of the trace extracted
from the log under the proof's trace commitment satisfies the AIR with probability at most
`chainError Q' + hashBadError + (Q' + maxChallenges) 2 ^ (-bits)`,
`Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
theorem knowledgeSoundness_bcs_of_secureRo (C : Statement F) (hp : Nat.card F = p)
    {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : C.SecureRo EF p B A bits)
    (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64) {K : ℕ} (hK : 0 < K)
    (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ') (hA : A.Valid (1 / 2 ^ C.params.logBlowup))
    (adversary : OracleComp (spec F K) (List F × Proof F EF)) {Q q : ℕ}
    (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.starkGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits z.1.2.2.1.degreeBits,
        ∀ trace ∈ closeTraces (C.setupAt EF _ h) δ'
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.traceCommit)),
        ¬ C.air.Satisfied z.1.2.2.1.degreeBits trace z.1.2.1] ≤
      chainError (Digest F) (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K) +
        hashBadError F (2 ^ C.params.capHeight) (C.capOffsets EF).length
          (q + C.verifierQueries EF) +
        (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K + maxChallenges (F := F)) *
          (2 ^ bits)⁻¹ := by
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1
  have hloss : ((Real.toNNReal A.loss : ℝ≥0) : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hδ'r : ∀ n, C.Admits n → (δ' : ℝ) < 1 - C.rate := fun _ _ ↦ by
    obtain ⟨h0, -, hle, h1, hρ⟩ := hA
    have hq : A.δ' < 1 - 1 / 2 ^ C.params.logBlowup := by nlinarith
    have hr : ((A.δ' : ℚ) : ℝ) < ((1 - 1 / 2 ^ C.params.logBlowup : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    rw [hδ', Statement.rate]
    push_cast at hr
    exact hr
  have hnode (node : Prefix PUnit (C.publicCoin EF)) :
      C.ratio EF node * C.nodeErrors EF (fun _ ↦ Real.toNNReal A.δ) (fun _ ↦ δ')
        (fun _ ↦ Real.toNNReal A.loss) (1 / Nat.card F) node ≤ (2 ^ bits)⁻¹ := by
    have hb : C.admits node.1.1 = true := (C.admits_iff _).mpr node.1.2
    have hs := h node.1.1 (by have := node.1.2.sound.twoAdic; omega) hb
    exact ((C.setupOf EF node.1.1 hb).ratio_mul_nodeErrors_le hp hB A hs.1 _ _ _
      (coe_toNNReal_δ A hA) hδ' hloss node.2).trans (ofReal_le_inv_two_pow hs.2)
  refine (C.knowledgeSoundness_bcs EF K h8 h64 hK (fun _ ↦ Real.toNNReal A.δ) (fun _ ↦ δ') hδ'r
    (fun _ ↦ Real.toNNReal A.loss) adversary hQ hq).trans (add_le_add le_rfl ?_)
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [mul_comm]
    exact le_of_le_of_eq (mul_le_mul_right (iSup_le fun _ ↦ iSup_le hnode) _) (by push_cast; rfl)
  · exact iSup_le fun _ ↦ pathError_le_of_challengesLE (C.publicCoin EF)
      (N := maxChallenges (F := F)) (fun n ↦ (C.setup EF n).challengesLE_publicCoin) _ hnode

variable (EF) in
/-- The bound of `knowledgeSoundness_bcs_of_secureRo` for `|F| = p` at `Q` duplex calls and `q`
oracle calls with squeezes of `K` samples, the round error's bound in place of `2 ^ (-bits)`:
`chainError Q' + hashBadError + (Q' + maxChallenges) · roundErrorBound`,
`Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
def bcsBound (C : Statement F) (p K Q q : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  let Q' := Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K
  ((Q' * (Q' + 1) / 2 : ℕ) : ℚ) / (p : ℚ) ^ 8 +
    (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight : ℕ) *
      ((q + C.verifierQueries EF : ℕ) : ℚ) ^ 2 / (p : ℚ) ^ 8 +
    ((Q' + maxChallenges (F := F) : ℕ) : ℚ) * C.roundErrorBound EF p B A

end CompStark.Iop.Statement

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security.StateRestoration
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

/-- Without lookups, LogUp has no interactions and no error. -/
theorem lookupError_eq_zero (S : Setup EF) (hl : S.hasLookups = false) (δ : ℝ≥0) :
    S.lookupError δ = 0 := by
  have h0 : S.numInteractions = 0 := Finset.sum_eq_zero fun i _ ↦ by
    rw [Ni.lookups_eq_nil_of S hl i, List.map_nil, List.sum_nil, Nat.mul_zero]
  rw [lookupError, h0, Nat.zero_add, Nat.zero_sub, Nat.zero_mul, Nat.mul_zero, Nat.cast_zero,
    ENNReal.zero_div]

/-- **The calculator bounds every node of the batch's duplex-challenger theorem.** For `|F| = p`
and an analysis that fits the batch with an MCA bound that holds, every node error with the query
positions' slack `1/p`, times its draw's ratio, is at most the calculator's round error bound:
without lookups, the lookup challenges' ratio `|𝕂| ^ 2` meets LogUp's error `0`. -/
theorem ratio_mul_nodeErrors_le (S : Setup EF) (hp : Nat.card F = p) {B : McaBound}
    (hB : B.Holds) (A : Analysis) (hA : S.Fits B A) (δ δ' loss : ℝ≥0) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') (hloss : (loss : ℝ) = A.loss) (node : Prefix PUnit S.publicCoin) :
    S.ratio node * S.nodeErrors δ δ' loss (1 / Nat.card F) node ≤
      ENNReal.ofReal (S.roundErrorBound p B A : ℝ) := by
  have hT {x : String × ℚ} (h : x ∈ S.roundErrorTerms p B A) :
      ENNReal.ofReal (x.2 : ℝ) ≤ ENNReal.ofReal (S.roundErrorBound p B A : ℝ) :=
    ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (le_maxTerms h))
  have hi := instance_le_calc S B A hp hB hA δ δ' hδ hδ'
  obtain ⟨_, _ | ⟨_, _, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, node⟩⟩⟩⟩⟩ := (node : S.PrefixShape)
  · change lookupRatio F EF S.hasLookups S.params.lookupPowBits * S.lookupError δ' ≤ _
    cases hl : S.hasLookups
    · rw [S.lookupError_eq_zero hl, mul_zero]
      exact zero_le
    · exact (powFraction_mul_le_ofReal hp _ (lookupError_le_calc S B A hp hA δ' hδ')).trans
        (hT (.head _))
  · change 1 * (⨆ i, foldingError (S.instanceSetup i) δ') ≤ _
    rw [one_mul]
    exact (iSup_le fun i ↦ (hi i).1).trans (hT (.tail _ (.head _)))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.1)).trans
      (hT (.tail _ (.tail _ (.head _))))
  · exact (powFraction_mul_le_ofReal hp _ (iSup_le fun i ↦ (hi i).2.2)).trans
      (hT (.tail _ (.tail _ (.tail _ (.head _)))))
  have hfin : S.params.logFinalPolyLen ≤ S.logN S.top := S.domainSetup.valid.finalPolyFits
  have hfolds := foldErrorsLE_plonky3 (2 ^ S.params.logBlowup) S.params.maxLogArity
    S.domainSetup.valid.folds (2 ^ S.params.logFinalPolyLen)
    (S.params.logFinalPolyLen + S.params.logBlowup) (by rw [← pow_add, Nat.add_comm]) δ loss _
    (S.logN S.top + S.params.logBlowup) (S.logN S.top + S.params.logBlowup)
    S.domainSetup.friDomain S.friHeights (by omega) (Nat.sub_le _ _) (fits_friHeights S)
    (foldBounds_calc A B hB _ hA.1 δ loss hδ hloss _ hA.2.2)
  refine (friRatio_mul_nodeErrors_le (F := F) (S.logN S.top + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.params.commitPowBits
    S.params.queryPowBits δ loss _ _ S.domainSetup.friDomain
    (S.domainSetup.friSchedule S.friHeights) 0 hfolds node).trans (max_le ?_ ?_)
  · refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    rw [← cast_maxQ_map, ofReal_div_card_eq' hp]
    rfl
  · have hq0 := queryDensity_nonneg S.domainSetup A hA.1 S.friHeights
    have hp0 : (0 : ℚ) ≤ 1 / p := by positivity
    refine (powFraction_mul_le_ofReal hp _ (le_of_eq ?_)).trans
      (hT (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    rw [Rat.cast_pow, ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (add_nonneg hq0 hp0)), Rat.cast_add,
      ENNReal.ofReal_add (Rat.cast_nonneg.mpr hq0) (Rat.cast_nonneg.mpr hp0)]
    congr 2
    · rw [Fri.Interaction.threshold, Nat.zero_add, Iop.Setup.numFolds_friSchedule,
        Iop.Setup.queryDensity, hδ, hloss]
      push_cast
      rfl
    · rw [hp, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
        ENNReal.ofReal_div_of_pos (by exact_mod_cast hp ▸ Nat.card_pos), ENNReal.ofReal_one,
        ENNReal.ofReal_natCast]

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs CompStark.RandomOracle OracleComp OracleSpec
open _root_.Interaction.Oracle _root_.Interaction.Oracle.PublicCoin
open _root_.Interaction.Oracle.Security _root_.Interaction.Oracle.Security.StateRestoration
open _root_.Interaction.Oracle.Security.HashChain
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

/-- **Batch knowledge soundness with Merkle commitments from the calculator.** If the calculator
certifies `bits` bits per oracle answer for the batch statement `C` at `A` with an MCA bound that
holds (`C.SecureRo EF p B A bits`), an adversary making at most `Q` duplex calls and `q` oracle
calls in all gets Plonky3's batch verifier to accept while no tuple of traces of the proof's
lengths, each within `δ' = A.δ'` of the trace extracted from the log under the proof's main
commitment, satisfies the batch with probability at most
`chainError Q' + hashBadError + (Q' + maxChallenges) 2 ^ (-bits)`,
`Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
theorem knowledgeSoundness_bcs_of_secureRo (C : Statement F) (hp : Nat.card F = p)
    {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : C.SecureRo EF p B A bits)
    {K : ℕ} (hK : 0 < K) (δ' : ℝ≥0) (hδ' : (δ' : ℝ) = A.δ')
    (adversary : OracleComp (spec F K) ((Fin C.k → List F) × CompStark.Batch.BatchProof F EF))
    {Q q : ℕ} (hQ : IsQueryBoundP adversary (fun t => isDuplex t = true) Q)
    (hq : IsTotalQueryBound adversary q) :
    Pr{let z ← (simulateQ Bcs.realImpl
        (simulateQ translate (C.batchGame EF K adversary))).run []}[
      z.1.2.2.2 = .ok () ∧ ∀ h : C.Admits (C.lengthsOf z.1.2.2.1),
        ∀ traces ∈ closeTraces (C.setupAt EF _ h) δ'
          ((C.setupAt EF _ h).traceWords ((C.setupAt EF _ h).traceMessageOf
            (merkleCache (Bcs.hashCacheOf z.2)) z.1.2.2.1.mainCommit)),
        ¬ (C.setupAt EF _ h).Satisfied traces z.1.2.1] ≤
      chainError (Digest F) (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K) +
        hashBadError F (2 ^ C.params.capHeight) (C.capOffsets EF).length
          (q + C.verifierQueries EF) +
        (Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K + maxChallenges (F := F)) *
          (2 ^ bits)⁻¹ := by
  have hA := h.1.1
  have hl0 : (0 : ℝ) < A.loss := by exact_mod_cast hA.2.1
  have hloss : ((Real.toNNReal A.loss : ℝ≥0) : ℝ) = A.loss := Real.coe_toNNReal _ hl0.le
  have hnode (node : Prefix PUnit (C.publicCoin EF)) :
      C.ratio EF node * C.nodeErrors EF (fun _ ↦ Real.toNNReal A.δ) (fun _ ↦ δ')
        (fun _ ↦ Real.toNNReal A.loss) (1 / Nat.card F) node ≤ (2 ^ bits)⁻¹ := by
    have hs := C.secureRo_setupAt EF h node.1.1 node.1.2
    exact ((C.setup EF node.1).ratio_mul_nodeErrors_le hp hB A hs.1 _ _ _
      (coe_toNNReal_δ A hA) hδ' hloss node.2).trans (ofReal_le_inv_two_pow hs.2)
  refine (C.knowledgeSoundness_bcs EF K hK (fun _ ↦ Real.toNNReal A.δ) (fun _ ↦ δ')
    (fun n hn ↦ batch_lt_one_sub_rate (C.setupAt EF n hn) B A (C.secureRo_setupAt EF h n hn).1
      δ' hδ') (fun _ ↦ Real.toNNReal A.loss) adversary hQ hq).trans (add_le_add le_rfl ?_)
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [mul_comm]
    exact le_of_le_of_eq (mul_le_mul_right (iSup_le fun _ ↦ iSup_le hnode) _) (by push_cast; rfl)
  · exact iSup_le fun _ ↦ pathError_le_of_challengesLE (C.publicCoin EF)
      (N := maxChallenges (F := F)) (fun n ↦ (C.setup EF n).challengesLE_publicCoin) _ hnode

variable (EF) in
/-- The bound of `knowledgeSoundness_bcs_of_secureRo` for `|F| = p` at `Q` duplex calls and `q`
oracle calls with squeezes of `K` samples, the round error's bound in place of `2 ^ (-bits)`:
`chainError Q' + hashBadError + (Q' + maxChallenges) · roundErrorBound`,
`Q' = Q + verifierQueries + 3 verifierChainQueries`. -/
def bcsBound (C : Statement F) (p K Q q : ℕ) (B : McaBound) (A : Analysis) : ℚ :=
  let Q' := Q + C.verifierQueries EF + 3 * C.verifierChainQueries EF K
  ((Q' * (Q' + 1) / 2 : ℕ) : ℚ) / (p : ℚ) ^ 8 +
    (2 + (C.capOffsets EF).length * 2 ^ C.params.capHeight : ℕ) *
      ((q + C.verifierQueries EF : ℕ) : ℚ) ^ 2 / (p : ℚ) ^ 8 +
    ((Q' + maxChallenges (F := F) : ℕ) : ℚ) * C.roundErrorBound EF p B A

end CompStark.Iop.Batch.Statement
