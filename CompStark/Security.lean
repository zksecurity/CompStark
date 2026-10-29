/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.KoalaBear.Challenge
public import CompStark.NonInteractive
public import CompStark.Complete.Quotient
public import CompStark.BatchNonInteractive
public import CompStark.Sound.Calculator

/-! # Concrete security: 100 bits over the quartic extension, 117 with grinding, 128 over quintic

The security calculator (`CompStark/SecurityCalculator.lean`) bounds every error term of a setup
by a rational number computed from the setup's numbers, for a base field of `p` elements, at the
radii and the loss of an `Analysis`: FRI's proximity `δ`, the extractor's `δ'` and a proximity
loss. Whether the bound reaches `bits` bits, `S.Secure p A bits` (or `S.SecureRo p A bits` per
oracle answer), is decidable, and `decide +kernel` checks it, evaluating the AIR's constraints,
widths and lookups in the kernel. The theorems below turn a checked condition into the soundness
statements: `knowledgeSoundness_of_secure`, `knowledgeSoundness_ro_of_secureRo`,
`batchKnowledgeSoundness_of_secure` and `Batch.batchKnowledgeSoundness_ro_of_secureRo`, and their
error bounds. `knowledgeErrorReport` and `roundErrorReport` print the bits of each term (`#eval`).

Every analysis below is the one `bestAnalysis` (or `bestAnalysisRo`) finds for its setup
(`tests/CompStarkTests/Security.lean` checks this). FRI's radius `δ` stays below the
unique-decoding radius `(1 - rate) / 2`, and so does the extractor's `δ'`, where the candidate
lists have at most one element (`listSize_le_one`). Every term but the queries is over `|𝕂|`:
`p ^ 4 ≈ 2 ^ 123.95` for `KoalaBear.Fast.Ext4`, which caps every configuration below
`2 ^ (-123.95)` (constraint folding alone is about `2 ^ (-117.98)`), and `p ^ 5 ≈ 2 ^ 154.94` for
`KoalaBear.Fast.Ext5`. In the random-oracle model, grinding divides every round's error after `α`
by about `2 ^ bits`; only constraint folding, which Plonky3 does not grind, stays an integer over
`|𝕂|`, so the quartic extension is capped near `2 ^ (-117.98)` instead. All configurations fold
by arity `2` down to a constant; the calculator takes any arity (Plonky3's Keccak example, at
arity `8`, is in `tests/CompStarkTests/KeccakSecurity.lean`).

The bits of each term, `-log₂` of its bound, and the smallest query count reaching the claim at
the analysis the search finds:

* `fibonacciSetup`: the Fibonacci AIR (2 columns, 5 constraints, 1 quotient chunk) on `2 ^ 10`
  rows, blowup `16` (rate `1/16`), `110` queries; FRI at `δ = 15/32 - 2 ^ (-40)`, the extractor
  at `δ' = 15/32 - 2 ^ (-42)`. Constraint folding `121.95`, out of domain `109.71`, batching
  `107.15` (the powers MCA bound `(m - 1) N`), FRI's folds `109.96` (each at the powers MCA bound
  `|L'|`, which needs no loss), queries `100.38`: at most `2 ^ (-100)`
  (`fibonacci_knowledgeError_le`), `100.36` bits; `109` queries reach `99.46`.
* `wideSetup`: `wide 64` (64 columns, 64 constraints of degree `3`, 2 quotient chunks,
  `numOpened = 136`) on `2 ^ 20` rows, blowup `4`, `150` queries; FRI at `δ = 3/8 - 2 ^ (-12)`,
  the extractor at `δ' = 3/8 - 2 ^ (-14)`, `loss = 2 ^ (-17)`. Constraint folding `117.98`, out
  of domain `100.95`, batching `105.88`, FRI's folds `105.50` (the lossy bound on the `6` largest
  domains, `|L'|` on the smaller), queries `101.57`: `100.17` bits (`wide_knowledgeError_le`);
  `149` queries reach `99.87`. The out-of-domain term `(ℓ identityDegree + n + N) / |𝕂|` grows
  with the list size, so the extractor stays below the unique-decoding radius at this size.
* `wide21Setup`: `wide 64` on `2 ^ 21` rows with `wideParams` and the same analysis: out of
  domain `99.95`, batching `105.88`, FRI's folds `105.31`, queries `101.57`, `99.50` bits
  (`wide21_knowledgeError_le`); the out-of-domain term caps the quartic extension below `100`
  bits on `2 ^ 21` rows.
* `wideSp1Setup`, in the random-oracle model: `wide 64` on `2 ^ 21` rows with SP1's FRI
  (soundcalc's core circuit, `sp1Params`): blowup `4`, `124` queries, `16` bits of query
  grinding; `δ = 3/8 - 2 ^ (-14)`, `δ' = 3/8 - 2 ^ (-16)`, `loss = 2 ^ (-16)`. Constraint folding
  `117.98`, out of domain `99.95`, batching `103.88`, FRI's folds `109.37`, queries
  `powFraction 16 · (5/8 + …) ^ 124`, `99.97`: every round error is at most `2 ^ (-99)`
  (`wideSp1_roundError_le`), `99.95` bits, capped by the out-of-domain term; `123` queries reach
  `99.40`. At every trace length the verifier admits, up to `2 ^ 22` rows, the same analysis
  gives at least `98.95` bits (`wideSp1Statement_secureRo`, `98`), the out-of-domain term growing
  with the length; by `knowledgeSoundness_ro`, a prover making `Q` oracle calls gets a proof
  accepted that the extractor cannot open with probability at most
  `q · 2 ^ (-98) + 4 q² / |𝔽| ^ 8`, `q = Q + verifierQueries`, `verifierQueries = 87307` on proofs
  of any length (`wideSp1_knowledgeSoundness_ro`).
* `wideGrindSetup`, in the random-oracle model: `wide 64` on `2 ^ 21` rows over the quartic
  extension, blowup `4`, `144` queries, grinding `20` bits before `ζ`, `12` before the batching
  challenge, `8` per fold and `20` before the queries (`wideGrindParams`);
  `δ = 3/8 - 2 ^ (-11)`, `δ' = 3/8 - 2 ^ (-13)`, `loss = 2 ^ (-16)`. Constraint folding `117.98`,
  out of domain `119.95`, batching `118.87`, FRI's folds `117.37`, queries `117.37`: every round
  error is at most `2 ^ (-117)` (`wideGrind_roundError_le`), `117.37` bits; `143` queries reach
  `116.82`. Constraint folding, without grinding, keeps any configuration above `2 ^ (-117.98)`.
  The analysis reaches `117` bits at every admitted length (`wideGrindStatement_secureRo`);
  `verifierQueries = 101367` (`wideGrind_knowledgeSoundness_ro`).
* `wide5Setup`, in the random-oracle model over the quintic extension `KoalaBear.Fast.Ext5`:
  `wide 64` on `2 ^ 21` rows with zkDTVM's FRI (soundcalc's `zkdtvm_v080.toml`, `wide5Params`):
  blowup `4`, `160` queries, `20` bits of query grinding; `δ = 3/8 - 2 ^ (-20)`,
  `δ' = 3/8 - 2 ^ (-22)`, no loss needed. Constraint folding `148.97`, out of domain `130.94`,
  batching `128.85`, FRI's folds `132.94`, queries `128.49`: every round error is at most
  `2 ^ (-128)` (`wide5_roundError_le`); `159` queries reach `127.81`. The analysis reaches `128`
  bits at every admitted length (`wide5Statement_secureRo`); `verifierQueries = 112642`
  (`wide5_knowledgeSoundness_ro`).
* `wide5iSetup`, the interactive counterpart, without credit for grinding: `wide 64` on `2 ^ 21`
  rows over `KoalaBear.Fast.Ext5`, blowup `4`, `190` queries (`wide5iParams`);
  `δ = 3/8 - 2 ^ (-14)`, `δ' = 3/8 - 2 ^ (-16)`, `loss = 2 ^ (-19)`. Constraint folding `148.97`,
  out of domain `130.94`, batching `134.84`, FRI's folds `134.70`, queries `128.79`: `128.46` bits
  (`wide5i_knowledgeError_le`, `wide5i_knowledgeSoundness`); `189` queries reach `127.90`.
* `wideBatchSetup`: a batch of three `wideBus 64` instances on `2 ^ 20`, `2 ^ 19` and `2 ^ 16`
  rows over `KoalaBear.Fast.Ext5`, every row receiving four columns and sending four on one global
  bus (`wideBus`: `wide 64` and two interactions of width `W = 4` per row,
  `T = 2 (2 ^ 20 + 2 ^ 19 + 2 ^ 16) = 3276800` in all; its LogUp constraints keep the two quotient
  chunks, add `4` constraints of degree `3` and two permutation columns, `20` opened words over
  the quintic extension), with `wide5iParams` and `wide5iAnalysis`. The lookup challenges
  `T + (T - 1) W = 16383996` (`lookupError`), `130.98`; constraint folding `148.88`, out of domain
  `131.94` and batching `134.65`, each at the worst instance, batching the `158` opened words of
  each instance's domain size; FRI's folds from `2 ^ 22` points, injecting the shorter instances'
  words at `2 ^ 21` and `2 ^ 18` points, `134.48`; queries `128.79`: `128.34` bits
  (`wideBatch_knowledgeError_le`, `wideBatch_knowledgeSoundness`); `189` queries reach `127.81`.
  The batch pays for the lookups once, for `α`, `ζ` and batching once, as its failing instance
  would alone among the instances of its size; FRI pays one more word per injected height.
  Plonky3's `p3-security` estimates LogUp's error as `N (W + 2) / |𝕂|` for `N` interactions; the
  bound here, `(T + (T - 1) W) / |𝕂|`, is Schwartz–Zippel on the numerator with every denominator
  cleared, at most `(W + 1) T / |𝕂|`, the same up to `T / |𝕂|`, and it counts the poles of every
  tuple, whatever its multiplicity.
* `wideBatch5Setup`, the batch in the random-oracle model, with `wide5Params`;
  `δ = 3/8 - 2 ^ (-20)`, `δ' = 3/8 - 2 ^ (-22)`, no loss needed: the lookup challenges `130.98`,
  constraint folding `148.88`, out of domain `131.94`, batching `128.65`, FRI's folds `132.94`,
  queries `128.49`; every round error is at most `2 ^ (-128)` (`wideBatch5_roundError_le`),
  `verifierQueries = 99669` (`wideBatch5_knowledgeSoundness_ro`).
* `wideBatchGrindSetup`, the batch over the quartic extension with `wideBusGrindParams` (`144`
  queries, grinding in every round but `α`, `18` bits before the lookup challenges);
  `δ = 3/8 - 2 ^ (-12)`, `δ' = 3/8 - 2 ^ (-14)`, `loss = 2 ^ (-15)`: the lookup challenges
  `117.99` (`99.99` without grinding), constraint folding `117.89`, out of domain `120.95`,
  batching `117.71`, FRI's folds `117.37`, queries `117.36`; every round error is at most
  `2 ^ (-117)` (`wideBatchGrind_roundError_le`), `verifierQueries = 89692`
  (`wideBatchGrind_knowledgeSoundness_ro`). Constraint folding, which Plonky3 does not grind,
  keeps the quartic extension above `2 ^ (-117.89)`: `117` bits is the best integer level, reached
  with `18` bits of lookup grinding (`17` leave the lookup challenges at `2 ^ (-116.99)`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

/-! ### The calculator's theorems

Each takes the calculator's certificate with an MCA bound `B` and the hypothesis that `B` holds
(`B.Holds`): `McaBound.uniqueDecoding_holds` for the bound within the unique-decoding radius,
`McaBound.uniqueOrJohnson_holds` up to the Johnson radius. -/

section Calculator
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

/-- **The calculator's knowledge error.** If the calculator certifies `bits` bits for `S` at the
analysis `A` with an MCA bound `B` that holds (`S.Secure p B A bits`, for `|F| = p`), the
knowledge error with FRI at `A.δ` and the extractor at `A.δ'` is at most `2 ^ (-bits)`. -/
theorem knowledgeError_le_of_secure {lookups : List (Lookup F)} (S : Setup EF lookups)
    (hp : Nat.card F = p) {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ}
    (h : S.Secure p B A bits) (δ δ' : NNReal) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    knowledgeError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (knowledgeError_le_bound S A hp B hB h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Knowledge soundness from the calculator.** If the calculator certifies `bits` bits for `S`
at `A` with an MCA bound that holds, and no trace within `δ' = A.δ'` of the prover's committed
trace satisfies the AIR, the verifier accepts with probability at most `2 ^ (-bits)`. -/
theorem knowledgeSoundness_of_secure (S : Setup EF) [S.Folds] (hp : Nat.card F = p)
    {B : McaBound}
    (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : S.Secure p B A bits) (δ' : NNReal)
    (hδ' : (δ' : ℝ) = A.δ') (publicValues : List F) (prover : Prover S) :
    (∀ trace ∈ closeTraces S δ' prover.trace, ¬ S.air.Satisfied S.logN trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ bits)⁻¹ := fun hfar ↦
  (knowledgeSoundness S publicValues prover _ δ' (lt_one_sub_rate S A h.1.1 δ' hδ')
    hfar).trans (knowledgeError_le_of_secure S hp hB A h _ δ' (coe_toNNReal_δ A h.1.1) hδ')

/-- **The calculator's round error.** If the calculator certifies `bits` bits per oracle answer
for `S` at `A` with an MCA bound `B` that holds (`S.SecureRo p B A bits`), the round error with
FRI at `A.δ` and the extractor at `A.δ'` is at most `2 ^ (-bits)`. -/
theorem roundError_le_of_secureRo (S : Setup EF) [S.Folds] (hp : Nat.card F = p)
    {B : McaBound}
    (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : S.SecureRo p B A bits) (δ δ' : NNReal)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    roundError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (roundError_le_bound A S hp B hB h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **The calculator's round error of a statement.** If the calculator certifies `bits` bits per
oracle answer for the statement `C` at `A` with an MCA bound `B` that holds
(`C.SecureRo p B A bits`), the round error with FRI at `A.δ` and the extractor at `A.δ'` at every
length is at most `2 ^ (-bits)`. -/
theorem Statement.roundError_le_of_secureRo (C : Statement F) (hp : Nat.card F = p)
    {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : C.SecureRo EF p B A bits)
    (δ δ' : NNReal) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    C.roundError EF (fun _ ↦ δ) (fun _ ↦ δ') ≤ (2 ^ bits)⁻¹ := by
  refine iSup_le fun n ↦ iSup_le fun hn ↦ ?_
  have hb : C.admits n = true := (C.admits_iff n).mpr hn
  have hs := h n (by have := hn.sound.twoAdic; omega) hb
  unfold Setup.lengthError
  split
  · rename_i hf
    have : (C.setupOf EF n hb).Folds := ⟨hf⟩
    exact _root_.CompStark.Iop.roundError_le_of_secureRo (C.setupOf EF n hb) hp hB A hs δ δ' hδ
      hδ'
  · exact (roundError0_le_bound A (C.setupOf EF n hb) hp B hB hs.1 δ δ' hδ hδ').trans
      (ofReal_le_inv_two_pow hs.2)

/-- **Knowledge soundness in the random-oracle model from the calculator.** If the calculator
certifies `bits` bits per oracle answer for the statement `C` at `A` with an MCA bound that holds,
on a base field of at least `2 ^ 8` elements with two-adicity below `2 ^ 64`, a prover making at
most `Q` oracle calls gets a proof accepted while no trace of its length within `δ' = A.δ'` of the
one it committed to satisfies the AIR, with probability at most `q · 2 ^ (-bits) + hashError q`,
`q = Q + verifierQueries`. -/
theorem knowledgeSoundness_ro_of_secureRo (C : Statement F) (hp : Nat.card F = p)
    {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : C.SecureRo EF p B A bits)
    (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64) (δ' : NNReal)
    (hδ' : (δ' : ℝ) = A.δ') (hA : A.Valid (1 / 2 ^ C.params.logBlowup)) (publicValues : List F)
    (Q : Nat) (prover : C.NIProver EF) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← C.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : C.Admits proof.degreeBits,
          ∀ trace ∈ closeTraces (C.setupAt EF _ h) δ'
              (committedTrace (C.setupAt EF _ h) log proof),
            ¬ C.air.Satisfied proof.degreeBits trace publicValues] ≤
      (Q + C.verifierQueries EF) * (2 ^ bits)⁻¹ +
        hashError F (C.params.capHeight + 1) (Q + C.verifierQueries EF) := by
  refine (knowledgeSoundness_ro C publicValues h8 h64 (fun _ ↦ Real.toNNReal A.δ) (fun _ ↦ δ')
    (fun n hn ↦ ?_) Q prover hQ).trans ?_
  · obtain ⟨h0, -, hle, h1, hρ⟩ := hA
    have hq : A.δ' < 1 - 1 / 2 ^ C.params.logBlowup := by nlinarith
    have hr : ((A.δ' : ℚ) : ℝ) < ((1 - 1 / 2 ^ C.params.logBlowup : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    rw [hδ', Statement.rate]
    push_cast at hr
    exact hr
  · gcongr
    exact C.roundError_le_of_secureRo hp hB A h _ δ' (coe_toNNReal_δ A hA) hδ'

/-- **The calculator's batch knowledge error.** If the calculator certifies `bits` bits for the
batch `S` at `A` with an MCA bound that holds, its knowledge error with FRI at `A.δ` and the
extractor at `A.δ'` is at most `2 ^ (-bits)`. -/
theorem Batch.knowledgeError_le_of_secure {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ}
    (h : S.Secure p B A bits) (δ δ' : NNReal) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.knowledgeError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (batchKnowledgeError_le_bound S B A hp hB h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Batch knowledge soundness from the calculator.** If the calculator certifies `bits` bits
for the batch `S` at `A` with an MCA bound that holds, and no tuple of traces, each within
`δ' = A.δ'` of its instance's committed trace, satisfies the batch, the verifier accepts with
probability at most `2 ^ (-bits)`. -/
theorem batchKnowledgeSoundness_of_secure {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ}
    (h : S.Secure p B A bits) (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ')
    (publicValues : Fin S.k → List F) (prover : Batch.Prover S) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace, ¬ S.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ (2 ^ bits)⁻¹ := fun hfar ↦
  (batchKnowledgeSoundness S publicValues prover _ δ' (batch_lt_one_sub_rate S B A h.1 δ' hδ')
    hfar).trans (Batch.knowledgeError_le_of_secure S hp hB A h _ δ' (coe_toNNReal_δ A h.1.1) hδ')

/-- **The calculator's batch round error.** If the calculator certifies `bits` bits per oracle
answer for the batch `S` at `A` with an MCA bound that holds, its round error with FRI at `A.δ`
and the extractor at `A.δ'` is at most `2 ^ (-bits)`. -/
theorem Batch.roundError_le_of_secureRo {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ}
    (h : S.SecureRo p B A bits) (δ δ' : NNReal) (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.roundError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (batchRoundError_le_bound S B A hp hB h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Batch knowledge soundness in the random-oracle model from the calculator.** If the
calculator certifies `bits` bits per oracle answer for the batch `S` at `A` with an MCA bound that
holds, a prover making at most `Q` oracle calls gets a proof accepted while no tuple of traces
within `δ' = A.δ'` of the ones it committed to satisfies the batch with probability at most
`q · 2 ^ (-bits) + hashError q`, `q = Q + verifierQueries`. -/
theorem Batch.batchKnowledgeSoundness_ro_of_secureRo (S : Batch.Setup EF) [S.CapFits]
    (hp : Nat.card F = p)
    {B : McaBound} (hB : B.Holds) (A : Analysis) {bits : ℕ} (h : S.SecureRo p B A bits)
    (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ') (publicValues : Fin S.k → List F) (Q : Nat)
    (prover : Batch.NIProver S) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ Batch.closeTraces S δ' (Batch.committedTraces S log proof),
          ¬ S.Satisfied traces publicValues] ≤
      (Q + S.verifierQueries) * (2 ^ bits)⁻¹ +
        hashError F S.params.capHeight (Q + S.verifierQueries) := by
  refine (Batch.batchKnowledgeSoundness_ro S publicValues (Real.toNNReal A.δ) δ'
    (batch_lt_one_sub_rate S B A h.1 δ' hδ') Q prover hQ).trans ?_
  gcongr
  exact Batch.roundError_le_of_secureRo S hp hB A h _ δ' (coe_toNNReal_δ A h.1.1) hδ'

end Calculator

/-! ### Examples -/

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize
local notation "Ext4" => KoalaBear.Fast.Ext4
local notation "Ext5" => KoalaBear.Fast.Ext5

/-- FRI with blowup `16`, folding by arity `2` down to a constant, and `110` queries. -/
def fibonacciParams : Fri.Params where
  logBlowup := 4
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 110
  commitPowBits := 0
  queryPowBits := 0

/-- The Fibonacci AIR on `2 ^ 10` rows with `fibonacciParams`. -/
def fibonacciSetup : Setup KoalaBear.Fast.Ext4 where
  params := fibonacciParams
  air := fibonacci
  logN := 10
  valid := ValidConfig.sound
    { colsInWidth := by unfold Air.ColsInWidth; decide
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := fibonacci_degreeFits 10
      twoAdic := by decide
      chunksFit := by
        rw [logQuotientChunks_of _ _ 0 rfl (by decide)]
        exact Nat.zero_le _
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }

instance : fibonacciSetup.Folds := ⟨by decide⟩

/-- FRI at `δ = 15/32 - 2 ^ (-40)`, the extractor at `δ' = 15/32 - 2 ^ (-42)`, below the
unique-decoding radius `15/32`, and `loss = 2 ^ (-60)`. -/
def fibonacciAnalysis : Analysis := ⟨15 / 32 - 1 / 2 ^ 40, 15 / 32 - 1 / 2 ^ 42, 1 / 2 ^ 60⟩

theorem fibonacci_secure :
    fibonacciSetup.Secure 2130706433 .uniqueDecoding fibonacciAnalysis 100 := by
  decide +kernel

/-- **100 bits.** The knowledge error of `fibonacciSetup`, FRI at `δ = 15/32 - 2 ^ (-40)` and the
extractor at `δ' = 15/32 - 2 ^ (-42)`, is at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeError_le :
    knowledgeError fibonacciSetup (15 / 32 - 2 ^ (-40 : ℤ)) (15 / 32 - 2 ^ (-42 : ℤ)) ≤
      (2 ^ 100)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ fibonacci_secure
    _ _ (by rw [coe_sub_two_zpow _ (-40) 40 rfl (by norm_num)]; norm_num [fibonacciAnalysis])
    (by rw [coe_sub_two_zpow _ (-42) 42 rfl (by norm_num)]; norm_num [fibonacciAnalysis])

/-- Knowledge soundness of `fibonacciSetup` with error `2 ^ (-100)`, the extractor at
`15/32 - 2 ^ (-42)`: if no trace within `15/32 - 2 ^ (-42)` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeSoundness (publicValues : List F) (prover : Prover fibonacciSetup) :
    (∀ trace ∈ closeTraces fibonacciSetup (15 / 32 - 2 ^ (-42 : ℤ) : NNReal) prover.trace,
      ¬ fibonacci.Satisfied 10 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ fibonacci_secure
    _ (by rw [coe_sub_two_zpow _ (-42) 42 rfl (by norm_num)]; norm_num [fibonacciAnalysis])
    publicValues prover

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `150` queries. -/
def wideParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 150
  commitPowBits := 0
  queryPowBits := 0

/-- The wide AIR reads only its columns. -/
theorem wide_colsInWidth (w : Nat) : (wide w : Air F).ColsInWidth := by
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.colsBelow, Bool.true_and,
    Bool.and_self, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hj, Nat.mod_lt _ (by omega)⟩, hj⟩

/-- `wide w` on `2 ^ logN` rows with FRI parameters of blowup `4` and a constant final
polynomial, for `logN ≤ 22`. -/
theorem wide_valid (P : Fri.Params) (hb : P.logBlowup = 2) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (w : ℕ) (hw : 0 < w) (logN : ℕ)
    (h : logN ≤ 22) : ValidConfig P (wide w : Air F) logN where
  colsInWidth := wide_colsInWidth w
  preprocessedSize := by simp only [wide, Array.size_empty, Nat.mul_zero]
  periodicFits := rfl
  degreeFits := wide_degreeFits w logN
  twoAdic := by
    rw [hb]
    change logN + 2 ≤ 24
    omega
  chunksFit := by
    rw [wide_logQuotientChunks w _ hw, hb]
    decide
  folds := ha
  finalPolyFits := by rw [hf]; exact Nat.zero_le _
  queries := hq
  blowup := by rw [hb]; decide

/-- `wide 64` on `2 ^ 20` rows with `wideParams`. -/
def wideSetup : Setup KoalaBear.Fast.Ext4 where
  params := wideParams
  air := wide 64
  logN := 20
  valid := ValidConfig.sound <|
    wide_valid wideParams rfl (by decide) rfl (by decide) 64 (by decide) 20 (by decide)

instance : wideSetup.Folds := ⟨by decide⟩

/-- FRI at `δ = 1535/4096 = 3/8 - 2 ^ (-12)`, the extractor at
`δ' = 6143/16384 = 3/8 - 2 ^ (-14)` and `loss = 2 ^ (-17)`. -/
def wideAnalysis : Analysis := ⟨1535 / 4096, 6143 / 16384, 1 / 2 ^ 17⟩

theorem wide_secure : wideSetup.Secure 2130706433 .uniqueDecoding wideAnalysis 100 := by
  decide +kernel

/-- **100 bits on `2 ^ 20` rows.** The knowledge error of `wideSetup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 6143/16384 = 3/8 - 2 ^ (-14)`, is at
most `2 ^ (-100)`. -/
theorem wide_knowledgeError_le :
    knowledgeError wideSetup (1535 / 4096) (6143 / 16384) ≤ (2 ^ 100)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide_secure _ _
    (by norm_num [wideAnalysis]) (by norm_num [wideAnalysis])

/-- Knowledge soundness of `wideSetup` with error `2 ^ (-100)`, the extractor at `6143/16384`:
if no trace within `6143/16384` of the prover's committed trace satisfies the AIR, the verifier
accepts with probability at most `2 ^ (-100)`. -/
theorem wide_knowledgeSoundness (publicValues : List F) (prover : Prover wideSetup) :
    (∀ trace ∈ closeTraces wideSetup (6143 / 16384 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 20 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide_secure _
    (by norm_num [wideAnalysis]) publicValues prover

/-- `wide 64` on `2 ^ 21` rows with `wideParams`. -/
def wide21Setup : Setup KoalaBear.Fast.Ext4 where
  params := wideParams
  air := wide 64
  logN := 21
  valid := ValidConfig.sound <|
    wide_valid wideParams rfl (by decide) rfl (by decide) 64 (by decide) 21 (by decide)

instance : wide21Setup.Folds := ⟨by decide⟩

/-- FRI at `δ = 1535/4096 = 3/8 - 2 ^ (-12)`, the extractor at
`δ' = 6143/16384 = 3/8 - 2 ^ (-14)` and `loss = 2 ^ (-17)`. -/
def wide21Analysis : Analysis := ⟨1535 / 4096, 6143 / 16384, 1 / 2 ^ 17⟩

theorem wide21_secure : wide21Setup.Secure 2130706433 .uniqueDecoding wide21Analysis 99 := by
  decide +kernel

/-- **99 bits on `2 ^ 21` rows.** The knowledge error of `wide21Setup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 6143/16384 = 3/8 - 2 ^ (-14)`, is at
most `2 ^ (-99)`. -/
theorem wide21_knowledgeError_le :
    knowledgeError wide21Setup (1535 / 4096) (6143 / 16384) ≤ (2 ^ 99)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide21_secure _ _
    (by norm_num [wide21Analysis]) (by norm_num [wide21Analysis])

/-- Knowledge soundness of `wide21Setup` with error `2 ^ (-99)`, the extractor at `6143/16384`:
if no trace within `6143/16384` of the prover's committed trace satisfies the AIR, the verifier
accepts with probability at most `2 ^ (-99)`. -/
theorem wide21_knowledgeSoundness (publicValues : List F) (prover : Prover wide21Setup) :
    (∀ trace ∈ closeTraces wide21Setup (6143 / 16384 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 99)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide21_secure _
    (by norm_num [wide21Analysis]) publicValues prover

/-- SP1's FRI parameters (soundcalc's `sp1.toml`, core circuit): blowup `4`, folding by arity `2`
down to a constant (soundcalc's early-stop degree `4` is the final domain's size), `124` queries
with `16` bits of query grinding. -/
def sp1Params : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 124
  commitPowBits := 0
  queryPowBits := 16

/-- `wide 64` on `2 ^ 21` rows with `sp1Params`: SP1's FRI on `2 ^ 21` rows. -/
def wideSp1Setup : Setup KoalaBear.Fast.Ext4 where
  params := sp1Params
  air := wide 64
  logN := 21
  valid := ValidConfig.sound <|
    wide_valid sp1Params rfl (by decide) rfl (by decide) 64 (by decide) 21 (by decide)

instance : wideSp1Setup.Folds := ⟨by decide⟩


/-- FRI at `δ = 3/8 - 2 ^ (-14)`, the extractor at `δ' = 3/8 - 2 ^ (-16)` and
`loss = 2 ^ (-16)`. -/
def wideSp1Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 14, 3 / 8 - 1 / 2 ^ 16, 1 / 2 ^ 16⟩

theorem wideSp1_secureRo :
    wideSp1Setup.SecureRo 2130706433 .uniqueDecoding wideSp1Analysis 99 := by
  decide +kernel

/-- **99 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wideSp1Setup`, FRI at
`δ = 3/8 - 2 ^ (-14)` and the extractor at `δ' = 3/8 - 2 ^ (-16)`, is at most `2 ^ (-99)`. -/
theorem wideSp1_roundError_le :
    roundError wideSp1Setup (3 / 8 - 2 ^ (-14 : ℤ)) (3 / 8 - 2 ^ (-16 : ℤ)) ≤ (2 ^ 99)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wideSp1_secureRo _ _
    (by rw [coe_sub_two_zpow _ (-14) 14 rfl (by norm_num)]; norm_num [wideSp1Analysis])
    (by rw [coe_sub_two_zpow _ (-16) 16 rfl (by norm_num)]; norm_num [wideSp1Analysis])

/-- `wide 64` with `sp1Params` at every trace length. -/
def wideSp1Statement : Statement F := ⟨sp1Params, wide 64, wide_colsInWidth 64⟩

/-- The oracle calls of the verifier on `wideSp1Statement`'s proofs, of any length. -/
theorem wideSp1Statement_verifierQueries : wideSp1Statement.verifierQueries Ext4 = 87307 := by
  decide +kernel

theorem wideSp1Statement_secureRo :
    wideSp1Statement.SecureRo Ext4 2130706433 .uniqueDecoding wideSp1Analysis 98 := by
  decide +kernel

/-- **98 bits per oracle call at every trace length.** A prover for `wideSp1Statement` making at
most `Q` oracle calls gets a proof accepted while no trace of its length
within `3/8 - 2 ^ (-16)` of the one it committed to satisfies the AIR, with probability at most
`q · 2 ^ (-98) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideSp1_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : wideSp1Statement.NIProver Ext4) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← wideSp1Statement.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : wideSp1Statement.Admits proof.degreeBits,
          ∀ trace ∈ closeTraces (wideSp1Statement.setupAt Ext4 _ h)
              (3 / 8 - 2 ^ (-16 : ℤ) : NNReal)
              (committedTrace (wideSp1Statement.setupAt Ext4 _ h) log proof),
            ¬ (wide 64 : Air F).Satisfied proof.degreeBits trace publicValues] ≤
      (Q + wideSp1Statement.verifierQueries Ext4) * (2 ^ 98)⁻¹ +
        hashError F 1 (Q + wideSp1Statement.verifierQueries Ext4) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds
    wideSp1Analysis
    wideSp1Statement_secureRo (by rw [KoalaBear.card_eq]; norm_num) (by decide) _
    (by rw [coe_sub_two_zpow _ (-16) 16 rfl (by norm_num)]; norm_num [wideSp1Analysis])
    (by decide +kernel) publicValues Q prover hQ

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `144` queries, with grinding
in every round after `α`: `20` bits before `ζ`, `12` before the batching challenge, `8` per fold
and `20` before the queries. -/
def wideGrindParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 144
  commitPowBits := 8
  queryPowBits := 20
  batchPowBits := 12
  oodPowBits := 20

/-- `wide 64` on `2 ^ 21` rows over the quartic extension with `wideGrindParams`. -/
def wideGrindSetup : Setup KoalaBear.Fast.Ext4 where
  params := wideGrindParams
  air := wide 64
  logN := 21
  valid := ValidConfig.sound <|
    wide_valid wideGrindParams rfl (by decide) rfl (by decide) 64 (by decide) 21 (by decide)

instance : wideGrindSetup.Folds := ⟨by decide⟩


/-- FRI at `δ = 3/8 - 2 ^ (-11)`, the extractor at `δ' = 3/8 - 2 ^ (-13)` and
`loss = 2 ^ (-16)`. -/
def wideGrindAnalysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 11, 3 / 8 - 1 / 2 ^ 13, 1 / 2 ^ 16⟩

theorem wideGrind_secureRo :
    wideGrindSetup.SecureRo 2130706433 .uniqueDecoding wideGrindAnalysis 117 := by
  decide +kernel

/-- **117 bits per oracle answer on `2 ^ 21` rows over the quartic extension.** Every round error
of `wideGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-11)` and the extractor at `δ' = 3/8 - 2 ^ (-13)`, is
at most `2 ^ (-117)`. -/
theorem wideGrind_roundError_le :
    roundError wideGrindSetup (3 / 8 - 2 ^ (-11 : ℤ)) (3 / 8 - 2 ^ (-13 : ℤ)) ≤ (2 ^ 117)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wideGrind_secureRo
    _ _ (by rw [coe_sub_two_zpow _ (-11) 11 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    (by rw [coe_sub_two_zpow _ (-13) 13 rfl (by norm_num)]; norm_num [wideGrindAnalysis])

/-- `wide 64` with `wideGrindParams` at every trace length. -/
def wideGrindStatement : Statement F := ⟨wideGrindParams, wide 64, wide_colsInWidth 64⟩

/-- The oracle calls of the verifier on `wideGrindStatement`'s proofs, of any length. -/
theorem wideGrindStatement_verifierQueries : wideGrindStatement.verifierQueries Ext4 = 101367 := by
  decide +kernel

theorem wideGrindStatement_secureRo :
    wideGrindStatement.SecureRo Ext4 2130706433 .uniqueDecoding wideGrindAnalysis 117 := by
  decide +kernel

/-- **117 bits per oracle call at every trace length.** A prover for `wideGrindStatement` making at
most `Q` oracle calls gets a proof accepted while no trace of its length
within `3/8 - 2 ^ (-13)` of the one it committed to satisfies the AIR, with probability at most
`q · 2 ^ (-117) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideGrind_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : wideGrindStatement.NIProver Ext4) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← wideGrindStatement.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : wideGrindStatement.Admits proof.degreeBits,
          ∀ trace ∈ closeTraces (wideGrindStatement.setupAt Ext4 _ h)
              (3 / 8 - 2 ^ (-13 : ℤ) : NNReal)
              (committedTrace (wideGrindStatement.setupAt Ext4 _ h) log proof),
            ¬ (wide 64 : Air F).Satisfied proof.degreeBits trace publicValues] ≤
      (Q + wideGrindStatement.verifierQueries Ext4) * (2 ^ 117)⁻¹ +
        hashError F 1 (Q + wideGrindStatement.verifierQueries Ext4) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds
    wideGrindAnalysis
    wideGrindStatement_secureRo (by rw [KoalaBear.card_eq]; norm_num) (by decide) _
    (by rw [coe_sub_two_zpow _ (-13) 13 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    (by decide +kernel) publicValues Q prover hQ

/-- zkDTVM's FRI parameters (soundcalc's `zkdtvm_v080.toml`, compress circuit): blowup `4`, folding
by arity `2` down to a constant, `160` queries with `20` bits of query grinding. -/
def wide5Params : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 160
  commitPowBits := 0
  queryPowBits := 20

/-- `wide 64` on `2 ^ 21` rows over the quintic extension with `wide5Params`. -/
def wide5Setup : Setup KoalaBear.Fast.Ext5 where
  params := wide5Params
  air := wide 64
  logN := 21
  valid := ValidConfig.sound <|
    wide_valid wide5Params rfl (by decide) rfl (by decide) 64 (by decide) 21 (by decide)

instance : wide5Setup.Folds := ⟨by decide⟩


/-- FRI at `δ = 3/8 - 2 ^ (-20)`, the extractor at `δ' = 3/8 - 2 ^ (-22)` and
`loss = 2 ^ (-60)`. -/
def wide5Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 20, 3 / 8 - 1 / 2 ^ 22, 1 / 2 ^ 60⟩

theorem wide5_secureRo : wide5Setup.SecureRo 2130706433 .uniqueDecoding wide5Analysis 128 := by
  decide +kernel

/-- **128 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wide5Setup`, FRI at
`δ = 3/8 - 2 ^ (-20)` and the extractor at `δ' = 3/8 - 2 ^ (-22)`, is at most `2 ^ (-128)`. -/
theorem wide5_roundError_le :
    roundError wide5Setup (3 / 8 - 2 ^ (-20 : ℤ)) (3 / 8 - 2 ^ (-22 : ℤ)) ≤ (2 ^ 128)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide5_secureRo _ _
    (by rw [coe_sub_two_zpow _ (-20) 20 rfl (by norm_num)]; norm_num [wide5Analysis])
    (by rw [coe_sub_two_zpow _ (-22) 22 rfl (by norm_num)]; norm_num [wide5Analysis])

/-- `wide 64` with `wide5Params` at every trace length. -/
def wide5Statement : Statement F := ⟨wide5Params, wide 64, wide_colsInWidth 64⟩

/-- The oracle calls of the verifier on `wide5Statement`'s proofs, of any length. -/
theorem wide5Statement_verifierQueries : wide5Statement.verifierQueries Ext5 = 112642 := by
  decide +kernel

theorem wide5Statement_secureRo :
    wide5Statement.SecureRo Ext5 2130706433 .uniqueDecoding wide5Analysis 128 := by
  decide +kernel

/-- **128 bits per oracle call at every trace length.** A prover for `wide5Statement` making at
most `Q` oracle calls gets a proof accepted while no trace of its length
within `3/8 - 2 ^ (-22)` of the one it committed to satisfies the AIR, with probability at most
`q · 2 ^ (-128) + hashError q`, `q = Q + verifierQueries`. -/
theorem wide5_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : wide5Statement.NIProver Ext5) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← wide5Statement.run publicValues prover}[
      verdict = .ok () ∧
        ∀ h : wide5Statement.Admits proof.degreeBits,
          ∀ trace ∈ closeTraces (wide5Statement.setupAt Ext5 _ h)
              (3 / 8 - 2 ^ (-22 : ℤ) : NNReal)
              (committedTrace (wide5Statement.setupAt Ext5 _ h) log proof),
            ¬ (wide 64 : Air F).Satisfied proof.degreeBits trace publicValues] ≤
      (Q + wide5Statement.verifierQueries Ext5) * (2 ^ 128)⁻¹ +
        hashError F 1 (Q + wide5Statement.verifierQueries Ext5) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds
    wide5Analysis
    wide5Statement_secureRo (by rw [KoalaBear.card_eq]; norm_num) (by decide) _
    (by rw [coe_sub_two_zpow _ (-22) 22 rfl (by norm_num)]; norm_num [wide5Analysis])
    (by decide +kernel) publicValues Q prover hQ

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `190` queries without
grinding. -/
def wide5iParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 190
  commitPowBits := 0
  queryPowBits := 0

/-- `wide 64` on `2 ^ 21` rows over the quintic extension with `wide5iParams`. -/
def wide5iSetup : Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  air := wide 64
  logN := 21
  valid := ValidConfig.sound <|
    wide_valid wide5iParams rfl (by decide) rfl (by decide) 64 (by decide) 21 (by decide)

instance : wide5iSetup.Folds := ⟨by decide⟩

/-- FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)`, the extractor at
`δ' = 24575/65536 = 3/8 - 2 ^ (-16)` and `loss = 2 ^ (-19)`. -/
def wide5iAnalysis : Analysis := ⟨6143 / 16384, 24575 / 65536, 1 / 2 ^ 19⟩

theorem wide5i_secure : wide5iSetup.Secure 2130706433 .uniqueDecoding wide5iAnalysis 128 := by
  decide +kernel

/-- **128 bits, interactively, on `2 ^ 21` rows.** The knowledge error of `wide5iSetup`, FRI at
`δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at `δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is
at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeError_le :
    knowledgeError wide5iSetup (6143 / 16384) (24575 / 65536) ≤ (2 ^ 128)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide5i_secure _ _
    (by norm_num [wide5iAnalysis]) (by norm_num [wide5iAnalysis])

/-- Knowledge soundness of `wide5iSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `24575/65536`: if no trace within `24575/65536` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeSoundness (publicValues : List F) (prover : Prover wide5iSetup) :
    (∀ trace ∈ closeTraces wide5iSetup (24575 / 65536 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 128)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _ wide5i_secure _
    (by norm_num [wide5iAnalysis]) publicValues prover

/-! ### Batches with lookups -/

section WideBus
open CompStark.Lookup

/-- `wideBus 64` packs its one lookup as it is. -/
theorem wideBus_packedLookups (logN : ℕ) :
    (wideBus 64 : Air F).packedLookups logN = [wideBusLookup] := rfl

/-- The LogUp constraints of `wideBus 64`, of degree `3`, keep its two quotient chunks. -/
theorem wideBus_logQuotientChunksWith (logN : ℕ) :
    (wideBus 64 : Air F).logQuotientChunksWith logN (logUpConstraints [wideBusLookup]) = 1 := by
  have hmax : (wideBus 64 : Air F).maxDegree = 3 := by decide +kernel
  have hext : (logUpConstraints [wideBusLookup] : List (ExtExpr F)).foldl
      (fun m c ↦ max m c.degree) 0 = 3 := by decide +kernel
  unfold Air.logQuotientChunksWith extDegree Air.constraintDegree
  simp only [show (wideBus 64 : Air F).periodic = [] from rfl, ↓reduceIte, hmax, hext]
  exact log2_two_mul_two_pow_sub_one 1

end WideBus

/-- `wideBus 64` on `2 ^ logN` rows with FRI parameters of blowup `4` and a constant final
polynomial, for `logN ≤ 22`. -/
theorem wideBus_valid (P : Fri.Params) (hb : P.logBlowup = 2) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (logN : ℕ) (h : logN ≤ 22) :
    ValidConfig P (wideBus 64 : Air F) logN :=
  have hc : (wideBus 64 : Air F).logQuotientChunks logN = (wide 64).logQuotientChunks logN := by
    unfold Air.logQuotientChunks
    rfl
  { colsInWidth := wide_colsInWidth 64
    preprocessedSize := by simp only [wideBus, wide, Array.size_empty, Nat.mul_zero]
    periodicFits := rfl
    degreeFits := by
      unfold Air.DegreeFits
      rw [hc]
      exact wide_degreeFits 64 logN
    twoAdic := by
      rw [hb]
      change logN + 2 ≤ 24
      omega
    chunksFit := by
      rw [hc, wide_logQuotientChunks 64 _ (by decide), hb]
      decide
    folds := ha
    finalPolyFits := by rw [hf]; exact Nat.zero_le _
    queries := hq
    blowup := by rw [hb]; decide }

/-- The lookup of `wideBus 64` fits its quotient chunks and reads its columns. -/
theorem wideBus_lookupsValid (P : Fri.Params) (hb : P.logBlowup = 2) (logN : ℕ) :
    LookupsValid P (wideBus 64 : Air F) logN
      (Batch.instanceLookups true (wideBus 64) logN) := by
  rw [show Batch.instanceLookups true (wideBus 64 : Air F) logN = [wideBusLookup] from
    wideBus_packedLookups logN]
  refine ⟨by rw [wideBus_logQuotientChunksWith, hb]; decide, fun l hl ↦ ?_⟩
  rw [List.mem_singleton.mp hl]
  unfold Stark.Lookup.Fits
  decide

/-- Three instances of `wideBus 64` exchange tuples of width `4` on one bus. -/
theorem wideBus_busesValid (logN : Fin 3 → ℕ) :
    Batch.BusesValid
      (List.ofFn fun i ↦ Batch.instanceLookups true (wideBus 64 : Air F) (logN i)) := by
  have hls : (List.ofFn fun i ↦ Batch.instanceLookups true (wideBus 64 : Air F) (logN i)) =
      [[wideBusLookup], [wideBusLookup], [wideBusLookup]] := rfl
  have hb : Batch.busLookups [[(wideBusLookup : Lookup F)], [wideBusLookup], [wideBusLookup]] =
      [(0, wideBusLookup), (0, wideBusLookup), (0, wideBusLookup)] := rfl
  rw [hls]
  refine ⟨fun l hl t ht ↦ ?_, fun x hx y hy _ ↦ ?_, fun x hx y hy _ ↦ ?_⟩
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
    subst hl
    revert t
    decide
  all_goals
    rw [hb] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx hy
    subst hx hy
    rfl

/-- Three instances of `wideBus 64` on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows over the quintic
extension with `wide5iParams`. -/
def wideBatchSetup : Batch.Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := ValidConfig.sound <|
    wideBus_valid wide5iParams rfl (by decide) rfl (by decide) _ (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

/-- FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)`, the extractor at
`δ' = 24575/65536 = 3/8 - 2 ^ (-16)` and `loss = 2 ^ (-19)`, as for `wide5iSetup`. -/
theorem wideBatch_secure :
    wideBatchSetup.Secure 2130706433 .uniqueDecoding wide5iAnalysis 128 := by
  decide +kernel

/-- **128 bits, interactively, for a batch of three tables of mixed heights with lookups.** The
knowledge error of `wideBatchSetup`, FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at
`δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeError_le :
    Batch.knowledgeError wideBatchSetup (6143 / 16384) (24575 / 65536) ≤ (2 ^ 128)⁻¹ :=
  Batch.knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatch_secure _ _
    (by norm_num [wide5iAnalysis]) (by norm_num [wide5iAnalysis])

/-- Knowledge soundness of `wideBatchSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `24575/65536`: if no three traces, each within `24575/65536` of its instance's
committed trace, satisfy the batch (`wideBus 64` each, the bus balanced), the verifier accepts
with probability at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeSoundness (publicValues : Fin 3 → List F)
    (prover : Batch.Prover wideBatchSetup) :
    (∀ traces ∈ Batch.closeTraces wideBatchSetup (24575 / 65536 : NNReal) prover.trace,
      ¬ wideBatchSetup.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ (2 ^ 128)⁻¹ :=
  batchKnowledgeSoundness_of_secure _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatch_secure _
    (by norm_num [wide5iAnalysis]) publicValues prover

/-! ### The batch in the random-oracle model -/

/-- The three instances `wideBus 64` on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows over the quintic
extension with `wide5Params` (`160` queries, `20` bits of query grinding). -/
def wideBatch5Setup : Batch.Setup KoalaBear.Fast.Ext5 where
  params := wide5Params
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := ValidConfig.sound <|
    wideBus_valid wide5Params rfl (by decide) rfl (by decide) _ (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

/-- `wideGrindParams` with `18` bits of grinding before the lookup challenges. -/
def wideBusGrindParams : Fri.Params := { wideGrindParams with lookupPowBits := 18 }

/-- The three instances over the quartic extension with `wideBusGrindParams` (`144` queries,
grinding in every round but `α`). -/
def wideBatchGrindSetup : Batch.Setup KoalaBear.Fast.Ext4 where
  params := wideBusGrindParams
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := ValidConfig.sound <|
    wideBus_valid wideBusGrindParams rfl (by decide) rfl (by decide) _ (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

/-- FRI at `δ = 3/8 - 2 ^ (-20)`, the extractor at `δ' = 3/8 - 2 ^ (-22)` and
`loss = 2 ^ (-60)`. -/
def wideBatch5Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 20, 3 / 8 - 1 / 2 ^ 22, 1 / 2 ^ 60⟩

/-- FRI at `δ = 3/8 - 2 ^ (-12)`, the extractor at `δ' = 3/8 - 2 ^ (-14)` and
`loss = 2 ^ (-15)`. -/
def wideBatchGrindAnalysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 12, 3 / 8 - 1 / 2 ^ 14, 1 / 2 ^ 15⟩

instance : wideBatch5Setup.CapFits := ⟨fun _ ↦ Nat.zero_le _⟩

instance : wideBatchGrindSetup.CapFits := ⟨fun _ ↦ Nat.zero_le _⟩

theorem wideBatch5_secureRo :
    wideBatch5Setup.SecureRo 2130706433 .uniqueDecoding wideBatch5Analysis 128 := by
  decide +kernel

theorem wideBatchGrind_secureRo :
    wideBatchGrindSetup.SecureRo 2130706433 .uniqueDecoding wideBatchGrindAnalysis 117 := by
  decide +kernel

/-- **128 bits per oracle answer for a batch of three tables of mixed heights with lookups.**
Every round error of `wideBatch5Setup`, FRI at `δ = 3/8 - 2 ^ (-20)` and the extractor at
`δ' = 3/8 - 2 ^ (-22)`, is at most `2 ^ (-128)`. -/
theorem wideBatch5_roundError_le :
    Batch.roundError wideBatch5Setup (3 / 8 - 2 ^ (-20 : ℤ)) (3 / 8 - 2 ^ (-22 : ℤ)) ≤
      (2 ^ 128)⁻¹ :=
  Batch.roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatch5_secureRo _ _
    (by rw [coe_sub_two_zpow _ (-20) 20 rfl (by norm_num)]; norm_num [wideBatch5Analysis])
    (by rw [coe_sub_two_zpow _ (-22) 22 rfl (by norm_num)]; norm_num [wideBatch5Analysis])

/-- **117 bits per oracle answer for a batch of three tables of mixed heights over the quartic
extension.** Every round error of `wideBatchGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-12)` and the
extractor at `δ' = 3/8 - 2 ^ (-14)`, is at most `2 ^ (-117)`. -/
theorem wideBatchGrind_roundError_le :
    Batch.roundError wideBatchGrindSetup (3 / 8 - 2 ^ (-12 : ℤ)) (3 / 8 - 2 ^ (-14 : ℤ)) ≤
      (2 ^ 117)⁻¹ :=
  Batch.roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatchGrind_secureRo _ _
    (by rw [coe_sub_two_zpow _ (-12) 12 rfl (by norm_num)]; norm_num [wideBatchGrindAnalysis])
    (by rw [coe_sub_two_zpow _ (-14) 14 rfl (by norm_num)]; norm_num [wideBatchGrindAnalysis])

theorem wideBatch5Setup_verifierQueries : wideBatch5Setup.verifierQueries = 99669 := by
  decide +kernel

theorem wideBatchGrindSetup_verifierQueries : wideBatchGrindSetup.verifierQueries = 89692 := by
  decide +kernel

/-- **128 bits per oracle call for a batch of three tables of mixed heights with lookups.** A
prover for `wideBatch5Setup` making at most `Q` oracle calls gets a proof accepted while no tuple of
traces close to the ones it committed to satisfies the batch with probability at most `q · 2 ^
(-128) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideBatch5_knowledgeSoundness_ro (publicValues : Fin wideBatch5Setup.k → List F) (Q : Nat)
    (prover : Batch.NIProver wideBatch5Setup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run wideBatch5Setup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn wideBatch5Setup.logN ∧
        ∀ traces ∈ Batch.closeTraces wideBatch5Setup (3 / 8 - 2 ^ (-22 : ℤ) : NNReal)
            (Batch.committedTraces wideBatch5Setup log proof),
          ¬ wideBatch5Setup.Satisfied traces publicValues] ≤
      (Q + wideBatch5Setup.verifierQueries) * (2 ^ 128)⁻¹ +
        hashError F 0 (Q + wideBatch5Setup.verifierQueries) :=
  Batch.batchKnowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatch5_secureRo _
    (by rw [coe_sub_two_zpow _ (-22) 22 rfl (by norm_num)]; norm_num [wideBatch5Analysis])
    publicValues Q prover hQ

/-- **117 bits per oracle call for a batch of three tables with lookups over the quartic
extension.** A prover for `wideBatchGrindSetup` making at most `Q` oracle calls gets a proof
accepted while no tuple of traces close to the ones it committed to satisfies the batch with
probability at most `q · 2 ^ (-117) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideBatchGrind_knowledgeSoundness_ro (publicValues : Fin wideBatchGrindSetup.k → List F)
    (Q : Nat) (prover : Batch.NIProver wideBatchGrindSetup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run wideBatchGrindSetup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn wideBatchGrindSetup.logN ∧
        ∀ traces ∈ Batch.closeTraces wideBatchGrindSetup (3 / 8 - 2 ^ (-14 : ℤ) : NNReal)
            (Batch.committedTraces wideBatchGrindSetup log proof),
          ¬ wideBatchGrindSetup.Satisfied traces publicValues] ≤
      (Q + wideBatchGrindSetup.verifierQueries) * (2 ^ 117)⁻¹ +
        hashError F 0 (Q + wideBatchGrindSetup.verifierQueries) :=
  Batch.batchKnowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq McaBound.uniqueDecoding_holds _
    wideBatchGrind_secureRo _
    (by rw [coe_sub_two_zpow _ (-14) 14 rfl (by norm_num)]; norm_num [wideBatchGrindAnalysis])
    publicValues Q prover hQ

end CompStark.Iop
