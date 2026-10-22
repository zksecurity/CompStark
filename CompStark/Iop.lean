/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Defs
public import CompStark.Stark.Constraints
public import CompStark.Lookup.Lookup

/-! # The STARK as an interactive oracle proof

The protocol behind `verify`, with the Merkle commitments replaced by oracles and the Fiat–Shamir
challenges by the verifier's uniform randomness. It runs over a base field `F` (`BaseField`) and
the spec field `𝕂 = Challenge.Spec EF` of a challenge field `EF` of degree `d` over it
(`Challenge`), for a `Setup EF`: FRI parameters, an AIR and a trace length `2 ^ logN`. The
prover's oracles are words on the domain `L = g · ⟨ω⟩` of `2 ^ (logN + logBlowup)` points, `g`
the base field's shift, that the trace is extended to. The verifier holds the extension of the
AIR's preprocessed trace, the polynomials through its columns on the trace domain evaluated on
`L` (`Setup.preprocessedWord`), as oracles of its own, and evaluates the AIR's periodic columns,
known polynomials, itself.

A STARK of its own proves no lookups. An instance of a batch (`CompStark/BatchIop.lean`) proves
its AIR's lookups (`Setup` with `lookups`): the prover also commits to its permutation trace, the
accumulator and the lookups' fractions over the challenge field (`Prover.perm`), and the quotient
holds the lookups' LogUp constraints too, over the batch's lookup challenges and the instance's
terminal.

1. The prover sends the extended trace, one word over `F` per column (`Prover.trace`).
2. The verifier samples the constraint-folding challenge `α`.
3. The prover sends the quotient's chunks, each as the `d` coordinates of a word over `𝕂`
   (`Prover.quotient`).
4. The verifier samples the out-of-domain point `ζ`.
5. The prover sends the claimed values of the trace's and the preprocessed trace's columns at `ζ`
   and, if the AIR reads their next rows, at `ζ ω_n`, and of the chunks at `ζ`
   (`Prover.openings`). The verifier checks the constraints at `ζ` (`ConstraintsHoldAt`).
6. The verifier samples the batching challenge `a`.
7. The prover shows with FRI that the batched DEEP word `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` over
   the opened words `fᵢ`, points `zᵢ` and values `yᵢ` is close to a polynomial of degree below
   `2 ^ logN` (`deepWord`). FRI is Plonky3's (`CompStark/Sound/FriGame.lean`): the prover
   commits to the word again and to its folds by Plonky3's arities, each after the challenge
   before it, and the queries check them against each other and against the DEEP word; the
   prover may follow any FRI strategy, and `friAcceptance` takes the best one.

`acceptance` is the probability that the verifier accepts. The extractor list-decodes the
committed trace: `closeTraces` are the traces whose columns are polynomials of degree at most
`2 ^ logN` close to the prover's trace words.
-/
@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Lookups that an AIR's instance of `2 ^ logN` rows can prove: none, or lookups whose LogUp
constraints keep the quotient's chunks within the blowup, each row-local and reading the AIR's
columns (`Lookup.Fits`). -/
def LookupsValid (params : Fri.Params) (air : Air F) (logN : Nat) : List (Lookup F) → Prop
  | [] => True
  | lookups@(_ :: _) =>
    air.logQuotientChunksWith logN (Lookup.logUpConstraints lookups) ≤ params.logBlowup ∧
      ∀ l ∈ lookups,
        l.Fits air.width air.mainNextWidth air.preprocessedWidth air.preprocessedNextWidth

/-- A STARK to prove with over the challenge field `EF`: FRI parameters, an AIR and a trace of
`2 ^ logN` rows, in a valid configuration (`ValidConfig`) with at least one FRI fold, and the
lookups it proves, Plonky3-packed (`Air.packedLookups`): none for a STARK of its own. -/
structure Setup (EF : Type) [Challenge F EF] (lookups : List (Lookup F) := []) where
  params : Fri.Params
  air : Air F
  logN : Nat
  valid : ValidConfig params air logN
  /-- FRI's final polynomial is shorter than the trace, so FRI folds at least once. -/
  folds : params.logFinalPolyLen < logN
  /-- The lookups are valid on the instance (`LookupsValid`). -/
  lookupsValid : LookupsValid params air logN lookups := by trivial

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- `n = 2 ^ logN`, the trace's length. -/
abbrev n : Nat := 2 ^ S.logN

/-- Plonky3's log number of quotient chunks, of the AIR's constraints and the lookups' LogUp
constraints. -/
abbrev logChunks : Nat := match lookups with
  | [] => S.air.logQuotientChunks S.logN
  | ls => S.air.logQuotientChunksWith S.logN (Lookup.logUpConstraints ls)

/-- The number of quotient chunks. -/
abbrev chunks : Nat := 2 ^ S.logChunks

/-- The lookups' LogUp constraints (`logUpConstraints`), none without lookups. -/
abbrev extConstraints (_ : Setup EF lookups) : List (Lookup.ExtExpr F) :=
  Lookup.logUpConstraints lookups

include S in
/-- The permutation trace's columns over the challenge field, the accumulator and one per lookup,
none without lookups. -/
abbrev permWidth : Nat := match lookups with
  | [] => 0
  | ls => ls.length + 1

/-- A STARK of its own has no permutation trace. -/
@[simp] theorem permWidth_nil (S : Setup EF) : S.permWidth = 0 := rfl

/-- `N = 2 ^ (logN + logBlowup)`, the size of `L`. -/
abbrev size : Nat := 2 ^ (S.logN + S.params.logBlowup)

/-- The points of `L`, indexed in natural order: `x_i = g ω^i`. -/
abbrev Point : Type := Fin (2 ^ (S.logN + S.params.logBlowup))

/-- The domain `L`. -/
noncomputable def domain : Domain.SmoothCosetFftDomain (S.logN + S.params.logBlowup) 𝕂 :=
  cosetDomain _ S.valid.twoAdic

/-- The polynomial of degree below `n` through column `j` of the preprocessed trace on the trace
domain `⟨ω_n⟩`. -/
noncomputable def preprocessedPoly (j : Nat) : F[X] :=
  Lagrange.interpolate (Finset.range S.n) (fun i ↦ twoAdicGen S.logN ^ i)
    fun i ↦ S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0

/-- The preprocessed trace's extension, column `j` on `L`: the verifier's own oracle. -/
noncomputable def preprocessedWord (j : Nat) (i : S.Point) : F :=
  (S.preprocessedPoly j).eval (basePoint (S.logN + S.params.logBlowup) i)

end Setup

/-- `ω_k`, the base field's generator of order `2 ^ k`, in `𝕂`. -/
noncomputable def rootOfUnity (k : Nat) : 𝕂 := lift (twoAdicGen k)

/-! ### The prover -/

/-- The values the prover claims at the out-of-domain point. -/
structure Openings {lookups : List (Lookup F)} (S : Setup EF lookups) where
  /-- Each trace column at `ζ`. -/
  traceAt : Fin S.air.width → 𝕂
  /-- Each trace column at `ζ ω_n`, if the AIR reads the next row. -/
  traceNext : Fin S.air.mainNextWidth → 𝕂
  /-- Each coordinate of each quotient chunk at `ζ`. -/
  quotientAt : Fin S.chunks → Fin (Challenge.d EF) → 𝕂
  /-- Each preprocessed column at `ζ`. -/
  preprocessedAt : Fin S.air.preprocessedWidth → 𝕂
  /-- Each preprocessed column at `ζ ω_n`, if the AIR reads the next preprocessed row. -/
  preprocessedNext : Fin S.air.preprocessedNextWidth → 𝕂
  /-- Each coordinate of each permutation column at `ζ`. -/
  permAt : Fin S.permWidth → Fin (Challenge.d EF) → 𝕂
  /-- Each coordinate of each permutation column at `ζ ω_n`. -/
  permNext : Fin S.permWidth → Fin (Challenge.d EF) → 𝕂

/-- A prover: its oracles and messages, each a function of the challenges before it. Provers are
deterministic; a randomized prover is a mixture of deterministic ones. -/
structure Prover {lookups : List (Lookup F)} (S : Setup EF lookups) where
  /-- The extended trace: each column's values on `L`. -/
  trace : Fin S.air.width → S.Point → F
  /-- The quotient's chunks, after `α`: coordinate `e` of chunk `c` on `L`. -/
  quotient : (α : 𝕂) → Fin S.chunks → Fin (Challenge.d EF) → S.Point → F
  /-- The claimed values, after `α` and `ζ`. -/
  openings : (α ζ : 𝕂) → Openings S
  /-- The extended permutation trace, sent before `α` (after the batch's lookup challenges):
  coordinate `e` of column `c` on `L`. -/
  perm : Fin S.permWidth → Fin (Challenge.d EF) → S.Point → F

/-! ### The verifier -/

/-- `Z_D(x) = (x / s) ^ m - 1`, the vanishing polynomial of a coset `s · ⟨ω_m⟩`. -/
noncomputable def vanishing (s : 𝕂) (m : Nat) (x : 𝕂) : 𝕂 := (x / s) ^ m - 1

variable {lookups : List (Lookup F)}

/-- The shift of quotient chunk `c`'s domain: `g ω_q ^ c`, `ω_q` of order `n · chunks`. -/
noncomputable def chunkShift (S : Setup EF lookups) (c : Nat) : 𝕂 :=
  lift gen * rootOfUnity (S.logN + S.logChunks) ^ c

/-- A permutation column's value from its coordinates' values `v`: `∑ₑ genᵉ vₑ`, `0` past the
width. -/
noncomputable def permValue {w : Nat} (v : Fin w → Fin (Challenge.d EF) → 𝕂) (c : Nat) : 𝕂 :=
  if h : c < w then ∑ e : Fin (Challenge.d EF), CompPoly.Extension.Ext.gen ^ (e : Nat) * v ⟨c, h⟩ e
  else 0

/-- The constraint check at `ζ` (`checkConstraints` and `recompose`, over `𝕂`): the constraints
and then the LogUp constraints, folded by `α`, on the claimed values of the trace, the
preprocessed trace (zeros for an unopened row) and the permutation trace, the periodic columns'
polynomials, the selectors at `ζ`, the lookup challenges `challenges` and the terminal, divided by
`Z_H(ζ)`, equal the quotient recomposed from the claimed chunks. -/
def ConstraintsHoldAt (S : Setup EF lookups) (publicValues : List F) (α ζ : 𝕂) (o : Openings S)
    (challenges : List 𝕂 := []) (terminal : 𝕂 := 0) : Prop :=
  let ω := rootOfUnity S.logN
  let zh := vanishing 1 S.n ζ
  let env : Expr.Env F 𝕂 :=
    { cur := fun j ↦ if h : j < S.air.width then o.traceAt ⟨j, h⟩ else 0
      next := fun j ↦ if h : j < S.air.mainNextWidth then o.traceNext ⟨j, h⟩ else 0
      prepCur := fun j ↦
        if h : j < S.air.preprocessedWidth then o.preprocessedAt ⟨j, h⟩ else 0
      prepNext := fun j ↦
        if h : j < S.air.preprocessedNextWidth then o.preprocessedNext ⟨j, h⟩ else 0
      periodic := fun j ↦ aeval ζ (S.air.periodicPolys S.logN j)
      pub := fun i ↦ lift (publicValues.getD i 0)
      const := lift
      isFirstRow := zh / (ζ - 1)
      isLastRow := zh / (ζ - ω⁻¹)
      isTransition := ζ - ω⁻¹ }
  let aux : Lookup.ExtExpr.Env 𝕂 :=
    ⟨permValue o.permAt, permValue o.permNext, (challenges.getD · 0), terminal⟩
  let folded := S.extConstraints.foldl (fun acc g ↦ acc * α + g.eval env aux)
    (S.air.constraints.foldl (fun acc c ↦ acc * α + c.eval env) 0)
  let selector (c : Fin S.chunks) : 𝕂 := ∏ d : Fin S.chunks with d ≠ c,
    vanishing (chunkShift S d) S.n ζ / vanishing (chunkShift S d) S.n (chunkShift S c)
  let chunk (c : Fin S.chunks) : 𝕂 :=
    ∑ e : Fin (Challenge.d EF), CompPoly.Extension.Ext.gen ^ (e : Nat) * o.quotientAt c e
  folded / zh = ∑ c, selector c * chunk c

/-- The opened words with their points and claimed values, in Plonky3's batching order: the trace
columns at `ζ` and, if opened, at `ζ ω_n`, each chunk's coordinates at `ζ`, the preprocessed
columns at `ζ` and, if opened, at `ζ ω_n`, and the permutation columns' coordinates at `ζ` and at
`ζ ω_n`. -/
noncomputable def openedWords {S : Setup EF lookups} (p : Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.width).map (fun j ↦ (p.trace j, ζ, o.traceAt j)) ++
  (List.finRange S.air.mainNextWidth).map (fun j ↦
    (p.trace (Fin.castLE S.air.mainNextWidth_le j), ζ * rootOfUnity S.logN, o.traceNext j)) ++
  ((List.finRange S.chunks).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.quotient α c e, ζ, o.quotientAt c e)) ++
  (List.finRange S.air.preprocessedWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ, o.preprocessedAt j)) ++
  (List.finRange S.air.preprocessedNextWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ * rootOfUnity S.logN, o.preprocessedNext j)) ++
  ((List.finRange S.permWidth).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.perm c e, ζ, o.permAt c e)) ++
  ((List.finRange S.permWidth).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.perm c e, ζ * rootOfUnity S.logN, o.permNext c e))

/-- The batched DEEP word: `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` at each point `x` of `L`. -/
noncomputable def deepWord {S : Setup EF lookups} (p : Prover S) (α ζ a : 𝕂) (i : S.Point) : 𝕂 :=
  ((openedWords p α ζ).zipIdx.map fun ((f, z, y), k) ↦
    a ^ k * (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)).sum

/-- FRI's rounds on `L`: Plonky3's folding schedule from `L` down to the final polynomial's
domain of `2 ^ (logFinalPolyLen + logBlowup)` points, injecting the word `words m` of the domain
of `2 ^ m` points at each log size `m` of `heights` (tallest first) when the folds reach it. -/
noncomputable def Setup.friRounds (S : Setup EF lookups) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (heights : List ℕ) : FriGame.Rounds 𝕂 (S.logN + S.params.logBlowup) :=
  FriGame.Rounds.schedule S.params.maxLogArity (S.params.logFinalPolyLen + S.params.logBlowup)
    words (S.logN + S.params.logBlowup) (S.logN + S.params.logBlowup) heights

/-- The probability that FRI accepts `word` on `L`, with the words `words m` injected at the log
sizes `heights`, against the best FRI prover: Plonky3's FRI (`FriGame.acceptance`) with a final
polynomial of degree below `2 ^ logFinalPolyLen` and `numQueries` queries. -/
noncomputable def friAcceptanceWith (S : Setup EF lookups) (words : (m : ℕ) → Fin (2 ^ m) → 𝕂)
    (heights : List ℕ) (word : S.Point → 𝕂) : ENNReal :=
  FriGame.acceptance S.domain (S.friRounds words heights) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries (Nat.two_pow_pos _) word

/-- The probability that FRI accepts `word` against the best FRI prover. -/
noncomputable def friAcceptance (S : Setup EF lookups) (word : S.Point → 𝕂) : ENNReal :=
  friAcceptanceWith S (fun _ _ ↦ 0) [] word

open Classical in
/-- The probability that the verifier accepts `prover`: over uniform `α`, `ζ` and `a`, the
constraints hold at `ζ` and FRI accepts the batched DEEP word. -/
noncomputable def acceptance {S : Setup EF} (publicValues : List F) (prover : Prover S) :
    ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 3 * ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
    if ConstraintsHoldAt S publicValues α ζ (prover.openings α ζ)
    then friAcceptance S (deepWord prover α ζ a) else 0

/-! ### The extractor: list decoding -/

/-- The trace whose columns take the values of the polynomials `columns` on the trace domain's
rows `ω_n ^ i`, row-major. -/
noncomputable def traceOf (S : Setup EF lookups) (columns : Fin S.air.width → F[X]) : Array F :=
  Array.ofFn fun r : Fin (S.n * S.air.width) ↦
    let (row, column) := finProdFinEquiv.symm r
    (columns column).eval (twoAdicGen S.logN ^ row.val)

/-- Words on `L` agree with polynomials on a common set of at least `(1 - δ) N` points. -/
def Agree (S : Setup EF lookups) {ι : Type} (δ : ℝ) (words : ι → S.Point → F)
    (polys : ι → F[X]) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧
    ∀ i ∈ T, ∀ k, words k i = (polys k).eval (basePoint (S.logN + S.params.logBlowup) i)

/-- The traces the extractor reads off committed trace words at proximity `δ`, by list decoding:
those whose columns are polynomials of degree at most `n` agreeing with the words on a common set
of at least `(1 - δ) N` points. -/
def closeTraces (S : Setup EF lookups) (δ : ℝ) (words : Fin S.air.width → S.Point → F) :
    Set (Array F) :=
  {t | ∃ columns : Fin S.air.width → F[X], (∀ j, (columns j).natDegree ≤ S.n) ∧
    Agree S δ words columns ∧ t = traceOf S columns}

end CompStark.Iop
