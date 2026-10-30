/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Defs
public import CompStark.Stark.Constraints
public import CompStark.Lookup.Lookup

/-! # The STARK's setups, messages and checks

What the STARK proves and what its interactive oracle protocol (`CompStark/Interaction/Stark.lean`)
exchanges, over a base field `F` (`BaseField`) and the spec field `𝕂 = Challenge.Spec EF` of a
challenge field `EF` of degree `d` over it (`Challenge`). A `Setup EF` is FRI parameters, an AIR
and a trace length `2 ^ logN`, in a sound configuration; a `Statement` is the same without the
length, which the prover claims and the verifier checks (`Statement.Admits`). The prover's words
are on the domain `L = g · ⟨ω⟩` of `2 ^ (logN + logBlowup)` points, `g` the base field's shift,
that the trace is extended to. The verifier holds the extension of the AIR's preprocessed trace
(`Setup.preprocessedWord`) as words of its own, and evaluates the AIR's periodic columns, known
polynomials, itself.

A STARK of its own proves no lookups. An instance of a batch (`CompStark/Interaction/BatchSetup.lean`) proves
its AIR's lookups (`Setup` with `lookups`): the prover also commits to its permutation trace, the
accumulator and the lookups' fractions over the challenge field (`Prover.perm`), and the quotient
holds the lookups' LogUp constraints too, over the batch's lookup challenges and the instance's
terminal.

A `Prover` is the prover's words and messages as functions of the challenges before them: the
extended trace, the quotient's chunks after `α`, and the claimed values at `ζ` (`Openings`) after
`ζ`. The verifier checks the constraints at `ζ` (`ConstraintsHoldAt`) and runs FRI on the batched
DEEP word `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` over the opened words `fᵢ`, points `zᵢ` and values `yᵢ`
(`openedWords`, `deepWord`), along Plonky3's schedule (`Setup.friRounds`). The extractor
list-decodes the committed trace: `closeTraces` are the traces whose columns are polynomials of
degree at most `2 ^ logN` close to the prover's trace words.
-/
@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Lookups that an AIR's instance of `2 ^ logN` rows can prove: none, or lookups whose LogUp
constraints keep the quotient domain within the two-adic subgroups, as the verifier checks, each
row-local and reading the AIR's columns (`Lookup.Fits`). -/
def LookupsValid (air : Air F) (logN : Nat) : List (Lookup F) → Prop
  | [] => True
  | lookups@(_ :: _) =>
    logN + air.logQuotientChunksWith logN (Lookup.logUpConstraints lookups) ≤ twoAdicity F ∧
      ∀ l ∈ lookups,
        l.Fits air.width air.mainNextWidth air.preprocessedWidth air.preprocessedNextWidth

/-- A STARK to prove with over the challenge field `EF`: FRI parameters, an AIR and a trace of
`2 ^ logN` rows, in a sound configuration (`SoundConfig`), and the lookups it proves,
Plonky3-packed (`Air.packedLookups`): none for a STARK of its own. -/
structure Setup (EF : Type) [Challenge F EF] (lookups : List (Lookup F) := []) where
  params : Fri.Params
  air : Air F
  logN : Nat
  valid : SoundConfig params air logN
  /-- The lookups are valid on the instance (`LookupsValid`). -/
  lookupsValid : LookupsValid air logN lookups := by trivial

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- FRI's final polynomial is shorter than the trace, so FRI folds at least once. -/
class Folds : Prop where
  folds : S.params.logFinalPolyLen < S.logN

theorem folds [h : S.Folds] : S.params.logFinalPolyLen < S.logN := h.folds

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

/-- A STARK's statement: FRI parameters and an AIR whose constraints read only its columns. The
trace length is not part of it: a proof claims it, and the verifier checks it (`Statement.Admits`);
`Statement.setupAt` is the STARK at a length. -/
structure Statement (F : Type) [BaseField F] where
  params : Fri.Params
  air : Air F
  /-- The constraints read only the AIR's columns, and the next preprocessed row only if the AIR
  declares it reads it. -/
  colsInWidth : air.ColsInWidth

namespace Statement
variable (C : Statement F)

/-- The log height of the AIR's preprocessed trace, its size over its width: the trace length its
verifying key fixes. -/
def preprocessedLogN : Nat := Nat.log2 (C.air.preprocessed.size / C.air.preprocessedWidth)

/-- The trace lengths `2 ^ n` the verifier admits: its checks on the length and the parameters
(`SoundConfig`, the AIR reading only its columns), and the preprocessed trace's length if the AIR
has one, which its verifying key fixes. -/
structure Admits (n : Nat) : Prop where
  sound : SoundConfig C.params C.air n
  preprocessed : 0 < C.air.preprocessedWidth → n = C.preprocessedLogN

/-- The STARK at an admitted trace length. -/
def setupAt (EF : Type) [Challenge F EF] (n : Nat) (h : C.Admits n) : Setup EF :=
  ⟨C.params, C.air, n, h.sound, trivial⟩

/-- The rate `1 / 2 ^ logBlowup` of the trace's code, at every length. -/
noncomputable def rate : ℝ := 1 / 2 ^ C.params.logBlowup

end Statement

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

/-- The prover's words and messages, each a function of the challenges before it. -/
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

namespace Setup
variable (S : Setup EF lookups)

/-- The committed words that the check at `ζ` reads, as one family: the trace's columns, the
coordinates of the permutation trace's columns and the coordinates of the quotient's chunks. -/
abbrev Committed : Type :=
  Fin S.air.width ⊕ (Fin S.permWidth × Fin (Challenge.d EF)) ⊕
    (Fin S.chunks × Fin (Challenge.d EF))

/-- A trace, a permutation trace and a quotient as one family over `Committed`. -/
def committed {α : Type} (trace : Fin S.air.width → α)
    (perm : Fin S.permWidth → Fin (Challenge.d EF) → α)
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → α) : S.Committed → α :=
  Sum.elim trace (Sum.elim (fun ce ↦ perm ce.1 ce.2) fun ce ↦ quotient ce.1 ce.2)

/-- The trace of a family over `Committed`. -/
def committedTrace {α : Type} (J : S.Committed → α) : Fin S.air.width → α :=
  fun j ↦ J (.inl j)

/-- The permutation trace of a family over `Committed`. -/
def committedPerm {α : Type} (J : S.Committed → α) : Fin S.permWidth → Fin (Challenge.d EF) → α :=
  fun c e ↦ J (.inr (.inl (c, e)))

/-- The quotient of a family over `Committed`. -/
def committedQuotient {α : Type} (J : S.Committed → α) :
    Fin S.chunks → Fin (Challenge.d EF) → α :=
  fun c e ↦ J (.inr (.inr (c, e)))

variable {α : Type} (trace : Fin S.air.width → α)
  (perm : Fin S.permWidth → Fin (Challenge.d EF) → α)
  (quotient : Fin S.chunks → Fin (Challenge.d EF) → α)

@[simp] theorem committedTrace_committed :
    S.committedTrace (S.committed trace perm quotient) = trace := rfl

@[simp] theorem committedPerm_committed :
    S.committedPerm (S.committed trace perm quotient) = perm := rfl

@[simp] theorem committedQuotient_committed :
    S.committedQuotient (S.committed trace perm quotient) = quotient := rfl

end Setup

/-- The traces the extractor reads off committed trace words at proximity `δ`, by list decoding:
those whose columns are polynomials of degree at most `n` agreeing with the words on a common set
of at least `(1 - δ) N` points. -/
def closeTraces (S : Setup EF lookups) (δ : ℝ) (words : Fin S.air.width → S.Point → F) :
    Set (Array F) :=
  {t | ∃ columns : Fin S.air.width → F[X], (∀ j, (columns j).natDegree ≤ S.n) ∧
    Agree S δ words columns ∧ t = traceOf S columns}

end CompStark.Iop
