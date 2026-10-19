/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Defs

/-! # The STARK as an interactive oracle proof

The protocol behind `verify`, with the Merkle commitments replaced by oracles and the Fiat–Shamir
challenges by the verifier's uniform randomness. It runs over KoalaBear `𝔽 = KoalaBear.Field` and
its quartic extension `𝕂 = KoalaBear.Ext4`, for a `Setup`: FRI parameters, an AIR and a trace
length `2 ^ logN`. The prover's oracles are words on the domain `L = g · ⟨ω⟩` of
`2 ^ (logN + logBlowup)` points, `g = 3`, that the trace is extended to.

1. The prover sends the extended trace, one word over `𝔽` per column (`Prover.trace`).
2. The verifier samples the constraint-folding challenge `α`.
3. The prover sends the quotient's chunks, each as the four coordinates of a word over `𝕂`
   (`Prover.quotient`).
4. The verifier samples the out-of-domain point `ζ`.
5. The prover sends the claimed values of the trace's columns at `ζ` and `ζ ω_n` and of the
   chunks at `ζ` (`Prover.openings`). The verifier checks the constraints at `ζ`
   (`ConstraintsHoldAt`).
6. The verifier samples the batching challenge `a`.
7. The prover shows with FRI that the batched DEEP word `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` over
   the opened words `fᵢ`, points `zᵢ` and values `yᵢ` is close to a polynomial of degree below
   `2 ^ logN` (`deepWord`). FRI is ArkLib's oracle reduction, folding by Plonky3's arities; the
   prover may follow any FRI strategy, and `friAcceptance` takes the best one.

`acceptance` is the probability that the verifier accepts. The extractor list-decodes the
committed trace: `closeTraces` are the traces whose columns are polynomials of degree at most
`2 ^ logN` close to the prover's trace words.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound Polynomial Montgomery.Native32

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

/-- A STARK to prove with: FRI parameters, an AIR and a trace of `2 ^ logN` rows, in a valid
configuration (`ValidConfig`) with a positive blowup and at least one FRI fold. -/
structure Setup where
  params : Fri.Params
  air : Air
  logN : Nat
  valid : ValidConfig params air logN
  /-- The trace is extended to at least twice its length, so that its code has room to detect
  errors. -/
  blowup : 0 < params.logBlowup
  /-- FRI's final polynomial is shorter than the trace, so FRI folds at least once. -/
  folds : params.logFinalPolyLen < logN

namespace Setup
variable (S : Setup)

/-- `n = 2 ^ logN`, the trace's length. -/
abbrev n : Nat := 2 ^ S.logN

/-- The number of quotient chunks. -/
abbrev chunks : Nat := 2 ^ S.air.logQuotientChunks

/-- `N = 2 ^ (logN + logBlowup)`, the size of `L`. -/
abbrev size : Nat := 2 ^ (S.logN + S.params.logBlowup)

/-- The points of `L`, indexed in natural order: `x_i = g ω^i`. -/
abbrev Point : Type := Fin (2 ^ (S.logN + S.params.logBlowup))

/-- The domain `L`. -/
noncomputable def domain : Domain.SmoothCosetFftDomain (S.logN + S.params.logBlowup) 𝕂 :=
  cosetDomain _ S.valid.twoAdic

end Setup

/-- `ω_k`, KoalaBear's generator of order `2 ^ k`, in `𝕂`. -/
noncomputable def rootOfUnity (k : Nat) : 𝕂 := lift (twoAdicGen k)

/-! ### The prover -/

/-- The values the prover claims at the out-of-domain point. -/
structure Openings (S : Setup) where
  /-- Each trace column at `ζ`. -/
  traceAt : Fin S.air.width → 𝕂
  /-- Each trace column at `ζ ω_n`, the next row. -/
  traceNext : Fin S.air.width → 𝕂
  /-- Each coordinate of each quotient chunk at `ζ`. -/
  quotientAt : Fin S.chunks → Fin 4 → 𝕂

/-- A prover: its oracles and messages, each a function of the challenges before it. Provers are
deterministic; a randomized prover is a mixture of deterministic ones. -/
structure Prover (S : Setup) where
  /-- The extended trace: each column's values on `L`. -/
  trace : Fin S.air.width → S.Point → 𝔽
  /-- The quotient's chunks, after `α`: coordinate `e` of chunk `c` on `L`. -/
  quotient : (α : 𝕂) → Fin S.chunks → Fin 4 → S.Point → 𝔽
  /-- The claimed values, after `α` and `ζ`. -/
  openings : (α ζ : 𝕂) → Openings S

/-! ### The verifier -/

/-- `Z_D(x) = (x / s) ^ m - 1`, the vanishing polynomial of a coset `s · ⟨ω_m⟩`. -/
noncomputable def vanishing (s : 𝕂) (m : Nat) (x : 𝕂) : 𝕂 := (x / s) ^ m - 1

/-- The shift of quotient chunk `c`'s domain: `g ω_q ^ c`, `ω_q` of order `n · chunks`. -/
noncomputable def chunkShift (S : Setup) (c : Nat) : 𝕂 :=
  lift gen * rootOfUnity (S.logN + S.air.logQuotientChunks) ^ c

/-- The constraint check at `ζ` (`checkConstraints` and `recompose`, over `𝕂`): the constraints,
folded by `α`, on the claimed trace values with the selectors at `ζ`, divided by `Z_H(ζ)`, equal
the quotient recomposed from the claimed chunks. -/
def ConstraintsHoldAt (S : Setup) (publicValues : List F) (α ζ : 𝕂) (o : Openings S) : Prop :=
  let ω := rootOfUnity S.logN
  let zh := vanishing 1 S.n ζ
  let env : Expr.Env 𝕂 :=
    { cur := fun j ↦ if h : j < S.air.width then o.traceAt ⟨j, h⟩ else 0
      next := fun j ↦ if h : j < S.air.width then o.traceNext ⟨j, h⟩ else 0
      pub := fun i ↦ lift (publicValues.getD i 0)
      const := lift
      isFirstRow := zh / (ζ - 1)
      isLastRow := zh / (ζ - ω⁻¹)
      isTransition := ζ - ω⁻¹ }
  let folded := S.air.constraints.foldl (fun acc c ↦ acc * α + c.eval env) 0
  let selector (c : Fin S.chunks) : 𝕂 := ∏ d : Fin S.chunks with d ≠ c,
    vanishing (chunkShift S d) S.n ζ / vanishing (chunkShift S d) S.n (chunkShift S c)
  let chunk (c : Fin S.chunks) : 𝕂 :=
    ∑ e : Fin 4, CompPoly.Extension.Ext.gen ^ (e : Nat) * o.quotientAt c e
  folded / zh = ∑ c, selector c * chunk c

/-- The opened words with their points and claimed values, in Plonky3's batching order: the trace
columns at `ζ`, the trace columns at `ζ ω_n`, each chunk's coordinates at `ζ`. -/
noncomputable def openedWords {S : Setup} (p : Prover S) (α ζ : 𝕂) :
    List ((S.Point → 𝔽) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.width).map (fun j ↦ (p.trace j, ζ, o.traceAt j)) ++
  (List.finRange S.air.width).map (fun j ↦ (p.trace j, ζ * rootOfUnity S.logN, o.traceNext j)) ++
  (List.finRange S.chunks).flatMap fun c ↦ (List.finRange 4).map fun e ↦
    (p.quotient α c e, ζ, o.quotientAt c e)

/-- The batched DEEP word: `∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` at each point `x` of `L`. -/
noncomputable def deepWord {S : Setup} (p : Prover S) (α ζ a : 𝕂) (i : S.Point) : 𝕂 :=
  ((openedWords p α ζ).zipIdx.map fun ((f, z, y), k) ↦
    a ^ k * (y - algebraMap 𝔽 𝕂 (f i)) / (z - S.domain i)).sum

/-- The probability that FRI accepts `word` against the best FRI prover: ArkLib's FRI oracle
reduction on `L`, folding by Plonky3's arities down to a final polynomial of degree below
`2 ^ logFinalPolyLen`, with `numQueries` queries. -/
noncomputable def friAcceptance (S : Setup) (word : S.Point → 𝕂) : ENNReal :=
  friAcceptanceOf S.domain
    (Sound.folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen))
    S.params.logFinalPolyLen S.params.numQueries word

open Classical in
/-- The probability that the verifier accepts `prover`: over uniform `α`, `ζ` and `a`, the
constraints hold at `ζ` and FRI accepts the batched DEEP word. -/
noncomputable def acceptance {S : Setup} (publicValues : List F) (prover : Prover S) :
    ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 3 * ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
    if ConstraintsHoldAt S publicValues α ζ (prover.openings α ζ)
    then friAcceptance S (deepWord prover α ζ a) else 0

/-! ### The extractor: list decoding -/

/-- The trace whose columns take the values of the polynomials `columns` on the trace domain's
rows `ω_n ^ i`, row-major. -/
noncomputable def traceOf (S : Setup) (columns : Fin S.air.width → 𝔽[X]) : Array F :=
  Array.ofFn fun r : Fin (S.n * S.air.width) ↦
    let (row, column) := finProdFinEquiv.symm r
    KoalaBear.Fast.ringEquiv.symm
      ((columns column).eval (FastField.toField (twoAdicGen S.logN) ^ row.val))

/-- Words on `L` agree with polynomials on a common set of at least `(1 - δ) N` points. -/
def Agree (S : Setup) {ι : Type} (δ : ℝ) (words : ι → S.Point → 𝔽) (polys : ι → 𝔽[X]) :
    Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧
    ∀ i ∈ T, ∀ k, words k i = (polys k).eval (basePoint (S.logN + S.params.logBlowup) i)

/-- The traces the extractor reads off a prover at proximity `δ`, by list decoding: those whose
columns are polynomials of degree at most `n` agreeing with the prover's trace words on a common
set of at least `(1 - δ) N` points. -/
def closeTraces (S : Setup) (δ : ℝ) (prover : Prover S) : Set (Array F) :=
  {t | ∃ columns : Fin S.air.width → 𝔽[X], (∀ j, (columns j).natDegree ≤ S.n) ∧
    Agree S δ prover.trace columns ∧ t = traceOf S columns}

end CompStark.Iop
