/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop
public import Mathlib.Data.Finset.Sort

/-! # The batch STARK as an interactive oracle proof

The protocol behind `verifyBatchWith`, with oracles in place of the Merkle commitments and uniform
challenges in place of Fiat–Shamir, for a `Batch.Setup`: FRI parameters and `k ≥ 1` AIR instances,
instance `i` with a trace of `2 ^ logN i` rows, proving its AIR's lookups (`Setup.lookups`, the
lookups packed as Plonky3 packs them). Each instance is a STARK of its own with its lookups
(`Setup.instanceSetup`, `CompStark/Iop.lean`), on its own domain `Lᵢ` of
`2 ^ (logN i + logBlowup)` points; the rounds are the STARK's, every instance in each, after a
round for the lookups:

1. The prover sends every instance's extended trace (`Prover.trace`).
2. The verifier samples the lookup challenges `(α_L, β_L)`. Lookup `c` of instance `i` gets its
   bus `b`'s denominator base `α_L + (b + 1) β_Lᵂ` and `β_L` (`Setup.challenges`).
3. The prover sends every instance's extended permutation trace (`Prover.perm`) and terminal
   (`Prover.terminal`). The verifier checks that the terminals of the instances with lookups sum
   to zero.
4. The verifier samples one constraint-folding challenge `α`.
5. The prover sends every instance's quotient chunks (`Prover.quotient`).
6. The verifier samples one out-of-domain point `ζ`.
7. The prover sends every instance's claimed values (`Prover.openings`). The verifier checks
   every instance's constraints and LogUp constraints at `ζ` (`ConstraintsHoldAt`), over its
   lookup challenges and terminal.
8. The verifier samples the batching challenge `a`.
9. As Plonky3's commitment scheme reduces the openings by height, the verifier batches, for each
   domain size, the DEEP quotients of the opened words of the instances of that size, in Plonky3's
   order (`groupOpened`: the main traces, the quotients, the preprocessed traces, the permutation
   traces), by the powers of `a` starting over at each size (`groupDeepWord`). The prover shows
   with FRI that these words are close to polynomials of degree below their traces' lengths: FRI
   runs on the tallest word and injects each shorter one when its folds reach that size
   (`friAcceptanceWith`).

`acceptance` is the probability that the verifier accepts. The extractor list-decodes every
instance's committed trace: `closeTraces` are the tuples of traces, one per instance, each close
to that instance's committed trace (`Iop.closeTraces`). The permutation traces are auxiliary: the
extractor does not output them.

A batch without lookups (`Setup` with `withLookups := false`) is a batch of STARKs of their own;
a STARK is such a batch of one instance (`Setup.toBatch`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CompStark.Lookup

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Batch

/-- The lookups an instance proves: its AIR's, packed for its height (`Air.packedLookups`), if the
batch proves lookups. -/
def instanceLookups (withLookups : Bool) (air : Air F) (logN : Nat) : List (Stark.Lookup F) :=
  if withLookups then air.packedLookups logN else []

/-- Every lookup of the instances' lookups `ls` with its bus number (`busIds`). -/
def busLookups (ls : List (List (Stark.Lookup F))) : List (Nat × Stark.Lookup F) :=
  (ls.zip (busIds ls)).flatMap fun (L, ids) ↦ ids.zip L

/-- The instances' lookups `ls` are valid together: every lookup's tuples share its width, and
so do the lookups of one bus (Plonky3's `check_bus_widths`), and the buses' numbers `b` give
distinct base elements `b + 1`. -/
structure BusesValid (ls : List (List (Stark.Lookup F))) : Prop where
  tupleWidths : ∀ l ∈ ls.flatten, ∀ t ∈ l.tuples, t.1.length = l.width
  busWidths : ∀ x ∈ busLookups ls, ∀ y ∈ busLookups ls, x.1 = y.1 → x.2.width = y.2.width
  distinct : ∀ x ∈ busLookups ls, ∀ y ∈ busLookups ls,
    ((x.1 + 1 : ℕ) : F) = ((y.1 + 1 : ℕ) : F) → x.1 = y.1

/-- A batch STARK to prove with over the challenge field `EF`: FRI parameters and `k ≥ 1` AIRs,
instance `i` with a trace of `2 ^ logN i` rows in a valid configuration (`ValidConfig`), with at
least one FRI fold, proving its AIR's lookups if `withLookups`. -/
structure Setup (EF : Type) [Challenge F EF] (withLookups : Bool := true) where
  params : Fri.Params
  /-- The number of instances. -/
  k : Nat
  air : Fin k → Air F
  logN : Fin k → Nat
  valid : ∀ i, ValidConfig params (air i) (logN i)
  /-- FRI's final polynomial is shorter than every trace, so FRI folds at least once. -/
  folds : ∀ i, params.logFinalPolyLen < logN i
  /-- The batch has an instance. -/
  nonempty : 0 < k
  /-- Every instance's lookups are valid on it (`LookupsValid`). -/
  lookupsValid : ∀ i, LookupsValid params (air i) (logN i)
    (instanceLookups withLookups (air i) (logN i))
  /-- The instances' lookups are valid together (`BusesValid`). -/
  buses : BusesValid (List.ofFn fun i ↦ instanceLookups withLookups (air i) (logN i))

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

/-- Instance `i`'s lookups (`instanceLookups`). -/
abbrev lookups (i : Fin S.k) : List (Stark.Lookup F) :=
  instanceLookups withLookups (S.air i) (S.logN i)

/-- Instance `i` as a STARK of its own with its lookups. -/
abbrev instanceSetup (i : Fin S.k) : Iop.Setup EF (S.lookups i) :=
  ⟨S.params, S.air i, S.logN i, S.valid i, S.folds i, S.lookupsValid i⟩

/-- An instance of the largest trace length: the last of the largest. -/
def top : Fin S.k :=
  (List.finRange S.k).foldl (fun t i ↦ if S.logN t ≤ S.logN i then i else t) ⟨0, S.nonempty⟩

theorem logN_le_top (i : Fin S.k) : S.logN i ≤ S.logN S.top := by
  have key : ∀ (l : List (Fin S.k)) (t : Fin S.k), S.logN t ≤
      S.logN (l.foldl (fun t i ↦ if S.logN t ≤ S.logN i then i else t) t) ∧
      ∀ j ∈ l, S.logN j ≤ S.logN (l.foldl (fun t i ↦ if S.logN t ≤ S.logN i then i else t) t) := by
    intro l
    induction l with
    | nil => exact fun t ↦ ⟨le_rfl, fun j hj ↦ absurd hj List.not_mem_nil⟩
    | cons x l ih =>
      intro t
      rw [List.foldl_cons]
      set t' := if S.logN t ≤ S.logN x then x else t
      have ht' : S.logN t ≤ S.logN t' ∧ S.logN x ≤ S.logN t' := by
        simp only [t']
        split <;> omega
      obtain ⟨h1, h2⟩ := ih t'
      refine ⟨ht'.1.trans h1, fun j hj ↦ ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ht'.2.trans h1
      · exact h2 j hj
  exact (key _ _).2 i (List.mem_finRange i)

/-- The tallest instance's setup, for FRI, which runs on its domain. -/
abbrev domainSetup : Iop.Setup EF (S.lookups S.top) := S.instanceSetup S.top

/-- The log sizes of the domains below the tallest, tallest first: where FRI injects the
batched DEEP words of the shorter instances. -/
def friHeights : List ℕ :=
  (List.range (S.logN S.top + S.params.logBlowup)).reverse.filter fun h ↦
    (List.finRange S.k).any fun i ↦ S.logN i + S.params.logBlowup == h

/-- The lookup challenges of instance `i` from the batch's pair `(α_L, β_L)`: for each of its
lookups, its bus `b`'s denominator base `α_L + (b + 1) β_Lᵂ` and the combiner `β_L`, `W` the
widest tuple of the batch and at least `1` (Plonky3's `lay_out_lookup_challenges`,
`challengeLayout`). -/
noncomputable def challenges (lookupAlpha lookupBeta : 𝕂) (i : Fin S.k) : List 𝕂 :=
  ((busIds (List.ofFn S.lookups)).getD i []).flatMap fun b ↦
    [lookupAlpha + algebraMap F 𝕂 ((b + 1 : ℕ) : F) *
      lookupBeta ^ maxWidth (List.ofFn S.lookups).flatten, lookupBeta]

end Setup

/-! ### The prover -/

/-- A prover: every instance's oracles and messages, each a function of the challenges before
it. -/
structure Prover {withLookups : Bool} (S : Setup EF withLookups) where
  /-- Every instance's extended trace: each column's values on its domain. -/
  trace : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F
  /-- Every instance's extended permutation trace, after `(α_L, β_L)`: coordinate `e` of column
  `c` on its domain. -/
  perm : (lookupAlpha lookupBeta : 𝕂) → (i : Fin S.k) → Fin (S.instanceSetup i).permWidth →
    Fin (Challenge.d EF) → (S.instanceSetup i).Point → F
  /-- Every instance's terminal, after `(α_L, β_L)`. -/
  terminal : (lookupAlpha lookupBeta : 𝕂) → Fin S.k → 𝕂
  /-- Every instance's quotient chunks, after `α`. -/
  quotient : (lookupAlpha lookupBeta α : 𝕂) → (i : Fin S.k) → Fin (S.instanceSetup i).chunks →
    Fin (Challenge.d EF) → (S.instanceSetup i).Point → F
  /-- Every instance's claimed values, after `α` and `ζ`. -/
  openings : (lookupAlpha lookupBeta α ζ : 𝕂) → (i : Fin S.k) → Openings (S.instanceSetup i)

/-- Instance `i`'s part of the prover, after the lookup challenges. -/
def Prover.instanceProver {withLookups : Bool} {S : Setup EF withLookups} (p : Prover S)
    (lookupAlpha lookupBeta : 𝕂) (i : Fin S.k) : Iop.Prover (S.instanceSetup i) :=
  ⟨p.trace i, fun α ↦ p.quotient lookupAlpha lookupBeta α i,
    fun α ζ ↦ p.openings lookupAlpha lookupBeta α ζ i, p.perm lookupAlpha lookupBeta i⟩

/-! ### The verifier -/

variable {lookups : List (Stark.Lookup F)}

/-- A STARK's opened trace words: the columns at `ζ`, then, if opened, at `ζ ω_n`. -/
noncomputable def mainOpened {S : Iop.Setup EF lookups} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.width).map (fun j ↦ (p.trace j, ζ, o.traceAt j)) ++
  (List.finRange S.air.mainNextWidth).map (fun j ↦
    (p.trace (Fin.castLE S.air.mainNextWidth_le j), ζ * rootOfUnity S.logN, o.traceNext j))

/-- A STARK's opened quotient words: each chunk's coordinates at `ζ`. -/
noncomputable def quotientOpened {S : Iop.Setup EF lookups} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  (List.finRange S.chunks).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.quotient α c e, ζ, (p.openings α ζ).quotientAt c e)

/-- A STARK's opened preprocessed words: the columns at `ζ`, then, if opened, at `ζ ω_n`. -/
noncomputable def preprocessedOpened {S : Iop.Setup EF lookups} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  (List.finRange S.air.preprocessedWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ, o.preprocessedAt j)) ++
  (List.finRange S.air.preprocessedNextWidth).map
    (fun j ↦ (S.preprocessedWord j.val, ζ * rootOfUnity S.logN, o.preprocessedNext j))

/-- A STARK's opened permutation words: each column's coordinates at `ζ`, then at `ζ ω_n`. -/
noncomputable def permOpened {S : Iop.Setup EF lookups} (p : Iop.Prover S) (α ζ : 𝕂) :
    List ((S.Point → F) × 𝕂 × 𝕂) :=
  let o := p.openings α ζ
  ((List.finRange S.permWidth).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.perm c e, ζ, o.permAt c e)) ++
  ((List.finRange S.permWidth).flatMap fun c ↦ (List.finRange (Challenge.d EF)).map fun e ↦
    (p.perm c e, ζ * rootOfUnity S.logN, o.permNext c e))

variable {withLookups : Bool}

/-- Instance `i`'s opened words, read as words on a domain of `2 ^ m` points if its domain has
that size, and none otherwise. -/
def onSize {S : Setup EF withLookups} (i : Fin S.k) (m : ℕ)
    (words : List (((S.instanceSetup i).Point → F) × 𝕂 × 𝕂)) :
    List ((Fin (2 ^ m) → F) × 𝕂 × 𝕂) :=
  if h : S.logN i + S.params.logBlowup = m then
    words.map fun w ↦ (fun x ↦ w.1 (Fin.cast (by rw [h]) x), w.2)
  else []

/-- The opened words of the instances whose domains have `2 ^ m` points, with their points and
claimed values, in Plonky3's batching order: the commitment scheme's rounds, every instance of
that size in each: the main traces, the quotients, the preprocessed traces, the permutation
traces. -/
noncomputable def groupOpened {S : Setup EF withLookups} (p : Prover S)
    (lookupAlpha lookupBeta α ζ : 𝕂) (m : ℕ) : List ((Fin (2 ^ m) → F) × 𝕂 × 𝕂) :=
  let q := p.instanceProver lookupAlpha lookupBeta
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (mainOpened (q i) α ζ)) ++
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (quotientOpened (q i) α ζ)) ++
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (preprocessedOpened (q i) α ζ)) ++
  (List.finRange S.k).flatMap (fun i ↦ onSize i m (permOpened (q i) α ζ))

/-- The batched DEEP word of the domain of `2 ^ m` points `g ⟨ω_m⟩`:
`∑ᵢ aⁱ (yᵢ - fᵢ(x)) / (zᵢ - x)` over its opened words, at each point `x`. -/
noncomputable def groupDeepWord {S : Setup EF withLookups} (p : Prover S)
    (lookupAlpha lookupBeta α ζ a : 𝕂) (m : ℕ) (x : Fin (2 ^ m)) : 𝕂 :=
  ((groupOpened p lookupAlpha lookupBeta α ζ m).zipIdx.map fun ((f, z, y), k) ↦
    a ^ k * (y - algebraMap F 𝕂 (f x)) / (z - lift (basePoint m x))).sum

open Classical in
/-- The probability that the verifier accepts `prover` at the lookup challenges `(α_L, β_L)`:
over uniform `α`, `ζ` and `a`, the terminals of the instances with lookups sum to zero, every
instance's constraints hold at `ζ` and FRI accepts the batched DEEP words, the tallest as FRI's
word and the shorter ones injected. -/
noncomputable def acceptanceAt {S : Setup EF withLookups} (publicValues : Fin S.k → List F)
    (prover : Prover S) (lookupAlpha lookupBeta : 𝕂) : ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 3 * ∑ α : 𝕂, ∑ ζ : 𝕂, ∑ a : 𝕂,
    if (∑ i with S.lookups i ≠ [], prover.terminal lookupAlpha lookupBeta i) = 0 ∧
      ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ
        (prover.openings lookupAlpha lookupBeta α ζ i) (S.challenges lookupAlpha lookupBeta i)
        (prover.terminal lookupAlpha lookupBeta i)
    then friAcceptanceWith S.domainSetup (groupDeepWord prover lookupAlpha lookupBeta α ζ a)
      S.friHeights (groupDeepWord prover lookupAlpha lookupBeta α ζ a _) else 0

/-- The probability that the verifier accepts `prover`: over uniform lookup challenges
`(α_L, β_L)`, the probability that it accepts there (`acceptanceAt`). -/
noncomputable def acceptance {S : Setup EF withLookups} (publicValues : Fin S.k → List F)
    (prover : Prover S) : ENNReal :=
  (Fintype.card 𝕂 : ENNReal)⁻¹ ^ 2 * ∑ lookupAlpha : 𝕂, ∑ lookupBeta : 𝕂,
    acceptanceAt publicValues prover lookupAlpha lookupBeta

/-! ### The relation -/

/-- The batch's lookup messages on the traces `traces` with the public values `publicValues`: for
every instance, row, lookup and tuple in turn, the lookup's bus (as `busIds` numbers the buses)
with the tuple's values on the row (`generationRow`), and the tuple's multiplicity there
(`Batch.messages`). -/
def Setup.messages (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : List ((Nat × List F) × F) :=
  ((List.finRange S.k).zip (busIds (List.ofFn S.lookups))).flatMap fun (i, ids) ↦
    (List.range (2 ^ S.logN i)).flatMap fun r ↦
      ((S.lookups i).zip ids).flatMap fun (l, b) ↦ l.tuples.map fun (es, m) ↦
        ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
          m.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))

/-- Every bus balances: for every bus and every tuple of values, the multiplicities of its
messages sum to zero in the field, as LogUp checks (`Batch.Balanced`). -/
def Setup.Balanced (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : Prop :=
  ∀ key : Nat × List F,
    (((S.messages traces publicValues).filter (·.1 = key)).map (·.2)).sum = 0

/-- The traces satisfy the batch: every instance's trace satisfies its AIR, and every bus of the
batch's lookups balances. -/
structure Setup.Satisfied (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : Prop where
  air : ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)
  balanced : S.Balanced traces publicValues

/-- The verifier's multiplicity bound `∑ᵢ wᵢ 2 ^ logNᵢ < p` (`heightBoundOk`), `wᵢ` the sum of
instance `i`'s count weights: the verifier rejects every proof for a batch that fails it. -/
def Setup.HeightBounded (S : Setup EF withLookups) : Prop :=
  heightBoundOk (CompPoly.CanonicalNat.bound F) (List.ofFn fun i ↦ (S.lookups i, S.logN i)) = true

/-- The batch's queries: its messages (`messages`) of the tuples of positive weight. -/
def Setup.queries (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : List ((Nat × List F) × F) :=
  ((List.finRange S.k).zip (busIds (List.ofFn S.lookups))).flatMap fun (i, ids) ↦
    (List.range (2 ^ S.logN i)).flatMap fun r ↦
      ((S.lookups i).zip ids).flatMap fun (l, b) ↦
        (l.entries.filter (0 < ·.2.weight)).map fun (es, c) ↦
          ((b, es.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))),
            c.expr.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r))

/-- Row `r` of instance `i` provides the tuple of values `key.2` on the bus `key.1`: a tuple of
weight `0` of one of the instance's lookups on that bus has these values on the row and a
nonzero multiplicity there. -/
def Setup.Provides (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) (key : Nat × List F) (i : Fin S.k) (r : Nat) : Prop :=
  r < 2 ^ S.logN i ∧
    ∃ lb ∈ (S.lookups i).zip ((busIds (List.ofFn S.lookups)).getD i []), lb.2 = key.1 ∧
      ∃ t ∈ lb.1.entries, t.2.weight = 0 ∧
        t.1.map (·.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r)) =
          key.2 ∧
        t.2.expr.eval (generationRow (S.air i) (S.logN i) (traces i) (publicValues i) r) ≠ 0

/-- Every bus's queries are included in what is provided: for every bus and tuple of values,
some row of some instance provides it (`Provides`), or the multiplicities of its queries, read as
the integers of magnitude below `p / 2` they stand for (`intValue`), sum to zero. -/
def Setup.Included (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : Prop :=
  ∀ key : Nat × List F, (∃ i r, S.Provides traces publicValues key i r) ∨
    (((S.queries traces publicValues).filter (·.1 = key)).map (intValue ·.2)).sum = 0

/-- The traces satisfy the batch with lookup inclusion: every instance's trace satisfies its AIR,
and every bus's queries are included in what is provided (`Included`). -/
structure Setup.SatisfiedWithInclusion (S : Setup EF withLookups) (traces : Fin S.k → Array F)
    (publicValues : Fin S.k → List F) : Prop where
  air : ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i)
  included : S.Included traces publicValues

/-- The AIR keeps its queries' multiplicities within their weights on traces of `2 ^ logN` rows:
on every row of every trace satisfying it, its multiplicities of positive weight, read as the
integers of magnitude below `p / 2` they stand for, have magnitudes summing to at most its
lookups' count weights. The verifier does not check it: it trusts the weights. -/
def _root_.CompStark.Stark.Air.CountsBounded (A : Air F) (logN : Nat) : Prop :=
  ∀ trace publicValues, A.Satisfied logN trace publicValues → ∀ r < 2 ^ logN,
    (((A.lookups.flatMap (·.entries)).filter (0 < ·.2.weight)).map fun t ↦
      (intValue (t.2.expr.eval (generationRow A logN trace publicValues r))).natAbs).sum ≤
    (A.lookups.map (·.countWeight)).sum

/-! ### The extractor: list decoding -/

/-- The tuples of traces the extractor reads off the committed trace words at proximity `δ`: one
trace per instance, each of `Iop.closeTraces`. -/
def closeTraces (S : Setup EF withLookups) (δ : ℝ)
    (words : (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F) :
    Set (Fin S.k → Array F) :=
  {traces | ∀ i, traces i ∈ Iop.closeTraces (S.instanceSetup i) δ (words i)}

end Batch

/-! ### A STARK is a batch of one instance -/

/-- A STARK as a batch of one instance, without lookups. -/
abbrev Setup.toBatch (S : Iop.Setup EF) : Batch.Setup EF false :=
  ⟨S.params, 1, fun _ ↦ S.air, fun _ ↦ S.logN, fun _ ↦ S.valid, fun _ ↦ S.folds, Nat.one_pos,
    fun _ ↦ trivial, ⟨fun _ hl ↦ absurd hl List.not_mem_nil, fun _ hx ↦ absurd hx List.not_mem_nil,
      fun _ hx ↦ absurd hx List.not_mem_nil⟩⟩

/-- A STARK prover as a prover of a batch of one instance. -/
abbrev Prover.toBatch {S : Iop.Setup EF} (p : Iop.Prover S) : Batch.Prover S.toBatch :=
  ⟨fun _ ↦ p.trace, fun _ _ _ ↦ p.perm, fun _ _ _ ↦ 0, fun _ _ α _ ↦ p.quotient α,
    fun _ _ α ζ _ ↦ p.openings α ζ⟩

end CompStark.Iop
