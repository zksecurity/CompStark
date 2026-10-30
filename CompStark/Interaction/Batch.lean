/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Stark
public import CompStark.BatchSoundnessError

/-! # The batch STARK on ArkLib's interaction layer

The batch STARK as an interactive oracle protocol on ArkLib's interaction layer, for a batch
statement `C` (FRI parameters, the AIRs and their keygen heights) and public values. The prover's
first move is the vector of trace lengths, a public message the verifier admits
(`Statement.Length`); every later shape is the one of the batch at those lengths
(`Statement.setup`). The rounds are the STARK's, every instance in each, after a round for the
lookups:

1. The prover sends every instance's extended trace as one oracle (`Setup.TraceMessage`).
2. The verifier samples the lookup challenges `(α_L, β_L)`.
3. The prover sends every instance's extended permutation trace as one oracle
   (`Setup.PermMessage`), then every instance's terminal in the clear.
4. The verifier samples the constraint-folding challenge `α`.
5. The prover sends every instance's quotient chunks as one oracle (`Setup.QuotientMessage`).
6. The verifier samples the out-of-domain point `ζ`.
7. The prover sends every instance's claimed values in the clear.
8. The verifier samples the batching challenge `a`.
9. FRI runs on the tallest domain's batched DEEP word, injecting the shorter domains' batched
   DEEP words (`groupDeepWord`) when its folds reach them: ArkLib's FRI on the interaction layer
   along Plonky3's schedule (`Setup.friProtocol`), on the tallest domain's subgroup `⟨ω⟩` as
   Plonky3 runs it. A fold by `2 ^ k` at `β` adds `β ^ 2 ^ k` times the injected word, Plonky3's
   roll-in of a reduced opening.

FRI's verifier reads a batched DEEP word at a point through a query program
(`Setup.readGroupDeep`) that queries the trace's, the permutation trace's and the chunks' values
there of the instances of that domain size. The verifier accepts if the terminals of the instances
with lookups sum to zero, every instance's constraints hold at `ζ` and FRI accepts.
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound CompStark.Interaction _root_.Interaction
open _root_.Interaction.Oracle OracleComp OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The messages -/

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

/-- Every instance's extended trace as one oracle message: column `j` of instance `i` at the point
`x` of its domain. -/
abbrev TraceMessage : Type :=
  ((i : Fin S.k) × (Fin (S.air i).width × (S.instanceSetup i).Point)) → F

/-- Every instance's extended permutation trace as one oracle message: coordinate `e` of column
`c` of instance `i` at the point `x`. -/
abbrev PermMessage : Type :=
  ((i : Fin S.k) × ((Fin (S.instanceSetup i).permWidth × Fin (Challenge.d EF)) ×
    (S.instanceSetup i).Point)) → F

/-- Every instance's quotient chunks as one oracle message: coordinate `e` of chunk `c` of
instance `i` at the point `x`. -/
abbrev QuotientMessage : Type :=
  ((i : Fin S.k) × ((Fin (S.instanceSetup i).chunks × Fin (Challenge.d EF)) ×
    (S.instanceSetup i).Point)) → F

/-- Every instance's claimed values. -/
abbrev OpeningsMessage : Type := (i : Fin S.k) → Openings (S.instanceSetup i)

/-- The trace words of a trace message. -/
def traceWords (T : S.TraceMessage) :
    (i : Fin S.k) → Fin (S.air i).width → (S.instanceSetup i).Point → F :=
  fun i j x ↦ T ⟨i, j, x⟩

/-- The permutation words of a permutation message. -/
def permWords (P : S.PermMessage) :
    (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F :=
  fun i c e x ↦ P ⟨i, (c, e), x⟩

/-- The quotient words of a quotient message. -/
def quotientWords (Q : S.QuotientMessage) :
    (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) →
      (S.instanceSetup i).Point → F :=
  fun i c e x ↦ Q ⟨i, (c, e), x⟩

/-- The prover of the messages. -/
def messageProver (T : S.TraceMessage) (P : S.PermMessage) (terminals : Fin S.k → 𝕂)
    (Q : S.QuotientMessage) (o : S.OpeningsMessage) : Prover S :=
  ⟨S.traceWords T, fun _ _ ↦ S.permWords P, fun _ _ ↦ terminals, fun _ _ _ ↦ S.quotientWords Q,
    fun _ _ _ _ ↦ o⟩

/-- FRI on the tallest domain along Plonky3's schedule, injecting the shorter domains' words. -/
abbrev friProtocol : Protocol := S.domainSetup.friProtocol S.friHeights

/-- After the claimed values: the batching challenge `a`, then FRI. -/
def afterOpenings : Protocol := .public .receiver 𝕂 fun _ ↦ S.friProtocol

/-- After `ζ`: every instance's claimed values in the clear. -/
def afterZeta : Protocol := .public .sender S.OpeningsMessage fun _ ↦ S.afterOpenings

/-- After the quotient: the out-of-domain point `ζ`. -/
def afterQuotient : Protocol := .public .receiver 𝕂 fun _ ↦ S.afterZeta

/-- After `α`: every instance's quotient chunks as an oracle. -/
def afterAlpha : Protocol := .oracle S.QuotientMessage S.afterQuotient

/-- After the terminals: the constraint-folding challenge `α`. -/
def afterTerminals : Protocol := .public .receiver 𝕂 fun _ ↦ S.afterAlpha

/-- After the permutation traces: every instance's terminal in the clear. -/
def afterPerm : Protocol := .public .sender (Fin S.k → 𝕂) fun _ ↦ S.afterTerminals

/-- After the lookup challenges: every instance's permutation trace as an oracle. -/
def afterLookup : Protocol := .oracle S.PermMessage S.afterPerm

/-- After the traces: the lookup challenges `(α_L, β_L)`. -/
def afterTrace : Protocol := .public .receiver (𝕂 × 𝕂) fun _ ↦ S.afterLookup

/-- The batch STARK at its lengths. -/
def protocol : Protocol := .oracle S.TraceMessage S.afterTrace

end Setup

namespace Statement
variable (C : Statement F)

/-- The vectors of trace lengths `2 ^ n i` the verifier admits, the prover's first move. -/
abbrev Length : Type := {n : Fin C.k → ℕ // C.Admits n}

/-- The batch at admitted lengths. -/
abbrev setup (EF : Type) [Challenge F EF] (n : C.Length) : Setup EF := C.setupAt EF n.1 n.2

/-- The batch STARK for a statement: the prover sends admitted trace lengths, then they run the
batch at those lengths. -/
def protocol (EF : Type) [Challenge F EF] : Protocol :=
  .public .sender C.Length fun n ↦ (C.setup EF n).protocol

end Statement

/-! ### The verifier -/

/-- Read a value of every index, each of its own type. -/
def readPi {ι : Type} {spec : OracleSpec ι} :
    (m : ℕ) → {β : Fin m → Type} → ((i : Fin m) → OracleComp spec (β i)) →
      OracleComp spec ((i : Fin m) → β i)
  | 0, _, _ => pure fun i ↦ i.elim0
  | m + 1, _, read => do
      let v ← read 0
      let rest ← readPi m fun i ↦ read i.succ
      return Fin.cons v rest

/-- Reading values of every index reads each of them. -/
theorem simulateQ_readPi {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Id) :
    ∀ (m : ℕ) {β : Fin m → Type} (read : (i : Fin m) → OracleComp spec (β i))
      (v : (i : Fin m) → β i), (∀ i, simulateQ impl (read i) = v i) →
      simulateQ impl (readPi m read) = v
  | 0, _, _, v, _ => funext fun i ↦ i.elim0
  | m + 1, _, read, v, h => by
    simp only [readPi, simulateQ_bind, simulateQ_pure, h]
    rw [simulateQ_readPi impl m (fun i ↦ read i.succ) (fun i ↦ v i.succ) (fun i ↦ h i.succ)]
    exact Fin.cons_self_tail v

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

/-- The access after the trace message. -/
abbrev traceAccess : PFunctor :=
  Access.extend noAccess (OracleInterface.instFunction
    (α := (i : Fin S.k) × (Fin (S.air i).width × (S.instanceSetup i).Point)) (β := F))

/-- The access after the permutation message. -/
abbrev permAccess : PFunctor :=
  Access.extend S.traceAccess (OracleInterface.instFunction
    (α := (i : Fin S.k) × ((Fin (S.instanceSetup i).permWidth × Fin (Challenge.d EF)) ×
      (S.instanceSetup i).Point)) (β := F))

/-- The access after the quotient message. -/
abbrev quotientAccess : PFunctor :=
  Access.extend S.permAccess (OracleInterface.instFunction
    (α := (i : Fin S.k) × ((Fin (S.instanceSetup i).chunks × Fin (Challenge.d EF)) ×
      (S.instanceSetup i).Point)) (β := F))

/-- The behavior of the messages. -/
def messagesImpl (T : S.TraceMessage) (P : S.PermMessage) (Q : S.QuotientMessage) :
    QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id :=
  Access.extendImpl S.permAccess OracleInterface.instFunction
    (Access.extendImpl S.traceAccess OracleInterface.instFunction
      (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) P) Q

/-- The program reading instance `i`'s trace column `j` at `x`, after the quotient. -/
def readTrace (i : Fin S.k) (j : Fin (S.air i).width) (x : (S.instanceSetup i).Point) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) F :=
  Fri.Interaction.extendAccess _ (Fri.Interaction.extendAccess _
    (Access.queryLatest noAccess (OracleInterface.instFunction
      (α := (i : Fin S.k) × (Fin (S.air i).width × (S.instanceSetup i).Point)) (β := F))
      ⟨i, j, x⟩))

/-- The program reading coordinate `e` of instance `i`'s permutation column `c` at `x`. -/
def readPerm (i : Fin S.k) (c : Fin (S.instanceSetup i).permWidth) (e : Fin (Challenge.d EF))
    (x : (S.instanceSetup i).Point) : OracleComp (OracleSpec.ofPFunctor S.quotientAccess) F :=
  Fri.Interaction.extendAccess _ (Access.queryLatest S.traceAccess (OracleInterface.instFunction
    (α := (i : Fin S.k) × ((Fin (S.instanceSetup i).permWidth × Fin (Challenge.d EF)) ×
      (S.instanceSetup i).Point)) (β := F)) ⟨i, (c, e), x⟩)

/-- The program reading coordinate `e` of instance `i`'s chunk `c` at `x`. -/
def readQuotient (i : Fin S.k) (c : Fin (S.instanceSetup i).chunks) (e : Fin (Challenge.d EF))
    (x : (S.instanceSetup i).Point) : OracleComp (OracleSpec.ofPFunctor S.quotientAccess) F :=
  Access.queryLatest S.permAccess (OracleInterface.instFunction
    (α := (i : Fin S.k) × ((Fin (S.instanceSetup i).chunks × Fin (Challenge.d EF)) ×
      (S.instanceSetup i).Point)) (β := F)) ⟨i, (c, e), x⟩

/-- The values at a point of the instances of a domain size: every instance's trace, permutation
trace and chunks there if its domain has that size, and zeros otherwise. -/
structure Values where
  trace : (i : Fin S.k) → Fin (S.air i).width → F
  perm : (i : Fin S.k) → Fin (S.instanceSetup i).permWidth → Fin (Challenge.d EF) → F
  quotient : (i : Fin S.k) → Fin (S.instanceSetup i).chunks → Fin (Challenge.d EF) → F

/-- The prover of values at a point, with the claimed values and terminals. -/
def valuesProver (v : S.Values) (terminals : Fin S.k → 𝕂) (o : S.OpeningsMessage) : Prover S :=
  ⟨fun i j _ ↦ v.trace i j, fun _ _ i c e _ ↦ v.perm i c e, fun _ _ ↦ terminals,
    fun _ _ _ i c e _ ↦ v.quotient i c e, fun _ _ _ _ ↦ o⟩

/-- The program reading the values at the point `x` of the domain of `2 ^ m` points. -/
def readValues (m : ℕ) (x : Fin (2 ^ m)) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) S.Values := do
  let tv ← readPi S.k fun i ↦ if h : S.logN i + S.params.logBlowup = m then
    Fri.Interaction.readAll _ fun j ↦ S.readTrace i j (Fin.cast (by rw [h]) x)
    else pure fun _ ↦ 0
  let pv ← readPi S.k fun i ↦ if h : S.logN i + S.params.logBlowup = m then
    Fri.Interaction.readAll _ fun c ↦ Fri.Interaction.readAll _ fun e ↦
      S.readPerm i c e (Fin.cast (by rw [h]) x)
    else pure fun _ _ ↦ 0
  let qv ← readPi S.k fun i ↦ if h : S.logN i + S.params.logBlowup = m then
    Fri.Interaction.readAll _ fun c ↦ Fri.Interaction.readAll _ fun e ↦
      S.readQuotient i c e (Fin.cast (by rw [h]) x)
    else pure fun _ _ ↦ 0
  return ⟨tv, pv, qv⟩

/-- The program evaluating the batched DEEP word of the domain of `2 ^ m` points at `x`. -/
noncomputable def readGroupDeep (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    (o : S.OpeningsMessage) (a : 𝕂) (m : ℕ) (x : Fin (2 ^ m)) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) 𝕂 := do
  let v ← S.readValues m x
  return groupDeepWord (S.valuesProver v terminals o) lα lβ α ζ a m x

/-- FRI's reader of the batched DEEP words. -/
noncomputable def deepReader (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    (o : S.OpeningsMessage) (a : 𝕂) :
    Fri.Interaction.Reader (K := 𝕂) (S.logN S.top + S.params.logBlowup) S.quotientAccess
      (S.logN S.top + S.params.logBlowup) where
  input m x := S.readGroupDeep lα lβ terminals α ζ o a m x
  word x := S.readGroupDeep lα lβ terminals α ζ o a _ x
  check _ := pure true

variable (publicValues : Fin S.k → List F)

/-- The verifier's checks in the clear: the terminals of the instances with lookups sum to zero,
and every instance's constraints hold at `ζ`. -/
def Checks (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂) (o : S.OpeningsMessage) : Prop :=
  (∑ i with S.lookups i ≠ [], terminals i) = 0 ∧
    ∀ i, ConstraintsHoldAt (S.instanceSetup i) (publicValues i) α ζ (o i)
      (S.challenges lα lβ i) (terminals i)

/-- FRI's verifier on the batched DEEP words, accepting only if the checks pass as well. -/
noncomputable def friVerifier (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    (o : S.OpeningsMessage) (a : 𝕂) :
    Verifier.Strategy unifSpec S.friProtocol.tree S.friProtocol.roles S.friProtocol.oracles
      S.quotientAccess (fun _ ↦ Bool) :=
  open Classical in
  Verifier.Fragment.mapOutput unifSpec
    (fun _ act ↦ (fun b ↦ decide (S.Checks publicValues lα lβ terminals α ζ o) && b) <$> act)
    (Fri.Interaction.verifier unifSpec (S.logN S.top + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries ($ᵗ 𝕂)
      ($ᵗ (Fin S.params.numQueries → Fin (2 ^ (S.logN S.top + S.params.logBlowup))))
      S.domainSetup.friDomain S.quotientAccess (S.deepReader lα lβ terminals α ζ o a)
      (S.domainSetup.friSchedule S.friHeights))

/-- The verifier after the claimed values: it samples `a` and runs FRI's verifier. -/
noncomputable def verifierAfterOpenings (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    (o : S.OpeningsMessage) :
    Verifier.Strategy unifSpec S.afterOpenings.tree S.afterOpenings.roles S.afterOpenings.oracles
      S.quotientAccess (fun _ ↦ Bool) := do
  let a ← liftComp ($ᵗ 𝕂) _
  return ⟨a, S.friVerifier publicValues lα lβ terminals α ζ o a⟩

/-- The verifier after `ζ`: it receives the claimed values. -/
noncomputable def verifierAfterZeta (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂) :
    Verifier.Strategy unifSpec S.afterZeta.tree S.afterZeta.roles S.afterZeta.oracles
      S.quotientAccess (fun _ ↦ Bool) :=
  fun o ↦ pure (S.verifierAfterOpenings publicValues lα lβ terminals α ζ o)

/-- The verifier after the quotient: it samples `ζ`. -/
noncomputable def verifierAfterQuotient (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α : 𝕂) :
    Verifier.Strategy unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess (fun _ ↦ Bool) := do
  let ζ ← liftComp ($ᵗ 𝕂) _
  return ⟨ζ, S.verifierAfterZeta publicValues lα lβ terminals α ζ⟩

/-- The verifier after `α`: it receives the quotient. -/
noncomputable def verifierAfterAlpha (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α : 𝕂) :
    Verifier.Strategy unifSpec S.afterAlpha.tree S.afterAlpha.roles S.afterAlpha.oracles
      S.permAccess (fun _ ↦ Bool) :=
  pure (S.verifierAfterQuotient publicValues lα lβ terminals α)

/-- The verifier after the terminals: it samples `α`. -/
noncomputable def verifierAfterTerminals (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) :
    Verifier.Strategy unifSpec S.afterTerminals.tree S.afterTerminals.roles
      S.afterTerminals.oracles S.permAccess (fun _ ↦ Bool) := do
  let α ← liftComp ($ᵗ 𝕂) _
  return ⟨α, S.verifierAfterAlpha publicValues lα lβ terminals α⟩

/-- The verifier after the permutation traces: it receives the terminals. -/
noncomputable def verifierAfterPerm (lα lβ : 𝕂) :
    Verifier.Strategy unifSpec S.afterPerm.tree S.afterPerm.roles S.afterPerm.oracles
      S.permAccess (fun _ ↦ Bool) :=
  fun terminals ↦ pure (S.verifierAfterTerminals publicValues lα lβ terminals)

/-- The verifier after the lookup challenges: it receives the permutation traces. -/
noncomputable def verifierAfterLookup (lα lβ : 𝕂) :
    Verifier.Strategy unifSpec S.afterLookup.tree S.afterLookup.roles S.afterLookup.oracles
      S.traceAccess (fun _ ↦ Bool) :=
  pure (S.verifierAfterPerm publicValues lα lβ)

/-- The verifier after the traces: it samples the lookup challenges. -/
noncomputable def verifierAfterTrace :
    Verifier.Strategy unifSpec S.afterTrace.tree S.afterTrace.roles S.afterTrace.oracles
      S.traceAccess (fun _ ↦ Bool) := do
  let l ← liftComp ($ᵗ (𝕂 × 𝕂)) _
  return ⟨l, S.verifierAfterLookup publicValues l.1 l.2⟩

/-- The batch STARK's verifier at its lengths. -/
noncomputable def verifier :
    Verifier.Strategy unifSpec S.protocol.tree S.protocol.roles S.protocol.oracles noAccess
      (fun _ ↦ Bool) :=
  pure (S.verifierAfterTrace publicValues)

end Setup

/-- The batch STARK's verifier for a statement: at the lengths the prover sends, the batch's
verifier there. -/
noncomputable def Statement.verifier (C : Statement F) (EF : Type) [Challenge F EF]
    (publicValues : Fin C.k → List F) :
    Verifier.Strategy unifSpec (C.protocol EF).tree (C.protocol EF).roles (C.protocol EF).oracles
      noAccess (fun _ ↦ Bool) :=
  fun n ↦ pure ((C.setup EF n).verifier publicValues)

/-! ### The batched DEEP word at a point -/

section Deep
variable {withLookups : Bool} {S : Setup EF withLookups}

/-- The batched DEEP word at a point is `∑ₖ aᵏ (yₖ - vₖ) / (zₖ - x)` over the opened words' values
`vₖ` there. -/
theorem groupDeepWord_eq_values (p : Prover S) (lα lβ α ζ a : 𝕂) (m : ℕ) (x : Fin (2 ^ m)) :
    groupDeepWord p lα lβ α ζ a m x =
      (((groupOpened p lα lβ α ζ m).map fun w ↦ (w.1 x, w.2)).zipIdx.map
        fun ((v, z, y), k) ↦ a ^ k * (y - algebraMap F 𝕂 v) / (z - lift (basePoint m x))).sum := by
  rw [groupDeepWord, List.zipIdx_map, List.map_map]
  rfl

/-- The batched DEEP word at a point reads the provers' words only there, on the instances of its
domain size. -/
theorem groupDeepWord_congr_at (p p' : Prover S) (lα lβ α ζ a : 𝕂) (m : ℕ) (x : Fin (2 ^ m))
    (htrace : ∀ i (hi : S.logN i + S.params.logBlowup = m) j,
      p.trace i j (Fin.cast (by rw [hi]) x) = p'.trace i j (Fin.cast (by rw [hi]) x))
    (hperm : ∀ i (hi : S.logN i + S.params.logBlowup = m) c e,
      p.perm lα lβ i c e (Fin.cast (by rw [hi]) x) = p'.perm lα lβ i c e (Fin.cast (by rw [hi]) x))
    (hquotient : ∀ i (hi : S.logN i + S.params.logBlowup = m) c e,
      p.quotient lα lβ α i c e (Fin.cast (by rw [hi]) x) =
        p'.quotient lα lβ α i c e (Fin.cast (by rw [hi]) x))
    (hopenings : ∀ i, p.openings lα lβ α ζ i = p'.openings lα lβ α ζ i) :
    groupDeepWord p lα lβ α ζ a m x = groupDeepWord p' lα lβ α ζ a m x := by
  rw [groupDeepWord_eq_values, groupDeepWord_eq_values]
  congr 3
  have key (i : Fin S.k) (f : {lookups : List (Stark.Lookup F)} → (T : Iop.Setup EF lookups) →
      Iop.Prover T → 𝕂 → 𝕂 → List ((T.Point → F) × 𝕂 × 𝕂))
      (hf : ∀ hi : S.logN i + S.params.logBlowup = m,
        (f _ (p.instanceProver lα lβ i) α ζ).map (fun w ↦ (w.1 (Fin.cast (by rw [hi]) x), w.2)) =
        (f _ (p'.instanceProver lα lβ i) α ζ).map
          (fun w ↦ (w.1 (Fin.cast (by rw [hi]) x), w.2))) :
      (onSize i m (f _ (p.instanceProver lα lβ i) α ζ)).map (fun w ↦ (w.1 x, w.2)) =
        (onSize i m (f _ (p'.instanceProver lα lβ i) α ζ)).map (fun w ↦ (w.1 x, w.2)) := by
    unfold onSize
    split_ifs with hi
    · simp only [List.map_map, Function.comp_def]
      exact hf hi
    · rfl
  simp only [groupOpened, List.map_append, List.map_flatMap]
  congr 1
  · congr 1
    · congr 1
      · refine List.flatMap_congr fun i _ ↦ key i (fun T q α ζ ↦ mainOpened q α ζ) fun hi ↦ ?_
        simp only [mainOpened, List.map_append, List.map_map, Function.comp_def,
          Prover.instanceProver, htrace i hi, hopenings i]
      · refine List.flatMap_congr fun i _ ↦ key i (fun T q α ζ ↦ quotientOpened q α ζ)
          fun hi ↦ ?_
        simp only [quotientOpened, List.map_flatMap, List.map_map, Function.comp_def,
          Prover.instanceProver, hquotient i hi, hopenings i]
    · refine List.flatMap_congr fun i _ ↦ key i (fun T q α ζ ↦ preprocessedOpened q α ζ)
        fun hi ↦ ?_
      simp only [preprocessedOpened, List.map_append, List.map_map, Function.comp_def,
        Prover.instanceProver, hopenings i]
  · refine List.flatMap_congr fun i _ ↦ key i (fun T q α ζ ↦ permOpened q α ζ) fun hi ↦ ?_
    simp only [permOpened, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
      Prover.instanceProver, hperm i hi, hopenings i]

end Deep

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

/-- The messages' values at the point `x` of the domain of `2 ^ m` points. -/
def valuesAt (T : S.TraceMessage) (P : S.PermMessage) (Q : S.QuotientMessage) (m : ℕ)
    (x : Fin (2 ^ m)) : S.Values where
  trace i := if h : S.logN i + S.params.logBlowup = m then
    fun j ↦ T ⟨i, j, Fin.cast (by rw [h]) x⟩ else fun _ ↦ 0
  perm i := if h : S.logN i + S.params.logBlowup = m then
    fun c e ↦ P ⟨i, (c, e), Fin.cast (by rw [h]) x⟩ else fun _ _ ↦ 0
  quotient i := if h : S.logN i + S.params.logBlowup = m then
    fun c e ↦ Q ⟨i, (c, e), Fin.cast (by rw [h]) x⟩ else fun _ _ ↦ 0

/-- `readValues` reads the messages' values. -/
theorem simulateQ_readValues (T : S.TraceMessage) (P : S.PermMessage) (Q : S.QuotientMessage)
    (m : ℕ) (x : Fin (2 ^ m)) :
    simulateQ (S.messagesImpl T P Q) (S.readValues m x) = S.valuesAt T P Q m x := by
  simp only [readValues, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_readPi (S.messagesImpl T P Q) S.k _ (S.valuesAt T P Q m x).trace fun i ↦ by
      by_cases h : S.logN i + S.params.logBlowup = m
      · simp only [valuesAt, h, dite_true]
        refine Fri.Interaction.simulateQ_readAll _ _ _ _ fun j ↦ ?_
        simp only [readTrace, messagesImpl, Fri.Interaction.simulateQ_extendAccess]
        rfl
      · simp only [valuesAt, h, dite_false, simulateQ_pure]
        rfl,
    simulateQ_readPi (S.messagesImpl T P Q) S.k _ (S.valuesAt T P Q m x).perm fun i ↦ by
      by_cases h : S.logN i + S.params.logBlowup = m
      · simp only [valuesAt, h, dite_true]
        refine Fri.Interaction.simulateQ_readAll _ _ _ _ fun c ↦
          Fri.Interaction.simulateQ_readAll _ _ _ _ fun e ↦ ?_
        simp only [readPerm, messagesImpl]
        rfl
      · simp only [valuesAt, h, dite_false, simulateQ_pure]
        rfl,
    simulateQ_readPi (S.messagesImpl T P Q) S.k _ (S.valuesAt T P Q m x).quotient fun i ↦ by
      by_cases h : S.logN i + S.params.logBlowup = m
      · simp only [valuesAt, h, dite_true]
        refine Fri.Interaction.simulateQ_readAll _ _ _ _ fun c ↦
          Fri.Interaction.simulateQ_readAll _ _ _ _ fun e ↦ ?_
        simp only [readQuotient, messagesImpl]
        rfl
      · simp only [valuesAt, h, dite_false, simulateQ_pure]
        rfl]
  rfl

/-- The batched DEEP words of the messages. -/
noncomputable def deepWords (T : S.TraceMessage) (lα lβ : 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) (m : ℕ) : Fin (2 ^ m) → 𝕂 :=
  groupDeepWord (S.messageProver T P terminals Q o) lα lβ α ζ a m

/-- `readGroupDeep` evaluates the batched DEEP words of the messages. -/
theorem simulateQ_readGroupDeep (T : S.TraceMessage) (lα lβ : 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) (m : ℕ) (x : Fin (2 ^ m)) :
    simulateQ (S.messagesImpl T P Q) (S.readGroupDeep lα lβ terminals α ζ o a m x) =
      S.deepWords T lα lβ P terminals α Q ζ o a m x := by
  simp only [readGroupDeep, simulateQ_bind, simulateQ_pure, simulateQ_readValues]
  refine groupDeepWord_congr_at _ _ lα lβ α ζ a m x (fun i hi j ↦ ?_) (fun i hi c e ↦ ?_)
    (fun i hi c e ↦ ?_) fun _ ↦ rfl
  · simp only [valuesProver, valuesAt, hi, dite_true]
    rfl
  · simp only [valuesProver, valuesAt, hi, dite_true]
    rfl
  · simp only [valuesProver, valuesAt, hi, dite_true]
    rfl

/-- FRI's reader reads the batched DEEP words of the messages. -/
theorem reads_deepReader (T : S.TraceMessage) (lα lβ : 𝕂) (P : S.PermMessage)
    (terminals : Fin S.k → 𝕂) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) :
    (S.deepReader lα lβ terminals α ζ o a).Reads (S.messagesImpl T P Q)
      (S.deepWords T lα lβ P terminals α Q ζ o a)
      (S.deepWords T lα lβ P terminals α Q ζ o a _) where
  input m x := S.simulateQ_readGroupDeep T lα lβ P terminals α Q ζ o a m x
  word x := S.simulateQ_readGroupDeep T lα lβ P terminals α Q ζ o a _ x

/-! ### Execution -/

variable (publicValues : Fin S.k → List F)

section Execution
variable (impl : QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem execute_fri (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂) (o : S.OpeningsMessage)
    (a : 𝕂) {OutP : S.friProtocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.friProtocol.tree
      S.friProtocol.roles OutP) :
    open Classical in
    executeStrategies unifSpec S.friProtocol.tree S.friProtocol.roles S.friProtocol.oracles
      S.quotientAccess impl prover (S.friVerifier publicValues lα lβ terminals α ζ o a) =
      (fun result ↦ ⟨result.1, result.2.1,
        decide (S.Checks publicValues lα lβ terminals α ζ o) && result.2.2⟩) <$>
      executeStrategies unifSpec S.friProtocol.tree S.friProtocol.roles S.friProtocol.oracles
        S.quotientAccess impl prover
        (Fri.Interaction.verifier unifSpec (S.logN S.top + S.params.logBlowup)
          (2 ^ S.params.logFinalPolyLen) S.params.numQueries ($ᵗ 𝕂)
          ($ᵗ (Fin S.params.numQueries → Fin (2 ^ (S.logN S.top + S.params.logBlowup))))
          S.domainSetup.friDomain S.quotientAccess (S.deepReader lα lβ terminals α ζ o a)
          (S.domainSetup.friSchedule S.friHeights)) :=
  executeStrategies_mapOutput unifSpec _ _ _ _ impl _ prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterOpenings (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    (o : S.OpeningsMessage) {OutP : S.afterOpenings.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterOpenings.tree
      S.afterOpenings.roles OutP) :
    executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
      S.afterOpenings.oracles S.quotientAccess impl prover
      (S.verifierAfterOpenings publicValues lα lβ terminals α ζ o) = (do
        let a ← $ᵗ 𝕂
        let p ← prover a
        let result ← executeStrategies unifSpec S.friProtocol.tree S.friProtocol.roles
          S.friProtocol.oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨a, path⟩) p
          (S.friVerifier publicValues lα lβ terminals α ζ o a)
        return ⟨⟨a, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterZeta (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α ζ : 𝕂)
    {OutP : S.afterZeta.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterZeta.tree
      S.afterZeta.roles OutP) :
    executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles S.afterZeta.oracles
      S.quotientAccess impl prover (S.verifierAfterZeta publicValues lα lβ terminals α ζ) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
          S.afterOpenings.oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterOpenings publicValues lα lβ terminals α ζ chosen.1)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receive unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterQuotient (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α : 𝕂)
    {OutP : S.afterQuotient.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterQuotient.tree
      S.afterQuotient.roles OutP) :
    executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess impl prover
      (S.verifierAfterQuotient publicValues lα lβ terminals α) = (do
        let ζ ← $ᵗ 𝕂
        let p ← prover ζ
        let result ← executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles
          S.afterZeta.oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨ζ, path⟩) p
          (S.verifierAfterZeta publicValues lα lβ terminals α ζ)
        return ⟨⟨ζ, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

end Execution

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterAlpha (impl : QueryImpl (OracleSpec.ofPFunctor S.permAccess) Id)
    (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂) (α : 𝕂)
    {OutP : S.afterAlpha.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterAlpha.tree
      S.afterAlpha.roles OutP) :
    executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles S.afterAlpha.oracles
      S.permAccess impl prover (S.verifierAfterAlpha publicValues lα lβ terminals α) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
          S.afterQuotient.oracles S.quotientAccess
          (Access.extendImpl S.permAccess OracleInterface.instFunction impl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterQuotient publicValues lα lβ terminals α)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receiveOracle unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterTerminals (impl : QueryImpl (OracleSpec.ofPFunctor S.permAccess) Id)
    (lα lβ : 𝕂) (terminals : Fin S.k → 𝕂)
    {OutP : S.afterTerminals.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterTerminals.tree
      S.afterTerminals.roles OutP) :
    executeStrategies unifSpec S.afterTerminals.tree S.afterTerminals.roles
      S.afterTerminals.oracles S.permAccess impl prover
      (S.verifierAfterTerminals publicValues lα lβ terminals) = (do
        let α ← $ᵗ 𝕂
        let p ← prover α
        let result ← executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles
          S.afterAlpha.oracles S.permAccess impl
          (OutP := fun path ↦ OutP ⟨α, path⟩) p
          (S.verifierAfterAlpha publicValues lα lβ terminals α)
        return ⟨⟨α, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterPerm (impl : QueryImpl (OracleSpec.ofPFunctor S.permAccess) Id)
    (lα lβ : 𝕂) {OutP : S.afterPerm.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterPerm.tree
      S.afterPerm.roles OutP) :
    executeStrategies unifSpec S.afterPerm.tree S.afterPerm.roles S.afterPerm.oracles
      S.permAccess impl prover (S.verifierAfterPerm publicValues lα lβ) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterTerminals.tree S.afterTerminals.roles
          S.afterTerminals.oracles S.permAccess impl
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterTerminals publicValues lα lβ chosen.1)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receive unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterLookup (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id)
    (lα lβ : 𝕂) {OutP : S.afterLookup.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterLookup.tree
      S.afterLookup.roles OutP) :
    executeStrategies unifSpec S.afterLookup.tree S.afterLookup.roles S.afterLookup.oracles
      S.traceAccess impl prover (S.verifierAfterLookup publicValues lα lβ) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterPerm.tree S.afterPerm.roles
          S.afterPerm.oracles S.permAccess
          (Access.extendImpl S.traceAccess OracleInterface.instFunction impl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterPerm publicValues lα lβ)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receiveOracle unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterTrace (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id)
    {OutP : S.afterTrace.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.afterTrace.tree
      S.afterTrace.roles OutP) :
    executeStrategies unifSpec S.afterTrace.tree S.afterTrace.roles S.afterTrace.oracles
      S.traceAccess impl prover (S.verifierAfterTrace publicValues) = (do
        let l ← $ᵗ (𝕂 × 𝕂)
        let p ← prover l
        let result ← executeStrategies unifSpec S.afterLookup.tree S.afterLookup.roles
          S.afterLookup.oracles S.traceAccess impl
          (OutP := fun path ↦ OutP ⟨l, path⟩) p (S.verifierAfterLookup publicValues l.1 l.2)
        return ⟨⟨l, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_protocol {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree
      S.protocol.roles OutP) :
    executeStrategies unifSpec S.protocol.tree S.protocol.roles S.protocol.oracles noAccess noImpl
      prover (S.verifier publicValues) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterTrace.tree S.afterTrace.roles
          S.afterTrace.oracles S.traceAccess
          (Access.extendImpl noAccess OracleInterface.instFunction noImpl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 (S.verifierAfterTrace publicValues)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receiveOracle unifSpec _ _ _ noImpl prover _

end Setup

set_option backward.isDefEq.respectTransparency false in
theorem Statement.execute_protocol (C : Statement F) (EF : Type) [Challenge F EF]
    (publicValues : Fin C.k → List F) {OutP : (C.protocol EF).tree.ExecutionPath → Type}
    (prover : _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree
      (C.protocol EF).roles OutP) :
    executeStrategies unifSpec (C.protocol EF).tree (C.protocol EF).roles (C.protocol EF).oracles
      noAccess noImpl prover (C.verifier EF publicValues) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec (C.setup EF chosen.1).protocol.tree
          (C.setup EF chosen.1).protocol.roles (C.setup EF chosen.1).protocol.oracles noAccess
          noImpl (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          ((C.setup EF chosen.1).verifier publicValues)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receive unifSpec _ _ _ noImpl prover _

end CompStark.Iop.Batch
