/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Fri
public import CompStark.Interaction.Execution

/-! # The STARK on ArkLib's interaction layer

The STARK as an interactive oracle protocol on ArkLib's interaction layer, for a statement `C`
(FRI parameters and an AIR) and public values. The prover's first move is the trace length
`2 ^ n`, a public message the verifier admits (`Statement.Length`); every later shape is the one
of the STARK at that length (`Statement.setup`):

1. The prover sends the extended trace as an oracle (`Setup.TraceMessage`): each column's values
   on the domain `L` of `2 ^ (n + logBlowup)` points.
2. The verifier samples the constraint-folding challenge `α`.
3. The prover sends the quotient's chunks as an oracle (`Setup.QuotientMessage`), each as the
   coordinates of a word over `𝕂`.
4. The verifier samples the out-of-domain point `ζ`.
5. The prover sends the claimed values at `ζ` (`Openings`) in the clear.
6. The verifier samples the batching challenge `a`.
7. FRI runs on the batched DEEP word (`deepWord`), ArkLib's FRI on the interaction layer
   (`Fri.Interaction.protocol`) along Plonky3's schedule (`Setup.friSchedule`).

The verifier (`Setup.verifier`) never reads a word: FRI's verifier reads the DEEP word at a point
through a query program (`Setup.deepReader`) that queries the trace's and the chunks' values
there and evaluates the DEEP quotients on the opened values. It accepts if the constraints hold
at `ζ` (`ConstraintsHoldAt`) and FRI accepts.

An `Iop.Prover`, the prover's words and messages as functions of the challenges before them,
plays the protocol (`Prover.strategy`), with FRI's honest prover on its DEEP word; it is accepted
whenever its claimed values pass the check at `ζ` and its DEEP word has low degree
(`Prover.strategy_accepts`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound _root_.Interaction _root_.Interaction.Oracle OracleComp
open OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### The messages -/

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- The extended trace as an oracle message: column `j` at the point `x` of `L`. -/
abbrev TraceMessage : Type := Fin S.air.width × S.Point → F

/-- The quotient's chunks as an oracle message: coordinate `e` of chunk `c` at the point `x`. -/
abbrev QuotientMessage : Type := (Fin S.chunks × Fin (Challenge.d EF)) × S.Point → F

/-- The trace words of a trace message. -/
def traceWords (T : S.TraceMessage) : Fin S.air.width → S.Point → F := fun j x ↦ T (j, x)

/-- The quotient words of a quotient message. -/
def quotientWords (Q : S.QuotientMessage) : Fin S.chunks → Fin (Challenge.d EF) → S.Point → F :=
  fun c e x ↦ Q ((c, e), x)

/-- FRI on `L` along Plonky3's schedule, injecting the words of the log sizes `heights`, with a
final polynomial of `2 ^ logFinalPolyLen` coefficients and `numQueries` queries. -/
def friProtocol (heights : List ℕ) : Protocol :=
  Fri.Interaction.protocol 𝕂 (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries (S.friSchedule heights)

/-- After the claimed values: the batching challenge `a`, then FRI on the DEEP word. -/
def afterOpenings : Protocol := .public .receiver 𝕂 fun _ ↦ S.friProtocol []

/-- After `ζ`: the claimed values in the clear. -/
def afterZeta : Protocol := .public .sender (Openings S) fun _ ↦ S.afterOpenings

/-- After the quotient: the out-of-domain point `ζ`. -/
def afterQuotient : Protocol := .public .receiver 𝕂 fun _ ↦ S.afterZeta

/-- After `α`: the quotient's chunks as an oracle. -/
def afterAlpha : Protocol := .oracle S.QuotientMessage S.afterQuotient

/-- After the trace: the constraint-folding challenge `α`. -/
def afterTrace : Protocol := .public .receiver 𝕂 fun _ ↦ S.afterAlpha

/-- The STARK at a length: the trace, `α`, the quotient, `ζ`, the claimed values, `a`, and FRI on
the DEEP word. -/
def protocol : Protocol := .oracle S.TraceMessage S.afterTrace

end Setup

namespace Statement
variable (C : Statement F)

/-- The trace lengths `2 ^ n` the verifier admits, the prover's first move. -/
abbrev Length : Type := {n : ℕ // C.Admits n}

/-- The STARK at an admitted length. -/
abbrev setup (EF : Type) [Challenge F EF] (n : C.Length) : Setup EF := C.setupAt EF n.1 n.2

/-- The STARK for a statement: the prover sends an admitted trace length, then they run the STARK
at that length. -/
def protocol (EF : Type) [Challenge F EF] : Protocol :=
  .public .sender C.Length fun n ↦ (C.setup EF n).protocol

end Statement

/-! ### The verifier -/

/-- The verifier's own oracles: none. -/
abbrev noAccess : PFunctor := 0

/-- The behavior of no oracles. -/
def noImpl : QueryImpl (OracleSpec.ofPFunctor noAccess) Id := fun q ↦ PEmpty.elim q

namespace Setup
variable (S : Setup EF)

/-- The access after the trace message. -/
abbrev traceAccess : PFunctor :=
  Access.extend noAccess (OracleInterface.instFunction (α := Fin S.air.width × S.Point) (β := F))

/-- The access after the quotient message. -/
abbrev quotientAccess : PFunctor :=
  Access.extend S.traceAccess
    (OracleInterface.instFunction (α := (Fin S.chunks × Fin (Challenge.d EF)) × S.Point) (β := F))

/-- The program reading the trace's value of column `j` at `x`, after the quotient. -/
def readTrace (j : Fin S.air.width) (x : S.Point) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) F :=
  Fri.Interaction.extendAccess _ (Access.queryLatest noAccess _ (j, x))

/-- The program reading coordinate `e` of chunk `c` at `x`. -/
def readQuotient (c : Fin S.chunks) (e : Fin (Challenge.d EF)) (x : S.Point) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) F :=
  Access.queryLatest S.traceAccess _ ((c, e), x)

/-- The program evaluating the DEEP word at `x`: it reads the trace's and the chunks' values at
`x` and evaluates the DEEP quotients on them and on the claimed values `o`. -/
noncomputable def readDeep (α ζ : 𝕂) (o : Openings S) (a : 𝕂) (x : S.Point) :
    OracleComp (OracleSpec.ofPFunctor S.quotientAccess) 𝕂 := do
  let tv ← Fri.Interaction.readAll S.air.width fun j ↦ S.readTrace j x
  let qv ← Fri.Interaction.readAll S.chunks fun c ↦
    Fri.Interaction.readAll (Challenge.d EF) fun e ↦ S.readQuotient c e x
  return deepWord (⟨fun j _ ↦ tv j, fun _ c e _ ↦ qv c e, fun _ _ ↦ o, fun _ _ _ ↦ 0⟩ : Prover S)
    α ζ a x

/-- FRI's inputs on `L`: the DEEP word at `L`'s log size, zero at the others. -/
noncomputable def deepInputs (w : S.Point → 𝕂) : (m : ℕ) → Fin (2 ^ m) → 𝕂 :=
  fun m x ↦ if h : m = S.logN + S.params.logBlowup then w (Fin.cast (by rw [h]) x) else 0

/-- FRI's reader of the DEEP word: its input on `L` is the DEEP word, read by `readDeep`. -/
noncomputable def deepReader (α ζ : 𝕂) (o : Openings S) (a : 𝕂) :
    Fri.Interaction.Reader (K := 𝕂) (S.logN + S.params.logBlowup) S.quotientAccess
      (S.logN + S.params.logBlowup) where
  input m x := if h : m = S.logN + S.params.logBlowup then
      S.readDeep α ζ o a (Fin.cast (by rw [h]) x) else pure 0
  word x := S.readDeep α ζ o a x
  check _ := pure true

variable (publicValues : List F)

/-- FRI's verifier on the DEEP word, accepting only if the constraints hold at `ζ` as well. -/
noncomputable def friVerifier (α ζ : 𝕂) (o : Openings S) (a : 𝕂) :
    Verifier.Strategy unifSpec (S.friProtocol []).tree (S.friProtocol []).roles
      (S.friProtocol []).oracles S.quotientAccess (fun _ ↦ Bool) :=
  open Classical in
  Verifier.Fragment.mapOutput unifSpec
    (fun _ act ↦ (fun b ↦ decide (ConstraintsHoldAt S publicValues α ζ o) && b) <$> act)
    (Fri.Interaction.verifier unifSpec (S.logN + S.params.logBlowup)
      (2 ^ S.params.logFinalPolyLen) S.params.numQueries ($ᵗ 𝕂)
      ($ᵗ (Fin S.params.numQueries → Fin (2 ^ (S.logN + S.params.logBlowup))))
      S.domain S.quotientAccess (S.deepReader α ζ o a) (S.friSchedule []))

/-- The verifier after the claimed values: it samples `a` and runs FRI's verifier. -/
noncomputable def verifierAfterOpenings (α ζ : 𝕂) (o : Openings S) :
    Verifier.Strategy unifSpec S.afterOpenings.tree S.afterOpenings.roles S.afterOpenings.oracles
      S.quotientAccess (fun _ ↦ Bool) := do
  let a ← liftComp ($ᵗ 𝕂) _
  return ⟨a, S.friVerifier publicValues α ζ o a⟩

/-- The verifier after `ζ`: it receives the claimed values. -/
noncomputable def verifierAfterZeta (α ζ : 𝕂) :
    Verifier.Strategy unifSpec S.afterZeta.tree S.afterZeta.roles S.afterZeta.oracles
      S.quotientAccess (fun _ ↦ Bool) :=
  fun o ↦ pure (S.verifierAfterOpenings publicValues α ζ o)

/-- The verifier after the quotient: it samples `ζ`. -/
noncomputable def verifierAfterQuotient (α : 𝕂) :
    Verifier.Strategy unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess (fun _ ↦ Bool) := do
  let ζ ← liftComp ($ᵗ 𝕂) _
  return ⟨ζ, S.verifierAfterZeta publicValues α ζ⟩

/-- The verifier after `α`: it receives the quotient. -/
noncomputable def verifierAfterAlpha (α : 𝕂) :
    Verifier.Strategy unifSpec S.afterAlpha.tree S.afterAlpha.roles S.afterAlpha.oracles
      S.traceAccess (fun _ ↦ Bool) :=
  pure (S.verifierAfterQuotient publicValues α)

/-- The verifier after the trace: it samples `α`. -/
noncomputable def verifierAfterTrace :
    Verifier.Strategy unifSpec S.afterTrace.tree S.afterTrace.roles S.afterTrace.oracles
      S.traceAccess (fun _ ↦ Bool) := do
  let α ← liftComp ($ᵗ 𝕂) _
  return ⟨α, S.verifierAfterAlpha publicValues α⟩

/-- The STARK's verifier at a length: it samples `α`, `ζ` and `a` uniformly and runs FRI's
verifier on the DEEP word; it accepts if FRI accepts and the constraints hold at `ζ`. -/
noncomputable def verifier :
    Verifier.Strategy unifSpec S.protocol.tree S.protocol.roles S.protocol.oracles noAccess
      (fun _ ↦ Bool) :=
  pure (S.verifierAfterTrace publicValues)

end Setup

/-- The STARK's verifier for a statement: at the length the prover sends, the STARK's verifier
there. -/
noncomputable def Statement.verifier (C : Statement F) (EF : Type) [Challenge F EF]
    (publicValues : List F) :
    Verifier.Strategy unifSpec (C.protocol EF).tree (C.protocol EF).roles (C.protocol EF).oracles
      noAccess (fun _ ↦ Bool) :=
  fun n ↦ pure ((C.setup EF n).verifier publicValues)


/-! ### Execution -/

namespace Setup
variable (S : Setup EF) (publicValues : List F)

open CompStark.Interaction

section Execution
variable {A : PFunctor} (impl : QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id)

set_option backward.isDefEq.respectTransparency false in
theorem execute_fri (α ζ : 𝕂) (o : Openings S) (a : 𝕂)
    {OutP : (S.friProtocol []).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (S.friProtocol []).tree (S.friProtocol []).roles OutP) :
    open Classical in
    executeStrategies unifSpec (S.friProtocol []).tree (S.friProtocol []).roles
      (S.friProtocol []).oracles S.quotientAccess impl prover
      (S.friVerifier publicValues α ζ o a) =
      (fun result ↦ ⟨result.1, result.2.1,
        decide (ConstraintsHoldAt S publicValues α ζ o) && result.2.2⟩) <$>
      executeStrategies unifSpec (S.friProtocol []).tree (S.friProtocol []).roles
        (S.friProtocol []).oracles S.quotientAccess impl prover
        (Fri.Interaction.verifier unifSpec (S.logN + S.params.logBlowup)
          (2 ^ S.params.logFinalPolyLen) S.params.numQueries ($ᵗ 𝕂)
          ($ᵗ (Fin S.params.numQueries → Fin (2 ^ (S.logN + S.params.logBlowup))))
          S.domain S.quotientAccess (S.deepReader α ζ o a) (S.friSchedule [])) :=
  executeStrategies_mapOutput unifSpec _ _ _ _ impl _ prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterOpenings (α ζ : 𝕂) (o : Openings S)
    {OutP : S.afterOpenings.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.afterOpenings.tree S.afterOpenings.roles OutP) :
    executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
      S.afterOpenings.oracles S.quotientAccess impl prover
      (S.verifierAfterOpenings publicValues α ζ o) = (do
        let a ← $ᵗ 𝕂
        let p ← prover a
        let result ← executeStrategies unifSpec (S.friProtocol []).tree (S.friProtocol []).roles
          (S.friProtocol []).oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨a, path⟩) p (S.friVerifier publicValues α ζ o a)
        return ⟨⟨a, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterZeta (α ζ : 𝕂) {OutP : S.afterZeta.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.afterZeta.tree S.afterZeta.roles OutP) :
    executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles S.afterZeta.oracles
      S.quotientAccess impl prover (S.verifierAfterZeta publicValues α ζ) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterOpenings.tree S.afterOpenings.roles
          S.afterOpenings.oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterOpenings publicValues α ζ chosen.1)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receive unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterQuotient (α : 𝕂) {OutP : S.afterQuotient.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.afterQuotient.tree S.afterQuotient.roles OutP) :
    executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
      S.afterQuotient.oracles S.quotientAccess impl prover
      (S.verifierAfterQuotient publicValues α) = (do
        let ζ ← $ᵗ 𝕂
        let p ← prover ζ
        let result ← executeStrategies unifSpec S.afterZeta.tree S.afterZeta.roles
          S.afterZeta.oracles S.quotientAccess impl
          (OutP := fun path ↦ OutP ⟨ζ, path⟩) p (S.verifierAfterZeta publicValues α ζ)
        return ⟨⟨ζ, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterAlpha (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id) (α : 𝕂)
    {OutP : S.afterAlpha.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.afterAlpha.tree S.afterAlpha.roles OutP) :
    executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles S.afterAlpha.oracles
      S.traceAccess impl prover (S.verifierAfterAlpha publicValues α) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterQuotient.tree S.afterQuotient.roles
          S.afterQuotient.oracles S.quotientAccess
          (Access.extendImpl S.traceAccess OracleInterface.instFunction impl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2
          (S.verifierAfterQuotient publicValues α)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receiveOracle unifSpec _ _ _ impl prover _

set_option backward.isDefEq.respectTransparency false in
theorem execute_afterTrace (impl : QueryImpl (OracleSpec.ofPFunctor S.traceAccess) Id)
    {OutP : S.afterTrace.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.afterTrace.tree S.afterTrace.roles OutP) :
    executeStrategies unifSpec S.afterTrace.tree S.afterTrace.roles S.afterTrace.oracles
      S.traceAccess impl prover (S.verifierAfterTrace publicValues) = (do
        let α ← $ᵗ 𝕂
        let p ← prover α
        let result ← executeStrategies unifSpec S.afterAlpha.tree S.afterAlpha.roles
          S.afterAlpha.oracles S.traceAccess impl
          (OutP := fun path ↦ OutP ⟨α, path⟩) p (S.verifierAfterAlpha publicValues α)
        return ⟨⟨α, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_sample unifSpec _ _ _ impl prover _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute_protocol {OutP : S.protocol.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec S.protocol.tree S.protocol.roles OutP) :
    executeStrategies unifSpec S.protocol.tree S.protocol.roles S.protocol.oracles noAccess noImpl
      prover (S.verifier publicValues) = (do
        let chosen ← prover
        let result ← executeStrategies unifSpec S.afterTrace.tree S.afterTrace.roles
          S.afterTrace.oracles S.traceAccess
          (Access.extendImpl noAccess OracleInterface.instFunction noImpl chosen.1)
          (OutP := fun path ↦ OutP ⟨chosen.1, path⟩) chosen.2 (S.verifierAfterTrace publicValues)
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) :=
  executeStrategies_receiveOracle unifSpec _ _ _ noImpl prover _

end Execution

end Setup

/-! ### The DEEP word at a point -/

section Deep
variable {lookups : List (Lookup F)} {S : Setup EF lookups}

/-- The DEEP word at a point `x` is `∑ₖ aᵏ (yₖ - vₖ) / (zₖ - x)` over the opened words' values `vₖ`
at `x`, their points `zₖ` and their claimed values `yₖ`. -/
theorem deepWord_eq_values (p : Prover S) (α ζ a : 𝕂) (x : S.Point) :
    deepWord p α ζ a x = (((openedWords p α ζ).map fun w ↦ (w.1 x, w.2)).zipIdx.map
      fun ((v, z, y), k) ↦ a ^ k * (y - algebraMap F 𝕂 v) / (z - S.domain x)).sum := by
  rw [deepWord, List.zipIdx_map, List.map_map]
  rfl

/-- The DEEP word at a point reads the prover's words only there. -/
theorem deepWord_congr_at (p p' : Prover S) (α ζ a : 𝕂) (x : S.Point)
    (htrace : ∀ j, p.trace j x = p'.trace j x)
    (hquotient : ∀ c e, p.quotient α c e x = p'.quotient α c e x)
    (hopenings : p.openings α ζ = p'.openings α ζ) (hperm : ∀ c e, p.perm c e x = p'.perm c e x) :
    deepWord p α ζ a x = deepWord p' α ζ a x := by
  rw [deepWord_eq_values, deepWord_eq_values]
  congr 3
  simp only [openedWords, List.map_append, List.map_map, List.map_flatMap, Function.comp_def,
    htrace, hquotient, hopenings, hperm]

end Deep

namespace Setup
variable (S : Setup EF)

/-- The prover of a trace message, a quotient message and claimed values. -/
def messageProver (T : S.TraceMessage) (Q : S.QuotientMessage) (o : Openings S) : Prover S :=
  ⟨S.traceWords T, fun _ ↦ S.quotientWords Q, fun _ _ ↦ o, fun _ _ _ ↦ 0⟩

/-- The behavior of the trace message and the quotient message. -/
def messagesImpl (T : S.TraceMessage) (Q : S.QuotientMessage) :
    QueryImpl (OracleSpec.ofPFunctor S.quotientAccess) Id :=
  Access.extendImpl S.traceAccess OracleInterface.instFunction
    (Access.extendImpl noAccess OracleInterface.instFunction noImpl T) Q

/-- `readDeep` evaluates the DEEP word of the messages. -/
theorem simulateQ_readDeep (T : S.TraceMessage) (Q : S.QuotientMessage) (α ζ : 𝕂)
    (o : Openings S) (a : 𝕂) (x : S.Point) :
    simulateQ (S.messagesImpl T Q) (S.readDeep α ζ o a x) =
      deepWord (S.messageProver T Q o) α ζ a x := by
  simp only [readDeep, simulateQ_bind, simulateQ_pure]
  rw [Fri.Interaction.simulateQ_readAll (S.messagesImpl T Q) _ _ (fun j ↦ T (j, x)) fun j ↦ by
      simp only [readTrace, messagesImpl]
      rfl,
    Fri.Interaction.simulateQ_readAll (S.messagesImpl T Q) _ _ (fun c e ↦ Q ((c, e), x))
      fun c ↦ Fri.Interaction.simulateQ_readAll (S.messagesImpl T Q) _ _ _ fun e ↦ by
        simp only [readQuotient, messagesImpl]
        rfl]
  exact deepWord_congr_at _ _ α ζ a x (fun _ ↦ rfl) (fun _ _ ↦ rfl) rfl fun c ↦ c.elim0

/-- FRI's reader reads the DEEP word of the messages. -/
theorem reads_deepReader (T : S.TraceMessage) (Q : S.QuotientMessage) (α ζ : 𝕂)
    (o : Openings S) (a : 𝕂) :
    (S.deepReader α ζ o a).Reads (S.messagesImpl T Q)
      (S.deepInputs (deepWord (S.messageProver T Q o) α ζ a))
      (deepWord (S.messageProver T Q o) α ζ a) where
  input m x := by
    by_cases h : m = S.logN + S.params.logBlowup
    · subst h
      simp only [deepReader, deepInputs, dite_true, Fin.cast_eq_self]
      exact S.simulateQ_readDeep T Q α ζ o a x
    · simp only [deepReader, deepInputs, h, dite_false, simulateQ_pure]
      rfl
  word x := S.simulateQ_readDeep T Q α ζ o a x

end Setup

/-! ### Provers -/

/-- The strategy of a prover's words and messages, as functions of the challenges before them:
it sends them, and runs FRI's honest prover on its DEEP word. -/
noncomputable def Prover.strategy {S : Setup EF} (p : Prover S) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec S.protocol.tree S.protocol.roles (fun _ ↦ Unit) :=
  pure ⟨fun x ↦ p.trace x.1 x.2, fun α ↦ pure (pure ⟨fun x ↦ p.quotient α x.1.1 x.1.2 x.2,
    fun ζ ↦ pure (pure ⟨p.openings α ζ, fun a ↦ pure
      (Fri.Interaction.honestProver unifSpec (S.logN + S.params.logBlowup)
        (2 ^ S.params.logFinalPolyLen) S.params.numQueries (S.deepInputs (deepWord p α ζ a))
        S.domain (deepWord p α ζ a) (S.friSchedule []))⟩)⟩)⟩

/-- The strategy of a statement's prover: it sends its trace length and plays its prover there. -/
noncomputable def Statement.Prover.strategy {C : Statement F} (p : C.Prover EF) :
    _root_.Interaction.Oracle.Prover.Strategy unifSpec (C.protocol EF).tree (C.protocol EF).roles
      (fun _ ↦ Unit) :=
  pure ⟨⟨p.logN, p.admits⟩, p.prover.strategy⟩

namespace Setup
variable (S : Setup EF)

/-- The constraint-folding challenge of an execution. -/
def alphaOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.1

/-- The out-of-domain point of an execution. -/
def zetaOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.2.2.1

/-- The batching challenge of an execution. -/
def batchOf (path : S.protocol.tree.ExecutionPath) : 𝕂 := path.2.2.2.2.2.1

end Setup

set_option backward.isDefEq.respectTransparency false in
/-- **Completeness.** A prover's strategy is accepted on every execution where its claimed values
pass the check at `ζ` and its DEEP word is a codeword of degree below `n` on `L`. -/
theorem Prover.strategy_accepts {S : Setup EF} (p : Prover S) (publicValues : List F) :
    ∀ result ∈ support (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl p.strategy (S.verifier publicValues)),
      ConstraintsHoldAt S publicValues (S.alphaOf result.1) (S.zetaOf result.1)
        (p.openings (S.alphaOf result.1) (S.zetaOf result.1)) →
      deepWord p (S.alphaOf result.1) (S.zetaOf result.1) (S.batchOf result.1) ∈
        ReedSolomon.code (S.domain : Fin (2 ^ (S.logN + S.params.logBlowup)) ↪ 𝕂) S.n →
      result.2.2 = true := by
  intro result hres hcheck hcode
  rw [Setup.execute_protocol] at hres
  obtain ⟨chosen, hchosen, hres⟩ := support_bind_exists hres
  rw [Prover.strategy, mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r1, hr1, hres⟩ := support_bind_exists hres
  rw [mem_support_pure_iff] at hres
  subst hres
  rw [Setup.execute_afterTrace] at hr1
  obtain ⟨α, -, hr1⟩ := support_bind_exists hr1
  obtain ⟨p1, hp1, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hp1
  subst hp1
  obtain ⟨r2, hr2, hr1⟩ := support_bind_exists hr1
  rw [mem_support_pure_iff] at hr1
  subst hr1
  rw [Setup.execute_afterAlpha] at hr2
  obtain ⟨chosen, hchosen, hr2⟩ := support_bind_exists hr2
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r3, hr3, hr2⟩ := support_bind_exists hr2
  rw [mem_support_pure_iff] at hr2
  subst hr2
  rw [Setup.execute_afterQuotient] at hr3
  obtain ⟨ζ, -, hr3⟩ := support_bind_exists hr3
  obtain ⟨p2, hp2, hr3⟩ := support_bind_exists hr3
  rw [mem_support_pure_iff] at hp2
  subst hp2
  obtain ⟨r4, hr4, hr3⟩ := support_bind_exists hr3
  rw [mem_support_pure_iff] at hr3
  subst hr3
  rw [Setup.execute_afterZeta] at hr4
  obtain ⟨chosen, hchosen, hr4⟩ := support_bind_exists hr4
  rw [mem_support_pure_iff] at hchosen
  subst hchosen
  obtain ⟨r5, hr5, hr4⟩ := support_bind_exists hr4
  rw [mem_support_pure_iff] at hr4
  subst hr4
  rw [Setup.execute_afterOpenings] at hr5
  obtain ⟨a, -, hr5⟩ := support_bind_exists hr5
  obtain ⟨p3, hp3, hr5⟩ := support_bind_exists hr5
  rw [mem_support_pure_iff] at hp3
  subst hp3
  obtain ⟨r6, hr6, hr5⟩ := support_bind_exists hr5
  rw [mem_support_pure_iff] at hr5
  subst hr5
  rw [Setup.execute_fri, support_map] at hr6
  obtain ⟨r7, hr7, rfl⟩ := hr6
  change ConstraintsHoldAt S publicValues α ζ (p.openings α ζ) at hcheck
  change deepWord p α ζ a ∈ _ at hcode
  have hw : deepWord (S.messageProver (fun x ↦ p.trace x.1 x.2)
      (fun x ↦ p.quotient α x.1.1 x.1.2 x.2) (p.openings α ζ)) α ζ a = deepWord p α ζ a :=
    funext fun x ↦ deepWord_congr_at _ _ α ζ a x (fun _ ↦ rfl) (fun _ _ ↦ rfl) rfl
      fun c ↦ c.elim0
  have hreads := S.reads_deepReader (fun x ↦ p.trace x.1 x.2)
    (fun x ↦ p.quotient α x.1.1 x.1.2 x.2) α ζ (p.openings α ζ) a
  rw [hw] at hreads
  have hacc := Fri.Interaction.honest_accepts unifSpec (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries _ _ (S.deepInputs (deepWord p α ζ a))
    (Nat.two_pow_pos _) (S.friSchedule []) S.domain _ _ _ _
    (S.arityPos_friSchedule [] (Fri.Interaction.Schedule.fits_nil _ _))
    (inputsInCode_plonky3_nil _ _ _ _ _ _ _)
    (by rwa [S.degree_friSchedule [] (Fri.Interaction.Schedule.fits_nil _ _)]) hreads
    (fun _ ↦ rfl) r7 hr7
  change (@decide _ (Classical.propDecidable _) && r7.2.2) = true
  rw [hacc, Bool.and_true]
  exact @decide_eq_true _ (Classical.propDecidable _) hcheck

namespace Statement
variable (C : Statement F) (EF : Type) [Challenge F EF] (publicValues : List F)

set_option backward.isDefEq.respectTransparency false in
theorem execute_protocol {OutP : (C.protocol EF).tree.ExecutionPath → Type}
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
  CompStark.Interaction.executeStrategies_receive unifSpec _ _ _ noImpl prover _

end Statement

end CompStark.Iop
