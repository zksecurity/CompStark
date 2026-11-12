/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Presentation

/-! Production WHIR messages and their causal projection to the compressed ideal protocol. -/

set_option autoImplicit false
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section
namespace CompStark.Compiled
open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The two transmitted quadratic coefficients in production order. -/
def quadraticEvents (message : Whir.Quadratic E) : List Transcript.Event :=
  fieldEvents ![message.1, message.2 0]

/-- A nonlast boundary combines residual, OOD and query introductions coefficientwise. -/
def combineQuadratic (residual ood query : Whir.Quadratic E) (lam : E) : Whir.Quadratic E :=
  (residual.1 + lam * ood.1 + lam ^ 2 * query.1,
    fun i => residual.2 i + lam * ood.2 i + lam ^ 2 * query.2 i)

/-- A last boundary combines the residual and query introduction coefficientwise. -/
def combineLastQuadratic (residual query : Whir.Quadratic E) (lam : E) : Whir.Quadratic E :=
  (residual.1 + lam * query.1, fun i => residual.2 i + lam * query.2 i)

/-- Decoding commutes with the nonlast boundary's linear combination. -/
theorem eval_combineQuadratic (residual ood query : Whir.Quadratic E)
    (rClaim oClaim jClaim lam x : E) :
    Whir.evalQuadratic (rClaim + lam * oClaim + lam ^ 2 * jClaim)
      (combineQuadratic residual ood query lam) x =
    Whir.evalQuadratic rClaim residual x + lam * Whir.evalQuadratic oClaim ood x +
      lam ^ 2 * Whir.evalQuadratic jClaim query x := by
  simp only [Whir.evalQuadratic, Sumcheck.compressedOps, combineQuadratic, Fin.sum_univ_one]
  ring

/-- Decoding commutes with the last boundary's linear combination. -/
theorem eval_combineLastQuadratic (residual query : Whir.Quadratic E)
    (rClaim jClaim lam x : E) :
    Whir.evalQuadratic (rClaim + lam * jClaim) (combineLastQuadratic residual query lam) x =
      Whir.evalQuadratic rClaim residual x + lam * Whir.evalQuadratic jClaim query x := by
  simp only [Whir.evalQuadratic, Sumcheck.compressedOps, combineLastQuadratic, Fin.sum_univ_one]
  ring

/-- The production opening has a residual lookahead after folding and a separate OOD intro. -/
def whirWireProtocol : {n : ℕ} → Whir.Schedule K n → Protocol
  | _, .last lanes tail encoding queries => .public .receiver E fun _ =>
      Whir.scalarRounds E lanes (.public .sender (Whir.Quadratic E) fun _ =>
        .public .sender (Whir.Table E tail) fun _ =>
          .public .receiver (Fin queries → encoding.Columns) fun _ =>
            .public .receiver E fun _ => Whir.scalarRounds E tail .done)
  | _, @Whir.Schedule.more _ tail lanes encoding queries rest => .public .receiver E fun _ =>
      Whir.scalarRounds E lanes (.public .sender (Whir.Quadratic E) fun _ =>
        .oracle (Whir.oracleMessage E rest)
          (.public .receiver (Fin tail → E) fun _ =>
            .public .sender E fun _ =>
              .public .sender (Whir.Quadratic E) fun _ =>
                .public .receiver (Fin queries → encoding.Columns) fun _ => whirWireProtocol rest))

/-- Map the first round of a sumcheck block and preserve every later message and challenge. -/
def scalarProjection (first : Whir.Quadratic E → Whir.Quadratic E) : (count : ℕ) →
    Projection (Whir.scalarRounds E count .done) (Whir.scalarRounds E count .done)
  | 0 => .refl _
  | count + 1 => .sender first fun _ => .challenge fun _ => scalarProjection id count

/-- Folding projects its residual lookahead away and retains it for the boundary projection. -/
def foldProjection {source target : Protocol} (first : Whir.Quadratic E → Whir.Quadratic E)
    (next : Whir.Quadratic E → Projection source target) : (count : ℕ) →
      Projection (Whir.scalarRounds E count (.public .sender (Whir.Quadratic E) fun _ => source))
        (Whir.scalarRounds E count target)
  | 0 => .read next
  | count + 1 => .sender first fun _ => .challenge fun _ => foldProjection id next count

/-- The stateful projection combines intros only after the existing batching challenge. -/
def whirProjection : {n : ℕ} → (schedule : Whir.Schedule K n) →
    (E → Whir.Quadratic E → Whir.Quadratic E) →
      Projection (whirWireProtocol schedule) (Whir.opening E schedule)
  | _, .last lanes tail _encoding _queries, combine =>
      .challenge fun lam => foldProjection (combine lam) (fun residual =>
        .sender id fun _ => .challenge fun _ => .challenge fun finalLam =>
          scalarProjection (fun query => combineLastQuadratic residual query finalLam) tail) lanes
  | _, .more lanes _encoding _queries rest, combine =>
      .challenge fun lam => foldProjection (combine lam) (fun residual =>
        .oracle (.challenge fun _ => .sender id fun _ => .read fun ood =>
          .challenge fun _ => whirProjection rest (fun nextLam query =>
            combineQuadratic residual ood query nextLam))) lanes

/-- The production boundary after its residual lookahead has been retained. -/
def whirWireTransition : {n : ℕ} → Whir.Schedule K n → Protocol
  | _, .last _ tail encoding queries =>
      .public .sender (Whir.Table E tail) fun _ =>
        .public .receiver (Fin queries → encoding.Columns) fun _ =>
          .public .receiver E fun _ => Whir.scalarRounds E tail .done
  | _, @Whir.Schedule.more _ tail _ encoding queries rest =>
      .oracle (Whir.oracleMessage E rest)
        (.public .receiver (Fin tail → E) fun _ => .public .sender E fun _ =>
          .public .sender (Whir.Quadratic E) fun _ =>
            .public .receiver (Fin queries → encoding.Columns) fun _ => whirWireProtocol rest)

/-- Boundary projection retains the OOD intro and combines the query intro after batching. -/
def whirBoundaryProjection : {n : ℕ} → (schedule : Whir.Schedule K n) →
    Whir.Quadratic E → Projection (whirWireTransition schedule) (Whir.transition E schedule)
  | _, .last _ tail _ _, residual =>
      .sender id fun _ => .challenge fun _ => .challenge fun lam =>
        scalarProjection (fun query => combineLastQuadratic residual query lam) tail
  | _, .more _ _ _ rest, residual =>
      .oracle (.challenge fun _ => .sender id fun _ => .read fun ood =>
        .challenge fun _ => whirProjection rest (fun lam query => combineQuadratic residual ood query lam))

/-- Observe every actual production message; the derived combined quadratic is never reabsorbed. -/
def whirWirePresentation : {n : ℕ} → (schedule : Whir.Schedule K n) →
    Presentation (whirWireProtocol schedule)
  | _, .last lanes tail encoding queries => .challenge id (fun _ => rfl) scalarDraw
      (whirRounds (.sender quadraticEvents fun _ =>
        .sender (fun table => fieldEvents fun i : Fin (2 ^ tail) =>
          table (fun bit => i.val.testBit bit.val)) (fun _ =>
            .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + encoding.rate))
              (.challenge id (fun _ => rfl) scalarDraw (whirRounds .done tail))))) lanes)
  | _, @Whir.Schedule.more _ tail lanes encoding queries rest =>
      .challenge id (fun _ => rfl) scalarDraw
        (whirRounds (.sender quadraticEvents fun _ => .merkle (extensionLayout rest)
          (.challenge id (fun _ => rfl) (vectorDraw tail)
            (.sender (fun value => fieldEvents ![value]) (fun _ =>
              .sender quadraticEvents fun _ =>
                .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + encoding.rate))
                  (whirWirePresentation rest)))))) lanes)

/-- Production WHIR presentation, projected to the unchanged ideal claim list and error schedule. -/
def whirPresentation {n : ℕ} (schedule : Whir.Schedule K n) : Presentation (Whir.opening E schedule) :=
  .refine (whirWirePresentation schedule) (whirProjection schedule (fun _ => id))

end CompStark.Compiled
