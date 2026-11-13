/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.TableSumcheck
public import CompStark.Tables.Stack
public import CompStark.Pcs.Evaluated
public import CompStark.Compose.Reduction

/-! The argument that opens a system's virtual columns, the interface the composed proof system
takes for "opened by another argument".

The retained object of the composed system is the committed stack `q`. The argument says how a
witness is read off `q` (`interpret`: the committed columns from the stack, the virtual ones from
the argument's own relation), carries a rider on the table sumcheck's draws (a relation on `q`
that the table phase restricts coordinate by coordinate, so that the argument can start at the
table sumcheck's final point instead of drawing its own), and runs a protocol after the table
sumcheck that reduces the transmitted virtual values to weighted claims on the stack. -/

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

/-- The output of an argument on the stack: its weighted claims and whether its checks passed. -/
structure StackOutput (M : ℕ) where
  /-- Weighted claims on the stack. -/
  claims : List (Whir.Claim E M)
  /-- Whether every public check passed. -/
  active : Bool

/-- An argument's endpoint relation: its checks passed and its claims hold on the stack. -/
def StackOutput.Holds {M : ℕ} (out : StackOutput M) (q : Whir.Table K M) : Prop :=
  out.active = true ∧ ∀ claim ∈ out.claims, claim.Holds (fun u ↦ ofK (q u))

variable (S : System K) (L : Layout S.tables.length) (k M : ℕ)

/-- A transmitted column is virtual. -/
def TableSumcheck.virtualAt (t : Fin S.tables.length) (c : ℕ) : Bool :=
  (S.table t).virtual.contains c

/-- The table sumcheck's transmitted virtual values are the virtual columns' extensions. -/
def VirtualHold (out : TableSumcheck.Output S L k) (w : Witness K S.tables.length) : Prop :=
  ∀ t (i : Fin (TableSumcheck.transmitted S t.1).length),
    TableSumcheck.virtualAt S t.1 (TableSumcheck.transmitted S t.1)[i] = true →
      out.values t i = S.column L w t.1 (TableSumcheck.transmitted S t.1)[i]
        (out.point.take (L.logHeight t.1))

/-- An argument opening a system's virtual columns on its stack of `M` variables. -/
structure External where
  /-- The witness read off a stack: its committed columns and the virtual columns the argument
  defines. -/
  interpret : Whir.Table K M → Witness K S.tables.length
  /-- An interpreted witness has the system's shape. -/
  interpret_shaped : ∀ q, S.Shaped L (interpret q)
  /-- An interpreted witness's committed cells are the stack's. -/
  interpret_committed : ∀ q t i c, c ∈ S.committedColumns t →
    ((interpret q t).getD i #[]).getD c 0 = ((S.read L M q t).getD i #[]).getD c 0
  /-- The rider on the table sumcheck's draws, in draw order. -/
  rider : List E → Whir.Table K M → Prop
  /-- One more draw makes a false rider true with probability at most `1 / |E|`. -/
  rider_local : ∀ q draws, draws.length < TableSumcheck.maxHeight S L →
    Pr{let r ← ($ᵗ E)}[¬ rider draws q ∧ rider (draws ++ [r]) q] ≤ overE 1
  /-- Before any draw the rider gives the system's external relation. -/
  external_of_rider : ∀ q, rider [] q → S.external (interpret q)
  /-- The stack of a satisfying witness interprets to the witness. -/
  interpret_stack : ∀ w, S.Shaped L w → S.external w → interpret (S.stack L M w) = w
  /-- The stack of a satisfying witness has a true rider at every draw. -/
  rider_stack : ∀ w draws, S.Shaped L w → S.external w → rider draws (S.stack L M w)
  /-- The argument's start relation at the table sumcheck's output. -/
  start : TableSumcheck.Output S L k → Whir.Table K M → Prop
  /-- At a full table point, the start relation gives the rider on the table's draws and the
  virtual values. -/
  start_sound : ∀ out q, out.point.length = TableSumcheck.maxHeight S L → start out q →
    rider out.point.reverse q ∧ VirtualHold S L k out (interpret q)
  /-- At a full table point, the rider on the table's draws and the virtual values give the start
  relation. -/
  start_complete : ∀ out q, out.point.length = TableSumcheck.maxHeight S L → rider out.point.reverse q → VirtualHold S L k out (interpret q) →
    start out q
  /-- The argument's protocol, after the table sumcheck; its shape does not depend on the table's
  output. -/
  protocol : Protocol
  /-- The argument's parsed output. -/
  Output : Type
  /-- The argument's output from a transcript. -/
  output : TableSumcheck.Output S L k → protocol.tree.ExecutionPath → Output
  /-- The argument's public checks and claims on the stack. -/
  stackOutput : TableSumcheck.Output S L k → Output → StackOutput M
  /-- A bound on the number of the argument's claims. -/
  claimBound : ℕ
  /-- The argument's output has at most `claimBound` claims. -/
  claims_le : ∀ out a, (stackOutput out a).claims.length ≤ claimBound
  /-- The argument's claims with certified evaluators of their weights. -/
  evaluated : TableSumcheck.Output S L k → Output → List (Pcs.EvaluatedClaim M)
  /-- The evaluated claims are the argument's claims. -/
  evaluated_claims : ∀ out a, (evaluated out a).map Pcs.EvaluatedClaim.claim = (stackOutput out a).claims
  /-- The argument's public checks, decided without building its claims. -/
  accepts : TableSumcheck.Output S L k → Output → Bool
  /-- The decided checks are the output's checks. -/
  accepts_eq : ∀ out a, accepts out a = (stackOutput out a).active

/-- The argument's honest prover. -/
structure External.Honest (ext : External S L k M) where
  /-- The verifier's coins. -/
  Coins : Type
  /-- The honest transcript against the verifier's coins. -/
  honest : TableSumcheck.Output S L k → Whir.Table K M → Coins → ext.protocol.tree.ExecutionPath
  /-- From its start relation on a stack whose witness satisfies the external relation, the honest
  transcript's output holds on the stack. -/
  honest_holds : ∀ out q coins, ext.start out q → S.external (ext.interpret q) →
    (ext.stackOutput out (ext.output out (honest out q coins))).Holds q

/-- The argument's reductions and error: on the stack from its start relation, framed by an obligation
it carries through unchanged. -/
structure External.Reductions (ext : External S L k M) where
  /-- The argument as a reduction on the stack. -/
  reduction : TableSumcheck.Output S L k → (Whir.Table K M → Prop) →
    Compose.Reduction ext.protocol (Whir.Table K M) ext.Output
  /-- The reduction starts at the start relation and the frame. -/
  reduction_input : ∀ out frame q, (reduction out frame).input q ↔ ext.start out q ∧ frame q
  /-- The reduction parses its output. -/
  reduction_output : ∀ out frame, (reduction out frame).output = ext.output out
  /-- The reduction ends at its checks and claims and the frame. -/
  reduction_relation : ∀ out frame a q, (reduction out frame).relation a q ↔
    (ext.stackOutput out a).Holds q ∧ frame q
  /-- The argument's error. -/
  error : ENNReal
  /-- The schedule's errors add up to at most the argument's error. -/
  budget : ∀ out frame, Retained.Budget ext.protocol.roles (reduction out frame).challenges error
  /-- The schedule does not depend on the frame. -/
  challenges_frame : ∀ out frame frame', (reduction out frame).challenges = (reduction out frame').challenges

/-- A system with no virtual columns and no external relation needs no argument: the stack is the
witness. -/
def External.none (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (novirtual : ∀ t, (S.table t).virtual = []) (noexternal : ∀ w, S.external w) :
    External S L k M where
  interpret := S.read L M
  interpret_shaped := S.read_shaped L M
  interpret_committed _ _ _ _ _ := rfl
  rider _ _ := True
  rider_local q draws _ := by
    apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun _ h ↦ h.1 trivial)
    simp only [prEvent_false, zero_le]
  external_of_rider q _ := noexternal _
  interpret_stack w shaped _ := S.read_stack L M hM w shaped novirtual
  rider_stack _ _ _ _ := trivial
  start _ _ := True
  start_sound out q _ _ := ⟨trivial, fun t i hv ↦ by
    simp only [TableSumcheck.virtualAt, novirtual, List.contains_nil, Bool.false_eq_true] at hv⟩
  start_complete _ _ _ _ _ := trivial
  protocol := .done
  Output := Unit
  output _ _ := ()
  stackOutput _ _ := ⟨[], true⟩
  claimBound := 0
  claims_le _ _ := le_rfl
  evaluated _ _ := []
  evaluated_claims _ _ := rfl
  accepts _ _ := true
  accepts_eq _ _ := rfl

/-- The trivial argument's honest prover: an empty transcript. -/
def External.none.honest (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (novirtual : ∀ t, (S.table t).virtual = []) (noexternal : ∀ w, S.external w) :
    (External.none S L k M hM novirtual noexternal).Honest where
  Coins := PUnit
  honest _ _ _ := PUnit.unit
  honest_holds _ _ _ _ _ := ⟨rfl, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- The trivial argument's reductions: nothing to reduce. -/
noncomputable def External.none.reductions (hM : (S.stackBlocks L).total ≤ 2 ^ M)
    (novirtual : ∀ t, (S.table t).virtual = []) (noexternal : ∀ w, S.external w) :
    (External.none S L k M hM novirtual noexternal).Reductions where
  reduction _ frame := Compose.reduction .done (fun q ↦ True ∧ frame q) (fun _ ↦ ())
    (fun _ q ↦ True ∧ frame q) PUnit.unit (fun _ ↦ trivial) (fun _ ↦ trivial)
    (Compose.endpoint_of_terminalPredicate _ _ _ _ (fun _ _ ↦ Iff.rfl))
  reduction_input _ _ _ := Iff.rfl
  reduction_output _ _ := rfl
  reduction_relation _ _ _ _ := by
    change True ∧ _ ↔ (true = true ∧ ∀ claim ∈ ([] : List (Whir.Claim E M)), _) ∧ _
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self, true_and]
  error := 0
  budget _ _ := trivial
  challenges_frame _ _ _ := rfl

end CompStark.Tables.Composed
