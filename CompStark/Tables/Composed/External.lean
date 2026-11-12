/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.TableSumcheck
public import CompStark.Tables.Stack
public import CompStark.Pcs.Evaluated

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
  /-- The argument's protocol, after the table sumcheck; its shape does not depend on the table's
  output. -/
  protocol : Protocol
  /-- Prefix predicates on the stack; the root is the argument's start relation. -/
  labels : (out : TableSumcheck.Output S L k) → Retained.Labels (Whir.Table K M) protocol.tree
  /-- The argument's output from a transcript. -/
  output : (out : TableSumcheck.Output S L k) → protocol.tree.ExecutionPath → StackOutput M
  /-- The authored endpoint predicate is the output's relation. -/
  endpoint : ∀ out path, Retained.endpoint (labels out) path = (output out path).Holds
  /-- The argument's challenge schedule. -/
  challenges : (out : TableSumcheck.Output S L k) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles
  /-- The identity extractor is prover-preserving. -/
  preserving : ∀ out q, (Retained.extractor q (labels out)).IsProverPreserving protocol.roles
  /-- The identity extractor meets the schedule's local bounds. -/
  bounded : ∀ out q, (Retained.extractor q (labels out)).IsLocallyBounded protocol.roles
    (challenges out)
  /-- The argument's claims with certified evaluators of their weights. -/
  evaluated : (out : TableSumcheck.Output S L k) → protocol.tree.ExecutionPath → List (Pcs.EvaluatedClaim M)
  /-- The evaluated claims are the argument's claims. -/
  evaluated_claims : ∀ out path, (evaluated out path).map Pcs.EvaluatedClaim.claim = (output out path).claims
  /-- A bound on the number of the argument's claims. -/
  claimBound : ℕ
  /-- The argument's output has at most `claimBound` claims. -/
  claims_le : ∀ out path, (output out path).claims.length ≤ claimBound
  /-- The argument's error. -/
  error : ENNReal
  /-- The schedule's errors add up to at most the argument's error. -/
  budget : ∀ out, Retained.Budget protocol.roles (challenges out) error
  /-- The start relation gives the rider on the table's draws and the virtual values. -/
  start_sound : ∀ out q, Retained.input (labels out) q →
    rider out.point.reverse q ∧ VirtualHold S L k out (interpret q)
  /-- The stack of a satisfying witness interprets to the witness. -/
  interpret_stack : ∀ w, S.Shaped L w → S.external w → interpret (S.stack L M w) = w
  /-- The stack of a satisfying witness has a true rider at every draw. -/
  rider_stack : ∀ w draws, S.Shaped L w → S.external w → rider draws (S.stack L M w)
  /-- The rider on the table's draws and the virtual values give the start relation. -/
  start_complete : ∀ out q, rider out.point.reverse q → VirtualHold S L k out (interpret q) →
    Retained.input (labels out) q
  /-- The verifier's coins. -/
  Coins : Type
  /-- The honest transcript against the verifier's coins. -/
  honest : TableSumcheck.Output S L k → Whir.Table K M → Coins → protocol.tree.ExecutionPath
  /-- From its start relation, the honest transcript's output holds on the stack. -/
  honest_holds : ∀ out q coins, Retained.input (labels out) q → (output out (honest out q coins)).Holds q

/-- A system with no virtual columns and no external relation needs no argument: the stack is the
witness. -/
def External.none (hM : (S.stackBlocks L).total ≤ 2 ^ M) (novirtual : ∀ t, (S.table t).virtual = [])
    (noexternal : ∀ w, S.external w) :
    External S L k M where
  interpret := S.read L M
  interpret_shaped := S.read_shaped L M
  interpret_committed _ _ _ _ _ := rfl
  rider _ _ := True
  rider_local q draws _ := by
    apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun _ h ↦ h.1 trivial)
    simp only [prEvent_false, zero_le]
  external_of_rider q _ := noexternal _
  protocol := .done
  labels _ := fun _ ↦ True
  output _ _ := ⟨[], true⟩
  endpoint _ _ := by
    funext q
    simp only [StackOutput.Holds, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self]
    rfl
  challenges _ := PUnit.unit
  evaluated _ _ := []
  evaluated_claims _ _ := rfl
  claimBound := 0
  claims_le _ _ := le_rfl
  preserving _ _ := trivial
  bounded _ _ := trivial
  error := 0
  budget _ := trivial
  start_sound out q _ := ⟨trivial, fun t i hv ↦ by
    simp only [TableSumcheck.virtualAt, novirtual, List.contains_nil, Bool.false_eq_true] at hv⟩
  interpret_stack w shaped _ := S.read_stack L M hM w shaped novirtual
  rider_stack _ _ _ _ := trivial
  start_complete _ _ _ _ := trivial
  Coins := PUnit
  honest _ _ _ := PUnit.unit
  honest_holds _ _ _ _ := ⟨rfl, fun _ h ↦ absurd h List.not_mem_nil⟩

end CompStark.Tables.Composed
