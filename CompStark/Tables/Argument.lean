/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.TableSumcheck.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.TableSumcheck

/-! The bus argument followed by the table sumcheck, over a `System`.

The table sumcheck starts at the bus's output. Both phases retain the committed witness, so a
witness that satisfies the external relation but not the system reaches true final claims with
probability at most the sum of the two errors. -/

@[expose] public section

namespace CompStark.Tables.Argument

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The bus's input relation and the external relation are the system's satisfaction. -/
theorem input_satisfied (w : Witness K S.tables.length) :
    Bus.Input S L w ∧ S.external w ↔ S.Satisfied L w := by
  constructor
  · rintro ⟨⟨shaped, balanced, nonzero, riders⟩, external⟩
    exact ⟨shaped, (S.ridersZero_iff L w).mp riders, nonzero, balanced, external⟩
  · rintro ⟨shaped, constraints, nonzero, balanced, external⟩
    exact ⟨⟨shaped, balanced, nonzero, (S.ridersZero_iff L w).mpr constraints⟩, external⟩

/-- The bus, then the table sumcheck from the bus's output; a rejected bus ends the run. -/
noncomputable def play
    (busProver : Retained.Strategy (Bus.protocol S L k).tree (Bus.protocol S L k).roles)
    (tableProver : Bus.Output S L k →
      Retained.Strategy (TableSumcheck.protocol S L).tree (TableSumcheck.protocol S L).roles) :
    ProbComp (Option ((Bus.protocol S L k).tree.ExecutionPath ×
      (TableSumcheck.protocol S L).tree.ExecutionPath)) := do
  let busPath ← Retained.play (Bus.protocol S L k).roles (Bus.challenges S L k) busProver
  match Bus.outputClaim S L k busPath with
  | none => return none
  | some o =>
      let tablePath ← Retained.play (TableSumcheck.protocol S L).roles
        (TableSumcheck.challenges S L k o) (tableProver o)
      return some (busPath, tablePath)

/-- Both phases ran and their final claims are true of the committed witness. -/
def Accepted (w₀ : Witness K S.tables.length)
    (paths : Option ((Bus.protocol S L k).tree.ExecutionPath ×
      (TableSumcheck.protocol S L).tree.ExecutionPath)) : Prop :=
  match paths with
  | none => False
  | some (busPath, tablePath) => ∃ o final,
      Bus.outputClaim S L k busPath = some o ∧
        TableSumcheck.outputClaim S L k o tablePath = some final ∧ TableSumcheck.Terminal S L k final w₀

variable {S L k} {width : String → ℕ} (hwf : S.WellFormed L) (hshape : S.BusShape k width)
include hwf hshape

/-- A witness that satisfies the external relation but not the system reaches true final claims
with probability at most the bus error plus the table sumcheck error. -/
theorem unsatisfied_acceptance_le (w₀ : Witness K S.tables.length) (hext : S.external w₀)
    (hne : ¬ S.Satisfied L w₀)
    (busProver : Retained.Strategy (Bus.protocol S L k).tree (Bus.protocol S L k).roles)
    (tableProver : Bus.Output S L k →
      Retained.Strategy (TableSumcheck.protocol S L).tree (TableSumcheck.protocol S L).roles) :
    Pr{let paths ← play S L k busProver tableProver}[Accepted S L k w₀ paths] ≤
      Bus.error S L k + TableSumcheck.error S L := by
  classical
  unfold play
  apply le_trans (prEvent_bind_le_prEvent_add
    (Retained.play (Bus.protocol S L k).roles (Bus.challenges S L k) busProver) _
    (Retained.Failure (Bus.extractor S L k w₀)) _ (ε := TableSumcheck.error S L) ?_)
  · exact add_le_add (Bus.knowledgeSoundness hwf hshape w₀ busProver) (le_refl _)
  · intro busPath busGood
    cases hout : Bus.outputClaim S L k busPath with
    | none => simp only [prEvent_pure, Accepted, ↓reduceIte, zero_le]
    | some o =>
      simp only [bind_pure_comp, prEvent_map]
      apply le_trans (prEvent_mono _ _ (Retained.Failure (TableSumcheck.extractor S L k o w₀)) ?_)
      · exact TableSumcheck.knowledgeSoundness S L k hwf o w₀ (tableProver o)
      · intro tablePath accepted
        change ∃ out final, Bus.outputClaim S L k busPath = some out ∧
          TableSumcheck.outputClaim S L k out tablePath = some final ∧
            TableSumcheck.Terminal S L k final w₀ at accepted
        obtain ⟨out, final, outEq, finalEq, finalGood⟩ := accepted
        have same : out = o := Option.some.inj (outEq.symm.trans hout)
        subst out
        have endpoint : (TableSumcheck.terminalProblem S L k w₀).rel ()
            (TableSumcheck.outputClaim S L k o tablePath) w₀ := by
          change w₀ = w₀ ∧ _
          refine ⟨rfl, ?_⟩
          rw [finalEq]
          exact finalGood
        obtain ⟨w, hw⟩ := Retained.terminal_known (TableSumcheck.terminalRelation S L k o w₀)
          tablePath w₀ endpoint
        refine ⟨w, hw, ?_⟩
        intro inputGood
        have hi : (Retained.state w₀ (Bus.Terminal S L k o)).holds w₀ := by
          rw [inputGood.1] at inputGood
          exact inputGood
        have busEndpoint : (Bus.terminalProblem S L k w₀).rel () (Bus.outputClaim S L k busPath) w₀ := by
          change w₀ = w₀ ∧ _
          refine ⟨rfl, ?_⟩
          rw [hout]
          exact hi.2
        obtain ⟨v, hv⟩ := Retained.terminal_known (Bus.terminalRelation S L k w₀) busPath w₀ busEndpoint
        apply busGood
        refine ⟨v, hv, ?_⟩
        change ¬ (_ = w₀ ∧ Bus.Input S L _)
        rintro ⟨eq, input⟩
        rw [eq] at input
        exact hne ((input_satisfied S L w₀).mp ⟨input, hext⟩)

omit hwf hshape in
/-- At accepted endpoints, the committed witness satisfies the system, or one of the two
extractors failed on its path. -/
theorem paths_satisfied_or_bad (w₀ : Witness K S.tables.length) (hext : S.external w₀)
    (busPath : (Bus.protocol S L k).tree.ExecutionPath) (o : Bus.Output S L k)
    (hout : Bus.outputClaim S L k busPath = some o)
    (tablePath : (TableSumcheck.protocol S L).tree.ExecutionPath)
    (w : ((TableSumcheck.extractor S L k o w₀).terminalState tablePath).Witness)
    (known : ((TableSumcheck.extractor S L k o w₀).terminalState tablePath).holds w) :
    S.Satisfied L w₀ ∨ Retained.Failure (Bus.extractor S L k w₀) busPath ∨
      Retained.Failure (TableSumcheck.extractor S L k o w₀) tablePath := by
  classical
  by_cases htbad : Retained.Failure (TableSumcheck.extractor S L k o w₀) tablePath
  · exact Or.inr (Or.inr htbad)
  by_cases hbbad : Retained.Failure (Bus.extractor S L k w₀) busPath
  · exact Or.inr (Or.inl hbbad)
  have ht : (Retained.state w₀ (Bus.Terminal S L k o)).holds
      ((TableSumcheck.extractor S L k o w₀).extractWitness tablePath w) := by
    by_contra hn
    exact htbad ⟨w, known, hn⟩
  have ht₀ : (Retained.state w₀ (Bus.Terminal S L k o)).holds w₀ := by
    rw [ht.1] at ht
    exact ht
  have endpoint : (Bus.terminalProblem S L k w₀).rel () (Bus.outputClaim S L k busPath) w₀ := by
    change w₀ = w₀ ∧ _
    refine ⟨rfl, ?_⟩
    rw [hout]
    exact ht₀.2
  obtain ⟨v, hv⟩ := Retained.terminal_known (Bus.terminalRelation S L k w₀) busPath w₀ endpoint
  have hb₀ : (Retained.state w₀ (Bus.Input S L)).holds
      ((Bus.extractor S L k w₀).extractWitness busPath v) := by
    by_contra hn
    exact hbbad ⟨v, hv, hn⟩
  rw [hb₀.1] at hb₀
  exact Or.inl ((input_satisfied S L w₀).mp ⟨hb₀.2, hext⟩)

end CompStark.Tables.Argument
