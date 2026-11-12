/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.RingSwitch.Protocol
public import CompStark.BinaryFields.WordProduct

/-! Ring-switch target evaluation retaining words throughout the Frobenius composition. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.Pcs.RingSwitch
open CompStark.BinaryFields BF64

/-- Apply ring-switch stages while retaining the running value and all Frobenius squares as words. -/
def frobMapWord : List (Nat × WordExt3) → WordExt3 → WordExt3
  | [], a => a
  | (s,f) :: stages, a => frobMapWord stages (a+f*WordExt3.frobenius a s)
/-- Word stages represent the exact additive ring-switch composition. -/
theorem frobMapWord_eq (stages : List (Nat × WordExt3)) (a : WordExt3) :
    (frobMapWord stages a).toField =
      frobMap (stages.map fun stage => (stage.1,stage.2.toField)) a.toField := by
  induction stages generalizing a with
  | nil => rfl
  | cons stage stages ih =>
    rw [frobMapWord.eq_2, ih]
    simp only [List.map_cons, frobMap.eq_2]
    congr 1
    change WordExt3.ringEquiv _ = _
    simp only [map_add, map_mul]
    change a.toField + stage.2.toField * (WordExt3.frobenius a stage.1).toField = _
    rw [WordExt3.toField_frobenius]
/-- Compute the ring target with one word conversion per input and repeated specialized squares. -/
def ringTargetWord {n : Nat} (statement : Statement n) (fs : Vector E 6) : E :=
  let stages := (ringStages fs).map fun stage => (stage.1,WordExt3.ofField stage.2)
  WordExt3.toField (∑ i : Fin 64,
    WordExt3.mulScalar (frobMapWord stages (WordExt3.ofField (statement.values i)))
      (Word.ofField g ^ i.val))
/-- Word target accumulation preserves the exact weighted ring-switch claim. -/
theorem ringTargetWord_eq {n : Nat} (statement : Statement n) (fs : Vector E 6) :
    ringTargetWord statement fs = ringTarget statement fs := by
  unfold ringTargetWord ringTarget
  change WordExt3.ringEquiv _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change WordExt3.toField (WordExt3.mulScalar _ _) = _
  rw [WordExt3.toField_mulScalar, frobMapWord_eq]
  simp only [List.map_map, Function.comp_def, WordExt3.toField_ofField]
  have stages : (ringStages fs).map (fun x => (x.1,x.2)) = ringStages fs := by
    change List.map id (ringStages fs) = ringStages fs
    exact List.map_id _
  rw [stages]
  change Word.ringEquiv (Word.ofField g ^ i.val) • _ = _
  rw [map_pow]
  change g ^ i.val • _ = _
  rw [Algebra.smul_def]
  rfl

/-- Native ring-switch targets retain the exact word composition. -/
@[csimp] theorem ringTarget_word : @ringTarget = @ringTargetWord := by
  funext n statement fs
  exact (ringTargetWord_eq statement fs).symm

end CompStark.Pcs.RingSwitch
