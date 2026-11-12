/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.GrandProduct
public import CompStark.Keccak.Gkr.Executable
public import CompStark.Pcs.WordSum

/-! Grand-product cofactor rounds retain word values and use Horner evaluation. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 8192

@[expose] public section
namespace CompStark.Multilinear.GrandProduct
open CompStark.BinaryFields BF64 Interaction.Oracle

/-- Decode a cofactor tail once and evaluate its polynomial in the word carrier. -/
def evaluateWord (d : Nat) (r current : WordExt3) (q : Message d) (x : WordExt3) : WordExt3 :=
  let coefficients := Vector.ofFn fun i : Fin d => WordExt3.ofField (q i)
  let constant := current - r * Pcs.sumFin (fun i : Fin d => coefficients[i])
  Keccak.Gkr.polyEvalHorner (Fin.cons constant (fun i : Fin d => coefficients[i])) x

/-- Word cofactor evaluation preserves the running claim and every transmitted coefficient. -/
theorem evaluateWord_eq (d : Nat) (r current : WordExt3) (q : Message d) (x : WordExt3) :
    WordExt3.toField (evaluateWord d r current q x) =
      evaluate d r.toField current.toField q x.toField := by
  unfold evaluateWord
  rw [Keccak.Gkr.polyEvalHorner_eq]
  change WordExt3.ringEquiv (∑ i : Fin (d+1), _) = _
  rw [map_sum]
  simp only [map_mul, map_pow]
  have coefficients : (fun i : Fin (d+1) => WordExt3.toField
      (Fin.cons (α := fun _ : Fin (d+1) => WordExt3) (current-r*Pcs.sumFin (fun j : Fin d => WordExt3.ofField (q j)))
        (fun j => WordExt3.ofField (q j)) i)) = decode d r.toField current.toField q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change WordExt3.ringEquiv (current-r*Pcs.sumFin (fun j : Fin d => WordExt3.ofField (q j))) =
        current.toField-r.toField*∑ j, q j
      rw [Pcs.sumFin_eq, map_sub, map_mul, map_sum]
      simp only [show ∀ a, WordExt3.ringEquiv (WordExt3.ofField a) = a from WordExt3.toField_ofField]
      rfl
    · exact WordExt3.toField_ofField _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  change (∑ i : Fin (d+1), WordExt3.toField _ * x.toField ^ i.val) = _
  unfold evaluate evaluateCoefficients
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun c => c*x.toField^i.val) (congrFun coefficients i)

/-- Read successive cofactor rounds while retaining the running claim as three words. -/
def roundsWord (d : Nat) (point : List E) (tail : Protocol) : (n : Nat) → List E → WordExt3 → Bool →
    (roundsProtocol d tail n).tree.ExecutionPath → Option (List E × E × Bool × tail.tree.ExecutionPath)
  | 0, coordinates, current, active, path => some (coordinates, current.toField, active, path)
  | n+1, coordinates, current, active, path => match path with
    | ⟨_, none, _⟩ => none
    | ⟨message, some x, rest⟩ =>
      roundsWord d point tail n (coordinates ++ [x])
        (evaluateWord d (WordExt3.ofField (point.getD coordinates.length 0)) current message (WordExt3.ofField x))
        active rest

/-- Word round parsing preserves the complete endpoint and every abort branch. -/
theorem roundsWord_eq (d : Nat) (point : List E) (tail : Protocol) (n : Nat)
    (coordinates : List E) (current : WordExt3) (active : Bool)
    (path : (roundsProtocol d tail n).tree.ExecutionPath) :
    roundsWord d point tail n coordinates current active path =
      roundsResult d point tail n coordinates current.toField active path := by
  induction n generalizing coordinates current active with
  | zero => rfl
  | succ n ih =>
    rcases path with ⟨message, challenge, rest⟩
    cases challenge with
    | none => rfl
    | some x =>
      change roundsWord d point tail n (coordinates ++ [x])
          (evaluateWord d (WordExt3.ofField (point.getD coordinates.length 0)) current message (WordExt3.ofField x)) active rest =
        roundsResult d point tail n (coordinates ++ [x])
          (evaluate d (point.getD coordinates.length 0) current.toField message x)
          (active && check d (point.getD coordinates.length 0) current.toField message) rest
      rw [ih, evaluateWord_eq, WordExt3.toField_ofField, WordExt3.toField_ofField, check_eq_true, Bool.and_true]

/-- Parse every product-tree layer with word-carrier cofactor rounds. -/
def resultWord (tail : Protocol) : (steps : List Nat) → (m : Nat) → Claim → Bool →
    (protocol tail steps m).tree.ExecutionPath → Option (Claim × Bool × tail.tree.ExecutionPath)
  | [], _, claim, active, path => some (claim, active, path)
  | lanes :: rest, m, claim, active, path => do
    let lam : E := path.1
    let (coordinates, current, good, descendants) ← roundsWord (2^lanes) claim.point
      (.public .sender (Fin 3 → Fin (2^lanes) → E) fun _ =>
        interpolationProtocol (protocol tail rest (m+lanes)) lanes)
      m [] (WordExt3.ofField (batch lam claim.values)) active path.2
    let children : Fin 3 → Fin (2^lanes) → E := descendants.1
    let (next, finalPath) := interpolationResult lanes coordinates children
      (protocol tail rest (m+lanes)) lanes [] descendants.2
    resultWord tail rest (m+lanes) next
      (good && decide (current = ∑ side : Fin 3, lam^side.val * ∏ i : Fin (2^lanes), children side i)) finalPath

/-- Word cofactor rounds preserve the exact product-tree parser. -/
@[csimp] theorem result_word : result = resultWord := by
  funext tail steps m claim active path
  induction steps generalizing m claim active with
  | nil => rfl
  | cons lanes rest ih =>
    rw [result.eq_2, resultWord.eq_2]
    simp only [roundsWord_eq, WordExt3.toField_ofField, ih]

end CompStark.Multilinear.GrandProduct
