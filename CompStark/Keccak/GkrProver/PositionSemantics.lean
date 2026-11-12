/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PackTerminal
public import CompStark.Keccak.GkrProver.TransposeSemantics
public import CompStark.Keccak.GkrProver.InputOpeningHonest

/-! Committed-witness semantics of the native zero-padded position factors. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64
open scoped BigOperators

/-- The three shifted position buffers, padded to the eleven-coordinate Boolean cube. -/
def positionFactors (table : PackedE) : Array (Array W) :=
  Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
    if j.val<1600 then table.get (shift j.val k.val) else lane 0

/-- Position factor materialization creates three complete eleven-coordinate tables. -/
theorem positionFactors_shape (table : PackedE) :
    (positionFactors table).size=3 ∧ ∀ k : Fin 3,((positionFactors table)[k.val]!).size=2048 := by
  constructor
  · exact Array.size_ofFn ..
  · intro k
    rw [positionFactors,ofFn_get!]
    exact Array.size_ofFn ..

/-- Every position buffer cell is its shifted factor or its explicit zero padding. -/
theorem positionFactors_get (table : PackedE) (k : Fin 3) (j : Fin 2048) :
    ((positionFactors table)[k.val]!)[j.val]! =
      if j.val<1600 then table.get (shift j.val k.val) else 0 := by
  rw [positionFactors,ofFn_get!,ofFn_get!]
  rfl

/-- Interpolation of the native position buffers is exactly the protocol's shifted factor evaluation. -/
theorem positionFactors_protocol {p : Nat} (q : Witness p) (d : Fin 12) (s : W)
    (point : Fin (p+1) → W) (table : PackedE)
    (ht : ∀ j : Fin 1600,table.get j.val=linearAtPack q d s point j)
    (position : Fin 11 → W) (k : Fin 3) :
    mle (n := 11) (fun j : Fin 2048 => ((positionFactors table)[k.val]!)[j.val]!) position =
      shiftedEvaluation q d s point position k.val := by
  unfold shiftedEvaluation
  apply congrArg (fun values : Fin 2048 → W => mle (n := 11) values position)
  funext j
  rw [positionFactors_get]
  split
  · rename_i hj
    rw [shift_eq ⟨j.val,hj⟩ k.val]
    exact ht (along ⟨j.val,hj⟩ k.val)
  · rfl

/-- Padding position weights preserves every original weight and adds exactly zero in the other cube rows. -/
theorem positionWeights_get {p : Nat} (claim : Claim) (hw : claim.weights.size=1600) (j : Fin 2048) :
    (claim.weights++Array.replicate 448 (0 : W))[j.val]! =
      if h : j.val<1600 then (claim.toWordProtocol p).weights ⟨j.val,h⟩ else 0 := by
  by_cases hj : j.val<1600
  · rw [arrayAppend_get_left _ _ _ (by omega),dite_eq_left hj]
    rfl
  · rw [show j.val=claim.weights.size+(j.val-claim.weights.size) by omega]
    rw [arrayAppend_get_right _ _ (j.val-claim.weights.size) (by
      rw [Array.size_replicate]; have := j.isLt; omega),dite_eq_right (by omega)]
    rw [getElem!_pos _ _ (by rw [Array.size_replicate]; have := j.isLt; omega),Array.getElem_replicate]

/-- The position summand on native buffers is the protocol summand whenever its entering factor table is certified. -/
theorem positionTableSummand_protocol {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim)
    (hw : claim.weights.size=1600) (t : LayerTranscript W p) (table : PackedE)
    (ht : ∀ j : Fin 1600,table.get j.val=linearAtPack q d t.point t.packPoint j)
    (position : Fin 11 → W) :
    positionTableSummand (claim.weights++Array.replicate 448 0) (positionFactors table) 11
      (eqEval (claim.toWordProtocol p).point t.packPoint) (sum (instanceWeights t.point)) position =
      positionSummand q d (claim.toWordProtocol p) t position := by
  have hwval : mle (n := 11) (fun j : Fin 2048 =>
      (claim.weights++Array.replicate 448 0)[j.val]!) position =
      mle (n := 11) (fun j : Fin 2048 => if hj : j.val<1600 then
        (claim.toWordProtocol p).weights ⟨j.val,hj⟩ else 0) position := by
    apply congrArg (fun values : Fin 2048 → W => mle (n := 11) values position)
    funext j
    exact positionWeights_get claim hw j
  exact congrArg₂ (fun weight factors : W => eqEval (claim.toWordProtocol p).point t.packPoint*weight*factors)
    hwval
    (congrArg₂ (·+·)
      (congrArg₂ (·*·) (instanceWeights_sum t.point)
        (positionFactors_protocol q d t.point t.packPoint table ht position (0 : Fin 3)))
      (congrArg₂ (·*·)
        (congrArg₂ (·+·) (instanceWeights_sum t.point)
          (positionFactors_protocol q d t.point t.packPoint table ht position (1 : Fin 3)))
        (positionFactors_protocol q d t.point t.packPoint table ht position (2 : Fin 3))))

/-- The actual native position loop returns the three committed shifted evaluations. -/
theorem positionLoop_evaluations_protocol {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim)
    (hw : claim.weights.size=1600) (s scale : W) (point : Fin (p+1) → W) (table : PackedE)
    (ht : ∀ j : Fin 1600,table.get j.val=linearAtPack q d s point j) (writer : Writer) (k : Fin 3) :
    let final := positionLoop writer (claim.weights++Array.replicate 448 0) (positionFactors table)
      scale (sum (instanceWeights s)) 11
    (final.factors.map (·[0]!))[k.val]! =
      shiftedEvaluation q d s point (fun i : Fin 11 => final.point[i.val]!) k.val := by
  dsimp only
  have hshape := positionFactors_shape table
  have hh := positionLoop_terminal writer (claim.weights++Array.replicate 448 0) (positionFactors table)
    scale (sum (instanceWeights s)) 11
    (by rw [Array.size_append,Array.size_replicate,hw]; rfl) hshape.1 hshape.2
  rw [getElem!_pos _ _ (by rw [Array.size_map,hh.2.1]; exact k.isLt),Array.getElem_map,
    ← getElem!_pos _ _ (by rw [hh.2.1]; exact k.isLt),hh.2.2.2.2 k]
  exact positionFactors_protocol q d s point table ht _ k

/-- Every native position message is the honest protocol message for its certified factor table. -/
theorem positionLoop_messages_protocol {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim)
    (hw : claim.weights.size=1600) (t : LayerTranscript W p) (table : PackedE)
    (ht : ∀ j : Fin 1600,table.get j.val=linearAtPack q d t.point t.packPoint j) (writer : Writer) :
    let final := positionLoop writer (claim.weights++Array.replicate 448 0) (positionFactors table)
      (eqEval (claim.toWordProtocol p).point t.packPoint) (sum (instanceWeights t.point)) 11
    (fun i : Fin 11 => positionMessageOfArray final.messages[i.val]!) =
      honestCompressedRounds (positionSummand q d (claim.toWordProtocol p) t)
        (positionCoordinateDegree q d (claim.toWordProtocol p) t) (fun i => final.point[i.val]!) := by
  dsimp only
  rw [positionLoop_honest _ _ _ _ _ 11
    (by rw [Array.size_append,Array.size_replicate,hw]; rfl)
    (positionFactors_shape table).1 (positionFactors_shape table).2]
  apply honestCompressedRounds_congr
  · exact funext (positionTableSummand_protocol q d claim hw t table ht)
  · rfl

/-- The committed RMFE factor polynomial commutes with coefficient-field homomorphisms. -/
theorem packedLinear_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) {p : Nat} (q : Witness p) (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600) :
    (packedLinear (E := F) q d m b j).map e=packedLinear (E := G) q d m b j := by
  simp only [packedLinear,kemb_map,zmod_cast_map]

/-- Evaluating a committed RMFE factor commutes with coefficient-field homomorphisms. -/
theorem packedLinear_eval_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) {p : Nat} (q : Witness p) (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600)
    (s : F) : e ((packedLinear q d m b j).eval s)=(packedLinear q d m b j).eval (e s) := by
  rw [← packedLinear_map e,Polynomial.eval_map_apply]

/-- The full committed pack evaluation commutes with coefficient-field homomorphisms. -/
theorem linearAtPack_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) {p : Nat} (q : Witness p) (d : Fin 12) (s : F) (point : Fin (p+1) → F)
    (j : Fin 1600) :
    e (linearAtPack q d s point j)=linearAtPack q d (e s) (fun i => e (point i)) j := by
  simp only [linearAtPack,map_sum,map_mul,eqWeight_map,packedLinear_eval_map]

/-- Zero-padded shifted position evaluations commute with coefficient-field homomorphisms. -/
theorem shiftedEvaluation_map {F G : Type} [CommRing F] [CharP F 2] [CommRing G] [CharP G 2]
    (e : F →+* G) {p : Nat} (q : Witness p) (d : Fin 12) (s : F) (point : Fin (p+1) → F)
    (position : Fin 11 → F) (k : Nat) :
    e (shiftedEvaluation q d s point position k)=
      shiftedEvaluation q d (e s) (fun i => e (point i)) (fun i => e (position i)) k := by
  unfold shiftedEvaluation
  rw [mle_map]
  apply congrArg (fun table : Fin 2048 → G => mle (n := 11) table (fun i => e (position i)))
  funext j
  split <;> simp only [linearAtPack_map,map_zero]

/-- Equality kernels commute with coefficient-field homomorphisms. -/
theorem eqEval_map {F G : Type} [CommRing F] [CommRing G] (e : F →+* G)
    {n : Nat} (point sampled : Fin n → F) :
    e (eqEval point sampled)=eqEval (fun i => e (point i)) (fun i => e (sampled i)) := by
  simp only [eqEval,map_prod,map_add,map_mul,map_sub,map_one]

/-- Interpret every native layer message in its word field. -/
def Layer.toWordProtocol (p : Nat) (layer : Layer) : LayerTranscript W p where
  product i := layer.product[i.val]!
  point := layer.s
  packPolys i := ((layer.packMessages[i.val]!)[0]!,fun _ => (layer.packMessages[i.val]!)[1]!)
  packPoint i := layer.packPoint[i.val]!
  positionPolys i := ((layer.positionMessages[i.val]!)[0]!,fun k => (layer.positionMessages[i.val]!)[k.val+1]!)
  positionPoint i := layer.positionPoint[i.val]!
  evaluations i := layer.evaluations[i.val]!
  beta := layer.beta

/-- The position summand transports from native word fields to the verifier field. -/
theorem positionSummand_toField {p : Nat} (q : Witness p) (d : Fin 12) (claim : Claim) (t : Layer)
    (position : Fin 11 → W) :
    WordExt3.ringEquiv (positionSummand q d (claim.toWordProtocol p) (t.toWordProtocol p) position) =
      positionSummand q d (claim.toProtocol p) (t.toProtocol p) (fun i => WordExt3.ringEquiv (position i)) := by
  let e := WordExt3.ringEquiv.toRingHom
  have hmu (i : Fin 16) : e (muAt t.s i)=muAt t.s.toField i :=
    (congrArg WordExt3.ringEquiv (mu_eq t.s i).symm).trans (mu_toField t.s i)
  have hkappa : e (∑ i : Fin 16,muAt t.s i)=∑ i : Fin 16,muAt t.s.toField i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hmu i)
  have hweight : e (mle (n := 11) (fun j : Fin 2048 =>
      if j.val<1600 then claim.weights[j.val]! else 0) position) =
      mle (n := 11) (fun j : Fin 2048 =>
        if j.val<1600 then claim.weights[j.val]!.toField else 0) (fun i => e (position i)) := by
    calc
      _ = mle (n := 11) (fun j : Fin 2048 => e
          (if j.val<1600 then claim.weights[j.val]! else 0)) (fun i => e (position i)) :=
        mle_map e _ position
      _ = _ := by
        apply congrArg (fun table : Fin 2048 → E => mle (n := 11) table (fun i => e (position i)))
        funext j
        split
        · rfl
        · exact map_zero e
  have hfactor (k : Nat) := shiftedEvaluation_map e q d t.s
    (fun i : Fin (p+1) => t.packPoint[i.val]!) position k
  have heq := eqEval_map e (fun i : Fin (p+1) => claim.point[i.val]!) (fun i => t.packPoint[i.val]!)
  change e (eqEval (fun i : Fin (p+1) => claim.point[i.val]!) (fun i => t.packPoint[i.val]!) *
    mle (n := 11) (fun j : Fin 2048 => if j.val<1600 then claim.weights[j.val]! else 0) position *
      ((∑ i : Fin 16,muAt t.s i)*shiftedEvaluation q d t.s (fun i => t.packPoint[i.val]!) position 0+
        ((∑ i : Fin 16,muAt t.s i)+shiftedEvaluation q d t.s (fun i => t.packPoint[i.val]!) position 1)*
          shiftedEvaluation q d t.s (fun i => t.packPoint[i.val]!) position 2)) = _
  rw [map_mul,map_mul,map_add,map_mul,map_mul,map_add]
  exact congrArg₂ (·*·) (congrArg₂ (·*·) heq hweight)
    (congrArg₂ (·+·) (congrArg₂ (·*·) hkappa (hfactor 0))
      (congrArg₂ (·*·) (congrArg₂ (·+·) hkappa (hfactor 1)) (hfactor 2)))

end CompStark.Keccak.GkrProver
