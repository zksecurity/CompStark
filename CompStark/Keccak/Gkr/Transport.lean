/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.Protocol

/-! Exact transport of GKR messages, equations and acceptance between coefficient rings. -/

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section
namespace CompStark.Keccak.Gkr
open scoped BigOperators

/-- Transport each transmitted compressed-message coefficient. -/
def mapMessage {R S : Type} (f : R → S) {n : Nat} (m : Sumcheck.CompressedMessage R n) :
    Sumcheck.CompressedMessage S n := (f m.1, fun i => f (m.2 i))
/-- Transport every scalar of a weighted GKR claim. -/
def Claim.map {R S : Type} {p : Nat} (f : R → S) (c : Claim R p) : Claim S p :=
  ⟨f c.value, fun i => f (c.mu i), fun i => f (c.point i), fun i => f (c.weights i)⟩
/-- Transport the transmitted scalars and challenges of one layer. -/
def LayerTranscript.map {R S : Type} {p : Nat} (f : R → S) (t : LayerTranscript R p) :
    LayerTranscript S p :=
  ⟨fun i => f (t.product i), f t.point, fun i => mapMessage f (t.packPolys i),
    fun i => f (t.packPoint i), fun i => mapMessage f (t.positionPolys i),
    fun i => f (t.positionPoint i), fun i => f (t.evaluations i), f t.beta⟩
/-- Transport both terminal sumchecks and their claimed evaluations. -/
def OpeningTranscript.map {R S : Type} (f : R → S) (t : OpeningTranscript R) :
    OpeningTranscript S :=
  ⟨fun i => mapMessage f (t.outputPolys i), fun i => f (t.outputPoint i), f t.outputValue,
    fun i => mapMessage f (t.inputPolys i), fun i => f (t.inputPoint i), fun i => f (t.slices i)⟩
/-- Transport the complete public GKR transcript. -/
def Transcript.map {R S : Type} {p : Nat} (f : R → S) (t : Transcript R p) : Transcript S p :=
  ⟨fun i => f (t.instancePoint i), f t.segment, fun i => f (t.lanePoint i), f t.middleValue,
    fun i => (t.layers i).map f, t.openings.map f⟩
section
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
/-- Equality weights commute with a coefficient-ring homomorphism. -/
theorem map_eqWeight {n : Nat} (r : Fin n → R) (i : Nat) :
    eqWeight (fun j => f (r j)) i = f (eqWeight r i) := by
  simp only [eqWeight, map_prod, apply_ite, map_sub, map_one]
/-- Multilinear evaluation commutes with transport of values and coordinates. -/
theorem map_mle {n : Nat} (a : Fin (2^n) → R) (r : Fin n → R) :
    mle (fun i => f (a i)) (fun i => f (r i)) = f (mle a r) := by
  simp only [mle, map_eqWeight, map_sum, map_mul]
/-- The equality polynomial commutes with scalar transport. -/
theorem map_eqEval {n : Nat} (r s : Fin n → R) :
    eqEval (fun i => f (r i)) (fun i => f (s i)) = f (eqEval r s) := by
  simp only [eqEval, map_prod, map_add, map_mul, map_sub, map_one]
/-- Coefficient-message evaluation commutes with scalar transport. -/
theorem map_polyEval {n : Nat} (a : Fin n → R) (r : R) :
    polyEval (fun i => f (a i)) (f r) = f (polyEval a r) := by
  simp only [polyEval, map_sum, map_mul, map_pow]
/-- RMFE Horner evaluation commutes with scalar transport. -/
theorem map_evaluateCoeffs (r : R) (cs : List Nat) :
    Embedding.evaluateCoeffs (f r) cs = f (Embedding.evaluateCoeffs r cs) := by
  induction cs with
  | nil => simp only [Embedding.evaluateCoeffs.eq_1, map_zero]
  | cons c cs ih => simp only [Embedding.evaluateCoeffs.eq_2, ih, map_add, map_mul, map_natCast]
/-- The sixteen in-pack weights commute with scalar transport. -/
theorem map_muAt (r : R) (i : Fin 16) : muAt (f r) i = f (muAt r i) :=
  map_evaluateCoeffs f r _
/-- The fixed binary projection masks commute with scalar transport. -/
theorem map_projectMessage (a : Fin 47 → R) (i : Fin 16) :
    projectMessage (fun j => f (a j)) i = f (projectMessage a i) := by
  simp only [projectMessage, map_sum, apply_ite, map_zero]
/-- Public iota contributions commute with scalar transport. -/
theorem map_constantContribution {p : Nat} (d : Fin 12) (c : Claim R p) :
    constantContribution d (c.map f) = f (constantContribution d c) := by
  simp only [constantContribution, Claim.map, map_mul, map_sum, apply_ite, map_sub, map_one, map_zero]
/-- The linear Keccak layer commutes with scalar transport. -/
theorem map_linear (a : Fin 1600 → R) (j : Fin 1600) :
    linear (fun i => f (a i)) j = f (linear a j) := by
  simp only [linear, map_add, map_sum]
/-- The transpose of the linear layer commutes with scalar transport. -/
theorem map_linearTranspose (a : Fin 1600 → R) (j : Fin 1600) :
    linearTranspose (fun i => f (a i)) j = f (linearTranspose a j) := by
  simp only [linearTranspose, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← map_linear]
  congr 1
  funext k
  split <;> simp only [map_one, map_zero]
/-- Pack-round cofactor evaluation commutes with scalar transport. -/
theorem map_cofactor (r c : R) (m : CofactorMessage R) (x : R) :
    (cofactorOps (f r)).evaluate (f c) (mapMessage f m) (f x) =
      f ((cofactorOps r).evaluate c m x) := by
  simp only [cofactorOps, mapMessage, map_mul, map_add, map_one, map_pow]
/-- Compressed position-round evaluation commutes with scalar transport. -/
theorem map_compressed (d : Nat) (c : R) (m : Sumcheck.CompressedMessage R d) (x : R) :
    (Sumcheck.compressedOps d).evaluate (f c) (mapMessage f m) (f x) =
      f ((Sumcheck.compressedOps d).evaluate c m x) := by
  simp only [Sumcheck.compressedOps, mapMessage, map_add, map_sub, map_mul, map_ofNat, map_sum, map_pow]
/-- Transport every running claim through a block of compatible sumcheck operations. -/
theorem map_roundsEnd {A B : Type} (g : A → B) {n : Nat}
    (ops : Fin n → Sumcheck.MessageOps R A) (mapped : Fin n → Sumcheck.MessageOps S B)
    (h : ∀ i c m x, (mapped i).evaluate (f c) (g m) (f x) = f ((ops i).evaluate c m x))
    (polys : Fin n → A) (point : Fin n → R) (c : R) :
    roundsEnd mapped (fun i => g (polys i)) (fun i => f (point i)) (f c) =
      f (roundsEnd ops polys point c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [roundsEnd.eq_2, h]
    exact ih _ _ (fun i => h i.succ) _ _ _
/-- The cofactor encoding enforces each Boolean sumcheck identity. -/
theorem cofactor_roundsValid {n : Nat} (r : Fin n → R)
    (polys : Fin n → CofactorMessage R) (point : Fin n → R) (c : R) :
    roundsValid (packOps r) polys point c := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih _ _ _ _⟩
/-- The compressed encoding enforces each Boolean sumcheck identity. -/
theorem compressed_roundsValid {d n : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage R d) (point : Fin n → R) (c : R) :
    roundsValid (fun _ => Sumcheck.compressedOps d) polys point c := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih _ _ _⟩
/-- The terminal pack-round claim commutes with scalar transport. -/
theorem map_packEnd {n : Nat} (r : Fin n → R)
    (polys : Fin n → CofactorMessage R) (point : Fin n → R) (c : R) :
    roundsEnd (packOps (fun i => f (r i))) (fun i => mapMessage f (polys i))
      (fun i => f (point i)) (f c) = f (roundsEnd (packOps r) polys point c) :=
  map_roundsEnd f (mapMessage f) _ _ (fun i => map_cofactor f (r i)) _ _ _
/-- The terminal compressed-round claim commutes with scalar transport. -/
theorem map_positionEnd {d n : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage R d) (point : Fin n → R) (c : R) :
    roundsEnd (fun _ => Sumcheck.compressedOps d) (fun i => mapMessage f (polys i))
      (fun i => f (point i)) (f c) =
        f (roundsEnd (fun _ => Sumcheck.compressedOps d) polys point c) :=
  map_roundsEnd f (mapMessage f) _ _ (fun _ => map_compressed f d) _ _ _
section
/-- Transporting a layer preserves its complete outgoing weighted claim. -/
theorem map_nextClaim [CharP R 2] [CharP S 2] {p : Nat} (t : LayerTranscript R p) :
    nextClaim (t.map f) = (nextClaim t).map f := by
  unfold nextClaim LayerTranscript.map Claim.map
  congr 1
  · simp only [map_add, map_mul, map_pow]
  · funext i
    exact map_muAt f _ _
  · funext i
    dsimp only
    rw [← map_linearTranspose]
    congr 1
    funext j
    simp only [map_eqWeight, map_add, map_mul, map_pow]
/-- The initial output claim commutes with scalar transport. -/
theorem map_firstClaim {p : Nat} (x : R) (output : Fin (2^(p+4)) → Fin 25 → R)
    (t : Transcript R p) :
    firstClaim (f x) (fun b l => f (output b l)) (t.map f) = (firstClaim x output t).map f := by
  unfold firstClaim Transcript.map Claim.map outputClaimAt
  simp only [map_mle, map_eqWeight, map_sum, map_add, map_mul, map_pow]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
/-- Every authored layer claim commutes with scalar transport. -/
theorem map_claimAt [CharP R 2] [CharP S 2] {p : Nat} (x : R) (output : Fin (2^(p+4)) → Fin 25 → R)
    (t : Transcript R p) (d : Fin 13) :
    claimAt (f x) (fun b l => f (output b l)) (t.map f) d = (claimAt x output t d).map f := by
  unfold claimAt
  split_ifs
  · exact map_firstClaim f _ _ _
  · exact map_nextClaim f _
/-- The terminal input-slot selector commutes with scalar transport. -/
theorem map_inputWeight [CharP R 2] [CharP S 2] {p : Nat} (c : Claim R p) (slot z : Fin 64) :
    inputWeight (c.map f) slot z = f (inputWeight c slot z) := by
  unfold inputWeight Claim.map
  split_ifs <;> simp only [map_mul, map_sub, map_one, map_zero]
/-- Zero-padded multilinear evaluation commutes with scalar transport. -/
theorem map_padded_mle {n m : Nat} (a : Fin m → R) (r : Fin n → R) :
    mle (fun j : Fin (2^n) => if h : j.val < m then f (a ⟨j.val,h⟩) else 0)
      (fun i => f (r i)) =
    f (mle (fun j : Fin (2^n) => if h : j.val < m then a ⟨j.val,h⟩ else 0) r) := by
  rw [← map_mle]
  congr 1
  funext j
  split <;> simp only [map_zero]
/-- An injective ring map preserves and reflects every layer equation. -/
theorem map_layerValid_iff [CharP R 2] [CharP S 2] (hf : Function.Injective f) {p : Nat}
    (d : Fin 12) (c : Claim R p) (t : LayerTranscript R p) :
    layerValid d (c.map f) (t.map f) ↔ layerValid d c t := by
  unfold layerValid
  rw [map_constantContribution]
  simp only [Claim.map, LayerTranscript.map, map_projectMessage, map_polyEval, map_packEnd, map_positionEnd,
    map_eqEval, map_muAt, cofactor_roundsValid, compressed_roundsValid,
    true_and, ← map_mul, ← map_add, ← map_sum, hf.eq_iff]
  have padded := map_padded_mle f (n := 11) (m := 1600) c.weights t.positionPoint
  simp only [Nat.reducePow] at padded
  rw [padded]
  simp only [← map_mul, hf.eq_iff]
/-- An injective ring map preserves and reflects both terminal openings. -/
theorem map_openingsValid_iff [CharP R 2] [CharP S 2] (hf : Function.Injective f) {p : Nat}
    (c : Claim R p) (t : Transcript R p) :
    openingsValid (c.map f) (t.map f) ↔ openingsValid c t := by
  have output : (fun slot : Fin 64 => if h : 25 ≤ slot.val ∧ slot.val < 50 then
      (1-(t.map f).segment)*eqWeight (t.map f).lanePoint (slot.val-25) else 0) =
      fun slot => f (if h : 25 ≤ slot.val ∧ slot.val < 50 then
        (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0) := by
    funext slot
    split <;> simp only [Transcript.map, map_eqWeight, map_mul, map_sub, map_one, map_zero]
  unfold openingsValid
  rw [output]
  simp only [Transcript.map, OpeningTranscript.map, map_inputWeight]
  simp only [Claim.map, compressed_roundsValid, true_and, map_positionEnd,
    map_mle (n := 6), ← map_mul, ← map_sum]
  have outputEval := map_mle f (n := 6) (fun slot : Fin 64 => if h : 25 ≤ slot.val ∧ slot.val < 50 then
      (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0) t.openings.outputPoint
  have inputEval := map_mle f (n := 4) c.mu (fun i => t.openings.inputPoint ⟨i.val, by omega⟩)
  simp only [Nat.reducePow] at outputEval inputEval
  rw [outputEval, inputEval]
  simp only [← map_mul, hf.eq_iff]
/-- An injective ring map preserves and reflects complete GKR acceptance. -/
theorem map_accepts_iff [CharP R 2] [CharP S 2] (hf : Function.Injective f) {p : Nat}
    (x : R) (output : Fin (2^(p+4)) → Fin 25 → R) (t : Transcript R p) :
    Accepts (f x) (fun b l => f (output b l)) (t.map f) ↔ Accepts x output t := by
  simp only [Accepts, map_claimAt, show (t.map f).layers = fun i => (t.layers i).map f from rfl, map_layerValid_iff f hf, map_openingsValid_iff f hf]
end
end
end CompStark.Keccak.Gkr
