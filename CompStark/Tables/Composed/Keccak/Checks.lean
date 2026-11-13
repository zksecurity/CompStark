/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Composed.Keccak.Start
public import CompStark.Keccak.Gkr.Tensor
public import CompStark.Keccak.Gkr.Transport

/-! The Keccak-f GKR's acceptance as a decision: every layer's sumcheck and projection checks and
the two terminal opening sumchecks, with the transmitted output lanes as a constant output table,
whose extension at any point is the transmitted value (`outputTable_mle`). -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Composed

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System

/-- Decide a finite sumcheck block by its round checks. -/
def roundsDecidable {F N : Type} : {n : ℕ} → (ops : Fin n → Sumcheck.MessageOps F N) →
    (polys : Fin n → N) → (challenges : Fin n → F) → (value : F) →
    Decidable (Keccak.Gkr.roundsValid ops polys challenges value)
  | 0, _, _, _, _ => isTrue trivial
  | _ + 1, ops, polys, challenges, value =>
      @instDecidableAnd ((ops 0).accept value (polys 0) = true)
        (Keccak.Gkr.roundsValid (fun i => ops i.succ) (fun i => polys i.succ)
          (fun i => challenges i.succ) ((ops 0).evaluate value (polys 0) (challenges 0)))
        inferInstance (roundsDecidable (fun i => ops i.succ) (fun i => polys i.succ)
          (fun i => challenges i.succ) ((ops 0).evaluate value (polys 0) (challenges 0)))

/-- Sumcheck blocks are decided by their round checks. -/
instance roundsInstance {F N : Type} {n : ℕ} (ops : Fin n → Sumcheck.MessageOps F N)
    (polys : Fin n → N) (challenges : Fin n → F) (value : F) :
    Decidable (Keccak.Gkr.roundsValid ops polys challenges value) :=
  roundsDecidable ops polys challenges value

/-- A claim with its position weights materialized. -/
def cacheClaim {p : ℕ} (c : Keccak.Gkr.Claim E p) : Keccak.Gkr.Claim E p :=
  let image := Vector.ofFn c.weights
  { c with weights := fun i => image[i] }

/-- Materializing a claim's weights leaves the claim. -/
theorem cacheClaim_eq {p : ℕ} (c : Keccak.Gkr.Claim E p) : cacheClaim c = c := by
  simp only [cacheClaim, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Decide a layer's checks. -/
@[noinline] def layerDecidableRaw {p : ℕ} (d : Fin 12) (c : Keccak.Gkr.Claim E p)
    (t : Keccak.Gkr.LayerTranscript E p) : Decidable (Keccak.Gkr.layerValid d c t) := by
  unfold Keccak.Gkr.layerValid
  infer_instance

/-- Decide a layer's checks with its claim's weights shared between them. -/
def layerDecidable {p : ℕ} (d : Fin 12) (c : Keccak.Gkr.Claim E p)
    (t : Keccak.Gkr.LayerTranscript E p) : Decidable (Keccak.Gkr.layerValid d c t) := by
  letI := layerDecidableRaw d (cacheClaim c) t
  exact decidable_of_iff (Keccak.Gkr.layerValid d (cacheClaim c) t) (by rw [cacheClaim_eq])

/-- Decide the terminal opening checks. -/
@[noinline] def openingsDecidableRaw {p : ℕ} (c : Keccak.Gkr.Claim E p)
    (t : Keccak.Gkr.Transcript E p) : Decidable (Keccak.Gkr.openingsValid c t) := by
  unfold Keccak.Gkr.openingsValid Keccak.Gkr.inputWeight
  infer_instance

/-- Decide the terminal opening checks with the claim's weights shared between them. -/
def openingsDecidable {p : ℕ} (c : Keccak.Gkr.Claim E p)
    (t : Keccak.Gkr.Transcript E p) : Decidable (Keccak.Gkr.openingsValid c t) := by
  letI := openingsDecidableRaw (cacheClaim c) t
  exact decidable_of_iff (Keccak.Gkr.openingsValid (cacheClaim c) t) (by rw [cacheClaim_eq])

/-- The three-word carrier has characteristic two. -/
instance wordCharP : CharP BF64.WordExt3 2 :=
  BF64.WordExt3.ringEquiv.toRingHom.charP BF64.WordExt3.ringEquiv.injective 2

/-- The specification extension into its three-word carrier. -/
def toWord : E →+* BF64.WordExt3 := BF64.WordExt3.ringEquiv.symm.toRingHom

/-- The carrier map is injective. -/
theorem toWord_injective : Function.Injective toWord := BF64.WordExt3.ringEquiv.symm.injective

/-- A claim over any field with its position weights materialized. -/
def cacheClaimAt {F : Type} {p : ℕ} (c : Keccak.Gkr.Claim F p) : Keccak.Gkr.Claim F p :=
  let image := Vector.ofFn c.weights
  { c with weights := fun i => image[i] }

/-- Materializing a claim's weights leaves the claim. -/
theorem cacheClaimAt_eq {F : Type} {p : ℕ} (c : Keccak.Gkr.Claim F p) : cacheClaimAt c = c := by
  simp only [cacheClaimAt, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Decide a layer's checks over the three-word carrier. -/
@[noinline] def layerDecidableWord {p : ℕ} (d : Fin 12) (c : Keccak.Gkr.Claim BF64.WordExt3 p)
    (t : Keccak.Gkr.LayerTranscript BF64.WordExt3 p) : Decidable (Keccak.Gkr.layerValid d c t) := by
  unfold Keccak.Gkr.layerValid
  infer_instance

/-- Decide the terminal opening checks over the three-word carrier. -/
@[noinline] def openingsDecidableWord {p : ℕ} (c : Keccak.Gkr.Claim BF64.WordExt3 p)
    (t : Keccak.Gkr.Transcript BF64.WordExt3 p) : Decidable (Keccak.Gkr.openingsValid c t) := by
  unfold Keccak.Gkr.openingsValid Keccak.Gkr.inputWeight
  infer_instance

/-- The GKR's first claim with transmitted output-lane values `values`, over any ring. -/
def firstClaimWith {F : Type} [CommRing F] {p : ℕ} (x : F) (values : Fin 25 → F)
    (t : Keccak.Gkr.Transcript F p) : Keccak.Gkr.Claim F p where
  value := t.middleValue + t.segment * ∑ l : Fin 25, Keccak.Gkr.eqWeight t.lanePoint l.val * values l
  mu := fun i => Keccak.Gkr.eqWeight (fun b : Fin 4 => t.instancePoint ⟨b.val, by omega⟩) i.val
  point := Fin.lastCases t.segment (fun b : Fin p => t.instancePoint ⟨b.val + 4, by omega⟩)
  weights := fun j => Keccak.Gkr.eqWeight t.lanePoint (j.val / 64) * x ^ (j.val % 64)

/-- The first claim commutes with a ring map. -/
theorem map_firstClaimWith {R F : Type} [CommRing R] [CommRing F] (f : R →+* F) {p : ℕ} (x : R)
    (values : Fin 25 → R) (t : Keccak.Gkr.Transcript R p) :
    firstClaimWith (f x) (fun l => f (values l)) (t.map f) = (firstClaimWith x values t).map f := by
  unfold firstClaimWith Keccak.Gkr.Transcript.map Keccak.Gkr.Claim.map
  simp only [Keccak.Gkr.map_eqWeight, map_sum, map_add, map_mul, map_pow]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun b => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

/-- The GKR's acceptance from a given first claim: every layer against its claim, the openings
against the last. -/
def acceptsFrom {F : Type} [CommRing F] [CharP F 2] {p : ℕ} (first : Keccak.Gkr.Claim F p)
    (t : Keccak.Gkr.Transcript F p) : Prop :=
  (∀ d : Fin 12, Keccak.Gkr.layerValid d
    (if h : d.val = 0 then first else Keccak.Gkr.nextClaim (t.layers ⟨d.val - 1, by omega⟩)) (t.layers d)) ∧
    Keccak.Gkr.openingsValid (Keccak.Gkr.nextClaim (t.layers (Fin.last 11))) t

/-- An injective ring map preserves and reflects acceptance from a first claim. -/
theorem map_acceptsFrom_iff {R F : Type} [CommRing R] [CommRing F] [CharP R 2] [CharP F 2] (f : R →+* F)
    (hf : Function.Injective f) {p : ℕ} (first : Keccak.Gkr.Claim R p) (t : Keccak.Gkr.Transcript R p) :
    acceptsFrom (first.map f) (t.map f) ↔ acceptsFrom first t := by
  unfold acceptsFrom
  have layers : ∀ i, (t.map f).layers i = (t.layers i).map f := fun _ => rfl
  simp only [layers, Keccak.Gkr.map_nextClaim f]
  refine and_congr (forall_congr' fun d => ?_) (Keccak.Gkr.map_openingsValid_iff f hf _ t)
  by_cases h : d.val = 0
  · simp only [h, ↓reduceDIte]
    exact Keccak.Gkr.map_layerValid_iff f hf d first (t.layers d)
  · simp only [h, ↓reduceDIte]
    exact Keccak.Gkr.map_layerValid_iff f hf d _ (t.layers d)

/-- Acceptance from a first claim over the three-word carrier, each claim's weights materialized
once. -/
def acceptsFromWord {p : ℕ} (first : Keccak.Gkr.Claim BF64.WordExt3 p)
    (t : Keccak.Gkr.Transcript BF64.WordExt3 p) : Bool :=
  (List.finRange 12).all (fun d => @decide _ (layerDecidableWord d (cacheClaimAt
      (if h : d.val = 0 then first else Keccak.Gkr.nextClaim (t.layers ⟨d.val - 1, by omega⟩))) (t.layers d))) &&
    @decide _ (openingsDecidableWord (cacheClaimAt (Keccak.Gkr.nextClaim (t.layers (Fin.last 11)))) t)

/-- The carrier checks decide acceptance from a first claim. -/
theorem acceptsFromWord_iff {p : ℕ} (first : Keccak.Gkr.Claim BF64.WordExt3 p)
    (t : Keccak.Gkr.Transcript BF64.WordExt3 p) :
    acceptsFromWord first t = true ↔ acceptsFrom first t := by
  unfold acceptsFromWord acceptsFrom
  rw [Bool.and_eq_true, List.all_eq_true, @decide_eq_true_iff _ (openingsDecidableWord _ _), cacheClaimAt_eq]
  refine and_congr ⟨fun h d => ?_, fun h d _ => ?_⟩ Iff.rfl
  · have := h d (List.mem_finRange d)
    rwa [@decide_eq_true_iff _ (layerDecidableWord _ _ _), cacheClaimAt_eq] at this
  · rw [@decide_eq_true_iff _ (layerDecidableWord _ _ _), cacheClaimAt_eq]
    exact h d

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

namespace KeccakTable

/-- The constant output table's extension at any point is the transmitted value. -/
theorem outputTable_mle (out : TableSumcheck.Output S L k) (point : Fin (kt.p + 4) → E) (l : Fin 25) :
    Keccak.Gkr.mle (fun b => kt.outputTable out b l) point =
      out.values ⟨kt.table, kt.active⟩ (kt.outputIndex l) := by
  simp only [Keccak.Gkr.mle, outputTable, ← Finset.sum_mul, Keccak.Gkr.eqWeight_sum, one_mul]

/-- The GKR's first claim with the transmitted output values. -/
def firstClaim (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) :
    Keccak.Gkr.Claim E kt.p where
  value := t.middleValue + t.segment *
    ∑ l : Fin 25, Keccak.Gkr.eqWeight t.lanePoint l.val * out.values ⟨kt.table, kt.active⟩ (kt.outputIndex l)
  mu := fun i => Keccak.Gkr.eqWeight (fun b : Fin 4 => t.instancePoint ⟨b.val, by omega⟩) i.val
  point := Fin.lastCases t.segment (fun b : Fin kt.p => t.instancePoint ⟨b.val + 4, by omega⟩)
  weights := fun j => Keccak.Gkr.eqWeight t.lanePoint (j.val / 64) * ofK g ^ (j.val % 64)

/-- The first claim with the constant output table is the claim with the transmitted values. -/
theorem firstClaim_eq (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) :
    Keccak.Gkr.firstClaim (ofK g) (kt.outputTable out) t = kt.firstClaim out t := by
  simp only [Keccak.Gkr.firstClaim, Keccak.Gkr.outputClaimAt, outputTable_mle, firstClaim]

/-- The GKR's acceptance with the transmitted output values: the first layer against the first
claim, every later layer against its predecessor's next claim, and the openings against the last. -/
def Accepts (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) : Prop :=
  (∀ d : Fin 12, Keccak.Gkr.layerValid d
    (if h : d.val = 0 then kt.firstClaim out t else Keccak.Gkr.nextClaim (t.layers ⟨d.val - 1, by omega⟩))
    (t.layers d)) ∧
    Keccak.Gkr.openingsValid (Keccak.Gkr.nextClaim (t.layers (Fin.last 11))) t

/-- The GKR's acceptance with the transmitted values is its acceptance with the constant output
table. -/
theorem accepts_iff (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) :
    kt.Accepts out t ↔ Keccak.Gkr.Accepts (ofK g) (kt.outputTable out) t := by
  unfold Accepts Keccak.Gkr.Accepts Keccak.Gkr.claimAt
  simp only [Fin.val_castSucc, Fin.val_last, firstClaim_eq]
  rfl

/-- The GKR's acceptance is decided layer by layer. -/
instance acceptsDecidable (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) :
    Decidable (kt.Accepts out t) := by
  letI := fun (d : Fin 12) (c : Keccak.Gkr.Claim E kt.p) (l : Keccak.Gkr.LayerTranscript E kt.p) =>
    layerDecidable d c l
  letI := fun (c : Keccak.Gkr.Claim E kt.p) (t : Keccak.Gkr.Transcript E kt.p) => openingsDecidable c t
  unfold Accepts
  infer_instance

/-- The GKR's checks decided over the three-word carrier. -/
def acceptsWord (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) : Bool :=
  acceptsFromWord (firstClaimWith (toWord (ofK g))
    (fun l => toWord (out.values ⟨kt.table, kt.active⟩ (kt.outputIndex l))) (t.map toWord)) (t.map toWord)

/-- The carrier decision is the GKR's acceptance. -/
theorem acceptsWord_eq (out : TableSumcheck.Output S L k) (t : Keccak.Gkr.Transcript E kt.p) :
    kt.acceptsWord out t = decide (kt.Accepts out t) := by
  refine Bool.eq_iff_iff.mpr ((acceptsFromWord_iff _ _).trans (Iff.trans ?_ decide_eq_true_iff.symm))
  rw [map_firstClaimWith toWord]
  exact map_acceptsFrom_iff toWord toWord_injective _ t

end KeccakTable

end CompStark.Tables.Composed
