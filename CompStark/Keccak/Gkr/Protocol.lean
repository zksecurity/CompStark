/-
Copyright (c) 2026 zkSecurity.
The protocol follows leanEthereum/leanMultisig (Apache-2.0),
revision 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, annex C and crates/keccak_gkr/src.
-/
module

public import CompStark.Keccak.Embedding
public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.ProofSystem.Sumcheck.Message.Compressed

/-!
# Two-segment Keccak GKR: protocol and layer algebra

`p` counts pack variables, so annex C's `kbatch` is `p + 4`. The initial sampling
adapter includes the externally drawn instance point; it is sampled after the committed
oracle table is fixed. `output` is the fixed table underlying the externally supplied
25 output-lane multilinear claims. Its evaluations are public inputs to the reduction.
Transmitted cofactor tails and compressed Boolean messages decode against each round's
running claim to the bounded-degree polynomials used by annex C. Knowledge states retain the PCS-supplied table. The generic sumcheck
certificate plugs into `roundsValid` at each block.
-/

set_option maxRecDepth 4096

@[expose] public section
namespace CompStark.Keccak.Gkr

open Polynomial Interaction.Oracle Interaction.Oracle.Security
open scoped BigOperators ENNReal

/-- A little-endian Boolean-cube index has one field weight per coordinate. -/
def eqWeight {E : Type*} [CommRing E] {n : Nat} (r : Fin n → E) (index : Nat) : E :=
  ∏ i : Fin n, if index.testBit i.val then r i else 1 - r i

/-- Multilinear evaluation of a complete, little-endian cube table. -/
def mle {E : Type*} [CommRing E] {n : Nat} (a : Fin (2^n) → E) (r : Fin n → E) : E :=
  ∑ b : Fin (2^n), eqWeight r b.val * a b

/-- Equality polynomial evaluated at two field points. -/
def eqEval {E : Type*} [CommRing E] {n : Nat} (r s : Fin n → E) : E :=
  ∏ i : Fin n, ((1-r i)*(1-s i) + r i*s i)

/-- Bit position `z + 64*(x+5*y)` shifted along its row by `k`. -/
def along (j : Fin 1600) (k : Nat) : Fin 1600 :=
  ⟨64 * ((j.val / 64 % 5 + k) % 5 + 5 * (j.val / 64 / 5)) + j.val % 64, by omega⟩

/-- FIPS 202's lane rotation amounts, in `x+5*y` order. -/
def rho : Fin 25 → Nat :=
  ![0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]

/-- Constant-time lane rotation lookup. -/
def rhoFast (i : Fin 25) : Nat :=
  (#[0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14] : Array Nat)[i.val]'i.isLt
/-- The array lookup agrees with the FIPS lane table. -/
@[csimp] theorem rho_code : rho = rhoFast := by
  have checked : ∀ i : Fin 25, rho i = rhoFast i := by decide
  exact funext checked

/-- The inverse pi lane map. -/
def inversePi (lane : Nat) : Fin 25 :=
  ⟨(lane % 5 + 3 * (lane / 5)) % 5 + 5 * (lane % 5), by omega⟩

/-- Theta followed by rho and pi, over any commutative coefficient ring. -/
def linear {E : Type*} [CommRing E] (a : Fin 1600 → E) (j : Fin 1600) : E :=
  let l := inversePi (j.val / 64)
  let z := (j.val % 64 + 64 - rho l) % 64
  a ⟨64*l.val+z, by omega⟩ +
    (∑ y : Fin 5, a ⟨64*((l.val%5+4)%5+5*y.val)+z, by omega⟩) +
    (∑ y : Fin 5, a ⟨64*((l.val%5+1)%5+5*y.val)+(z+63)%64, by omega⟩)

/-- The transpose sends position weights backward through theta, rho, and pi. -/
def linearTranspose {E : Type*} [CommRing E] (w : Fin 1600 → E) (i : Fin 1600) : E :=
  ∑ j, w j * linear (fun k => if k = i then 1 else 0) j

/-- The transpose is adjoint to the linear Keccak layer. -/
theorem linearTranspose_adjoint {E : Type*} [CommRing E]
    (w a : Fin 1600 → E) :
    ∑ j, w j * linear a j = ∑ i, linearTranspose w i * a i := by
  have expansion (j : Fin 1600) :
      linear a j = ∑ i, linear (fun k => if k = i then 1 else 0) j * a i := by
    simp only [linear, add_mul, Finset.sum_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 1600)))
      (t := (Finset.univ : Finset (Fin 5)))]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [linearTranspose, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [expansion j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_assoc _ _ _).symm

/-- The 24 iota words, indexed from round zero in the source. -/
def roundConstants : Fin 24 → Nat :=
  ![0x0000000000000001,0x0000000000008082,0x800000000000808A,0x8000000080008000,
    0x000000000000808B,0x0000000080000001,0x8000000080008081,0x8000000000008009,
    0x000000000000008A,0x0000000000000088,0x0000000080008009,0x000000008000000A,
    0x000000008000808B,0x800000000000008B,0x8000000000008089,0x8000000000008003,
    0x8000000000008002,0x8000000000000080,0x000000000000800A,0x800000008000000A,
    0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008]

/-- Bounded array lookup of the pinned iota words. -/
def roundConstantsFast (i : Fin 24) : Nat :=
  (#[0x0000000000000001,0x0000000000008082,0x800000000000808A,0x8000000080008000,
    0x000000000000808B,0x0000000080000001,0x8000000080008081,0x8000000000008009,
    0x000000000000008A,0x0000000000000088,0x0000000080008009,0x000000008000000A,
    0x000000008000808B,0x800000000000008B,0x8000000000008089,0x8000000000008003,
    0x8000000000008002,0x8000000000000080,0x000000000000800A,0x800000008000000A,
    0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008] : Array Nat)[i.val]'i.isLt

/-- Array lookup agrees with all twenty-four pinned iota words. -/
@[csimp] theorem roundConstants_code : roundConstants = roundConstantsFast := by
  have checked : ∀ i : Fin 24, roundConstants i = roundConstantsFast i := by decide
  exact funext checked

/-- One zero-indexed Keccak round, including its public round constant. -/
def round (r : Fin 24) (a : Fin 1600 → ZMod 2) (j : Fin 1600) : ZMod 2 :=
  let b := linear a
  b j + (1 + b (along j 1)) * b (along j 2) +
    if j.val < 64 ∧ (roundConstants r).testBit j.val then 1 else 0

/-- The committed table has 64 slots; the fourteen unused slots still participate in openings. -/
abbrev Witness (p : Nat) := Fin (2^(p+4)) → Fin 64 → Fin 64 → ZMod 2

/-- The two committed starting states occupy lanes `25*m+l`. -/
def startState {p : Nat} (q : Witness p) (permutation : Fin (2^(p+4)))
    (m : Fin 2) (j : Fin 1600) : ZMod 2 :=
  q permutation ⟨25*m.val+j.val/64, by omega⟩ ⟨j.val%64, by omega⟩

/-- Execute at most twelve rounds of one segment, with its actual FIPS round numbers. -/
def segmentState {p : Nat} (q : Witness p) (permutation : Fin (2^(p+4)))
    (m : Fin 2) : (e : Nat) → e ≤ 12 → Fin 1600 → ZMod 2
  | 0, _ => startState q permutation m
  | e+1, he => round ⟨12*m.val+e, by omega⟩ (segmentState q permutation m e (by omega))

/-- A 64-bit lane interpreted in the field's polynomial basis. -/
def laneValue {E : Type*} [CommRing E] [CharP E 2] (x : E)
    (bits : Fin 64 → ZMod 2) : E :=
  ∑ z, ZMod.castHom (dvd_refl 2) E (bits z) * x ^ z.val

/-- The initial witness relation states every output lane and every middle-state chain bit. -/
def InputRelation {E : Type*} [CommRing E] [CharP E 2] {p : Nat} (x : E)
    (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) : Prop :=
  (∀ b j, segmentState q b 0 12 (by omega) j = startState q b 1 j) ∧
    ∀ b l, output b l = laneValue x
      (fun z => segmentState q b 1 12 (by omega) ⟨z.val+64*l.val, by omega⟩)

/-- One GKR claim, including the segment coordinate after the pack coordinates. -/
structure Claim (E : Type*) (p : Nat) where
  /-- Claimed weighted sum. -/
  value : E
  /-- In-pack instance weights. -/
  mu : Fin 16 → E
  /-- Pack coordinates followed by the segment coordinate. -/
  point : Fin (p+1) → E
  /-- Position weights, zero-padded to 2048 only when multilinearly evaluated. -/
  weights : Fin 1600 → E

/-- Low four instance bits followed by the pack index. -/
def packInstance {p : Nat} (i : Fin 16) (b : Fin (2^p)) : Fin (2^(p+4)) :=
  ⟨i.val+16*b.val, by rw [pow_add]; norm_num; omega⟩

/-- The semantic weighted claim at depth `d` of the twelve-layer reduction. -/
def ClaimHolds {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 13) (c : Claim E p) : Prop :=
  c.value = ∑ m : Fin 2, ∑ b : Fin (2^p), ∑ i : Fin 16, ∑ j : Fin 1600,
    eqWeight c.point (b.val+2^p*m.val) * c.mu i * c.weights j *
      ZMod.castHom (dvd_refl 2) E
        (segmentState q (packInstance i b) m (12-d.val) (by omega) j)

/-- Evaluate a full coefficient message at a scalar challenge. -/
def polyEval {E : Type*} [CommRing E] {n : Nat} (coeffs : Fin n → E) (s : E) : E :=
  ∑ i, coeffs i * s ^ i.val

/-- The two transmitted positive-degree coefficients of a quadratic cofactor. -/
abbrev CofactorMessage (E : Type) := Sumcheck.CompressedMessage E 1

/-- Transmitted coordinates in their absorb order, with the first scalar before the tail. -/
def messageVector {E : Type} {d : Nat} (m : Sumcheck.CompressedMessage E d) : Fin (d+1) → E :=
  Fin.cons m.1 m.2

/-- The transmitted vector determines its message. -/
theorem messageVector_injective {E : Type} {d : Nat} :
    Function.Injective (@messageVector E d) := by
  intro a b h
  exact Prod.ext (congrFun h 0) (funext fun i => congrFun h i.succ)

/-- Read a transmitted vector into its first scalar and remaining coordinates. -/
def vectorMessage {E : Type} {d : Nat} (v : Fin (d+1) → E) : Sumcheck.CompressedMessage E d :=
  (v 0, fun i => v i.succ)

/-- Encoding a transmitted vector preserves every scalar. -/
@[simp] theorem messageVector_vectorMessage {E : Type} {d : Nat} (v : Fin (d+1) → E) :
    messageVector (vectorMessage v) = v := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Decoding the transmitted coordinates preserves the message. -/
@[simp] theorem vectorMessage_messageVector {E : Type} {d : Nat}
    (m : Sumcheck.CompressedMessage E d) : vectorMessage (messageVector m) = m := rfl

/-- The full cubic evaluated by a pack round, including its known equality factor. -/
def cofactorOps {E : Type} [CommRing E] (r : E) : Sumcheck.MessageOps E (CofactorMessage E) where
  evaluate c m x := (1+r+x) * (c+r*(m.1+m.2 0)+m.1*x+m.2 0*x^2)
  accept _ _ := true

/-- The degree-three polynomial represented by a claim-aware cofactor pair. -/
noncomputable def cofactorPolynomial {E : Type} [CommRing E]
    (r c : E) (m : CofactorMessage E) : E⦃≤ 3⦄[X] :=
  ⟨(C (1+r)+X) * (C (c+r*(m.1+m.2 0))+C m.1*X+C (m.2 0)*X^2), by
    apply Polynomial.mem_degreeLE.mpr
    apply (Polynomial.degree_mul_le _ _).trans
    have left : (C (1+r)+X : E[X]).degree ≤ 1 :=
      degree_add_le_of_degree_le (degree_C_le.trans (by norm_num)) degree_X_le
    have right : (C (c+r*(m.1+m.2 0))+C m.1*X+C (m.2 0)*X^2 : E[X]).degree ≤ 2 := by
      apply degree_add_le_of_degree_le
      · apply degree_add_le_of_degree_le
        · exact degree_C_le.trans (by norm_num)
        · simpa only [pow_one] using (degree_C_mul_X_pow_le 1 m.1).trans (by norm_num)
      · exact degree_C_mul_X_pow_le 2 (m.2 0)
    exact (add_le_add left right).trans (by norm_num)⟩

/-- Runtime cofactor evaluation agrees with the full cubic interpretation. -/
theorem cofactor_evaluate_eq {E : Type} [CommRing E] (r c : E) (m : CofactorMessage E) (x : E) :
    (cofactorOps r).evaluate c m x = (cofactorPolynomial r c m).val.eval x := by
  simp only [cofactorOps, cofactorPolynomial, eval_mul, eval_add, eval_C, eval_X, eval_pow]

/-- The equality-factored cubic has the prescribed Boolean sum in characteristic two. -/
theorem cofactor_boolean_sum {E : Type} [CommRing E] [CharP E 2]
    (r c : E) (m : CofactorMessage E) :
    (cofactorPolynomial r c m).val.eval 0 + (cofactorPolynomial r c m).val.eval 1 = c := by
  rw [← cofactor_evaluate_eq, ← cofactor_evaluate_eq]
  simp only [cofactorOps, zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, mul_one, add_zero]
  have htwo : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hthree : (3 : E) = 1 := by calc
    _ = (2 : E) + 1 := by norm_num
    _ = 1 := by rw [htwo, zero_add]
  have hfour : (4 : E) = 0 := by calc
    _ = (2 : E) * 2 := by norm_num
    _ = 0 := by rw [htwo, mul_zero]
  ring_nf
  simp only [htwo, hthree, hfour, mul_zero, mul_one, zero_add, add_zero]

/-- The pack cofactor pair represents a cubic under the ordinary Boolean sumcheck contract. -/
noncomputable def cofactorModel {E : Type} [CommRing E] [CharP E 2] [DecidableEq E]
    [Nontrivial E] (r : E) : Sumcheck.MessageModel ({0,1} : Finset E) (cofactorOps r) 3 where
  interpret := cofactorPolynomial r
  evaluate_eq := cofactor_evaluate_eq r
  accept_iff c m := by
    simpa only [cofactorOps, Finset.sum_pair (zero_ne_one : (0 : E) ≠ 1), true_iff]
      using cofactor_boolean_sum r c m

/-- Round-specific operations retain the incoming equality coordinate at every pack round. -/
def packOps {E : Type} [CommRing E] {n : Nat} (point : Fin n → E) :
    Fin n → Sumcheck.MessageOps E (CofactorMessage E) := fun i => cofactorOps (point i)

/-- Final running claim of a block with claim-aware, round-specific decoding. -/
def roundsEnd {E M : Type} : {n : Nat} → (Fin n → Sumcheck.MessageOps E M) →
    (Fin n → M) → (Fin n → E) → E → E
  | 0, _, _, _, value => value
  | _+1, ops, polys, challenges, value => roundsEnd (fun i => ops i.succ)
      (fun i => polys i.succ) (fun i => challenges i.succ)
      ((ops 0).evaluate value (polys 0) (challenges 0))

/-- Each transmitted message satisfies its model's Boolean sum check before the fresh challenge. -/
def roundsValid {E M : Type} : {n : Nat} → (Fin n → Sumcheck.MessageOps E M) →
    (Fin n → M) → (Fin n → E) → E → Prop
  | 0, _, _, _, _ => True
  | _+1, ops, polys, challenges, value =>
      (ops 0).accept value (polys 0) = true ∧
      roundsValid (fun i => ops i.succ) (fun i => polys i.succ) (fun i => challenges i.succ)
        ((ops 0).evaluate value (polys 0) (challenges 0))

/-- One complete layer transcript, retaining exactly the transmitted scalars. -/
structure LayerTranscript (E : Type) (p : Nat) where
  /-- Degree-at-most-46 product polynomial. -/
  product : Fin 47 → E
  /-- Fresh polynomial evaluation point, after the product message. -/
  point : E
  /-- Pack and segment quadratic cofactor tails. -/
  packPolys : Fin (p+1) → CofactorMessage E
  /-- Fresh pack and segment challenges. -/
  packPoint : Fin (p+1) → E
  /-- Eleven compressed position cubics, slice coordinates before lanes. -/
  positionPolys : Fin 11 → Sumcheck.CompressedMessage E 2
  /-- Fresh position challenges. -/
  positionPoint : Fin 11 → E
  /-- The three claimed shifted evaluations, before beta. -/
  evaluations : Fin 3 → E
  /-- Fresh quadratic batching challenge. -/
  beta : E

/-- In-pack weights after evaluating the sixteen embedding columns. -/
def muAt {E : Type*} [CommRing E] (s : E) (i : Fin 16) : E :=
  Embedding.evaluateCoeffs s (Embedding.basisCoeffs i)

/-- The computed mask weight is the evaluation of the RMFE basis polynomial. -/
theorem muAt_eq_eval {E : Type*} [CommRing E] [CharP E 2] (s : E) (i : Fin 16) :
    muAt s i = ((Embedding.basis i).map (ZMod.castHom (dvd_refl 2) E)).eval s :=
  Embedding.evaluateCoeffs_eq s (Embedding.basisCoeffs i)

/-- Project a 47-coefficient message using the exact RMFE masks. -/
def projectMessage {E : Type*} [CommRing E] (a : Fin 47 → E) (i : Fin 16) : E :=
  ∑ c : Fin 47, if (Embedding.projectionWords i).testBit c.val then a c else 0

/-- The round constant contribution, summed over both segments. -/
def constantContribution {E : Type*} [CommRing E] (d : Fin 12) {p : Nat} (c : Claim E p) : E :=
  (∑ i, c.mu i) * ∑ m : Fin 2,
    (if m.val = 0 then 1-c.point (Fin.last p) else c.point (Fin.last p)) *
      ∑ z : Fin 64, if (roundConstants ⟨12*(m.val+1)-d.val-1, by omega⟩).testBit z
        then c.weights ⟨z.val, by omega⟩ else 0

/-- Batch the three shifted position claims and transpose the linear map onto their weights. -/
def nextClaim {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (t : LayerTranscript E p) : Claim E p where
  value := t.evaluations 0 + t.beta*t.evaluations 1 + t.beta^2*t.evaluations 2
  mu := muAt t.point
  point := t.packPoint
  weights := linearTranspose fun j => eqWeight t.positionPoint j.val +
    t.beta*eqWeight t.positionPoint (along j 4).val +
    t.beta^2*eqWeight t.positionPoint (along j 3).val

/-- All deterministic verifier checks in one layer. -/
noncomputable def layerValid {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) : Prop :=
  (∑ i, c.mu i * projectMessage t.product i) + constantContribution d c = c.value ∧
    roundsValid (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point) ∧
    roundsValid (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint
      (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point)) ∧
    roundsEnd (fun _ => Sumcheck.compressedOps 2) t.positionPolys t.positionPoint
      (roundsEnd (packOps c.point) t.packPolys t.packPoint (polyEval t.product t.point)) =
      eqEval c.point t.packPoint *
        mle (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0)
          t.positionPoint *
        ((∑ i, muAt t.point i)*t.evaluations 0 +
          ((∑ i, muAt t.point i)+t.evaluations 1)*t.evaluations 2)

/-- Opening sumchecks and their two output claims. -/
structure OpeningTranscript (E : Type) where
  /-- Six degree-two rounds for the committed middle states. -/
  outputPolys : Fin 6 → Sumcheck.CompressedMessage E 1
  /-- Slot challenges for the word opening. -/
  outputPoint : Fin 6 → E
  /-- Claimed committed word evaluation. -/
  outputValue : E
  /-- Four low-instance and six slot degree-two rounds for the inputs. -/
  inputPolys : Fin 10 → Sumcheck.CompressedMessage E 1
  /-- The input low-instance and slot challenges, in that order. -/
  inputPoint : Fin 10 → E
  /-- The 64 bit-slice evaluations sent after the input sumcheck. -/
  slices : Fin 64 → E

/-- Full public transcript after the committed oracle table is fixed. -/
structure Transcript (E : Type) (p : Nat) where
  /-- The externally drawn instance point, low four coordinates first. -/
  instancePoint : Fin (p+4) → E
  /-- Fresh segment batching challenge. -/
  segment : E
  /-- Five fresh lane batching challenges. -/
  lanePoint : Fin 5 → E
  /-- The prover's segment-weighted committed-middle claim. -/
  middleValue : E
  /-- Twelve layers, each reducing both segments by one round. -/
  layers : Fin 12 → LayerTranscript E p
  /-- The two commitment openings. -/
  openings : OpeningTranscript E

/-- The source reduction's public input: 25 lane evaluations at one batch point. -/
structure OutputClaim (E : Type*) (p : Nat) where
  /-- Instance coordinates, low four bits first. -/
  point : Fin (p+4) → E
  /-- Claimed output-lane evaluations at this point. -/
  lanes : Fin 25 → E

/-- The initial sampling adapter evaluates the fixed public output tables at its challenge. -/
def outputClaimAt {E : Type*} [CommRing E] {p : Nat}
    (output : Fin (2^(p+4)) → Fin 25 → E) (r : Fin (p+4) → E) : OutputClaim E p where
  point := r
  lanes := fun l => mle (fun b => output b l) r

/-- The first weighted claim combines fifty lanes at the external instance point. -/
def firstClaim {E : Type} [CommRing E] {p : Nat} (x : E)
    (output : Fin (2^(p+4)) → Fin 25 → E) (t : Transcript E p) : Claim E p where
  value := t.middleValue + t.segment *
    ∑ l, eqWeight t.lanePoint l.val * (outputClaimAt output t.instancePoint).lanes l
  mu := fun i => eqWeight (fun b : Fin 4 => t.instancePoint ⟨b.val, by omega⟩) i.val
  point := Fin.lastCases t.segment (fun b : Fin p => t.instancePoint ⟨b.val+4, by omega⟩)
  weights := fun j => eqWeight t.lanePoint (j.val/64) * x^(j.val%64)

/-- The claim before layer zero, or after the indicated layer. -/
def claimAt {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (t : Transcript E p) (d : Fin 13) : Claim E p :=
  if h : d.val = 0 then firstClaim x output t
  else nextClaim (t.layers ⟨d.val-1, by omega⟩)

/-- The final input claim's weight on one committed slot and slice. -/
def inputWeight {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (slot z : Fin 64) : E :=
  if h : slot.val < 50 then
    (if slot.val < 25 then 1-c.point (Fin.last p) else c.point (Fin.last p)) *
      c.weights ⟨64*(slot.val%25)+z.val, by omega⟩
  else 0

/-- Both opening sumchecks are checked against their sent terminal values. -/
noncomputable def openingsValid {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (t : Transcript E p) : Prop :=
  roundsValid (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue ∧
  roundsEnd (fun _ => Sumcheck.compressedOps 1) t.openings.outputPolys t.openings.outputPoint t.middleValue =
    mle (fun slot : Fin 64 => if h : 25 ≤ slot.val ∧ slot.val < 50 then
      (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0)
      t.openings.outputPoint * t.openings.outputValue ∧
  roundsValid (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint c.value ∧
  roundsEnd (fun _ => Sumcheck.compressedOps 1) t.openings.inputPolys t.openings.inputPoint c.value =
    mle c.mu (fun i : Fin 4 => t.openings.inputPoint ⟨i.val,by omega⟩) *
      ∑ z, mle (fun slot => inputWeight c slot z)
        (fun i : Fin 6 => t.openings.inputPoint ⟨i.val+4,by omega⟩) * t.openings.slices z

/-- The deterministic verifier accepts exactly the layer and opening equations. -/
noncomputable def Accepts {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (t : Transcript E p) : Prop :=
  (∀ d : Fin 12, layerValid d (claimAt x output t d.castSucc) (t.layers d)) ∧
    openingsValid (claimAt x output t (Fin.last 12)) t

/-- Concatenate an instance point and a six-bit slot point, low coordinates first. -/
def appendSlot {E : Type*} {p : Nat} (permutation : Fin (p+4) → E) (slot : Fin 6 → E) :
    Fin (p+10) → E := fun i =>
  if h : i.val < p+4 then permutation ⟨i.val,h⟩ else slot ⟨i.val-(p+4),by omega⟩

/-- The terminal relation is one committed word claim and 64 committed bit-slice claims.
Ring switching consumes the slices; the PCS consumes the word and switched claims. -/
noncomputable def TerminalRelation {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) : Prop :=
  let wordPoint := appendSlot t.instancePoint t.openings.outputPoint
  let c := nextClaim (t.layers (Fin.last 11))
  let inputInstance : Fin (p+4) → E := fun i => if h : i.val < 4 then
    t.openings.inputPoint ⟨i.val,by omega⟩ else c.point ⟨i.val-4,by omega⟩
  let slicePoint := appendSlot inputInstance
    (fun i : Fin 6 => t.openings.inputPoint ⟨i.val+4,by omega⟩)
  (t.openings.outputValue = mle (fun b : Fin (2^(p+10)) =>
      laneValue x (q ⟨b.val%2^(p+4), Nat.mod_lt _ (by positivity)⟩
        ⟨b.val/2^(p+4), by
          have hpow : 2^(p+10) = 2^(p+4)*64 := by rw [show p+10=p+4+6 by omega, pow_add]; rfl
          apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
          simpa only [Nat.mul_comm, hpow] using b.isLt⟩)) wordPoint) ∧
    ∀ z : Fin 64, t.openings.slices z = mle (fun b : Fin (2^(p+10)) =>
      ZMod.castHom (dvd_refl 2) E (q ⟨b.val%2^(p+4), Nat.mod_lt _ (by positivity)⟩
        ⟨b.val/2^(p+4), by
          have hpow : 2^(p+10) = 2^(p+4)*64 := by rw [show p+10=p+4+6 by omega, pow_add]; rfl
          apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
          simpa only [Nat.mul_comm, hpow] using b.isLt⟩ z)) slicePoint

/-- Each fresh verifier challenge has its own annex C error numerator. -/
inductive Challenge where
  /-- Initial instance coordinates, drawn after the commitment. -/
  | initialInstance (coordinate : Nat)
  /-- Initial segment batching. -/
  | segment
  /-- Initial lane batching. -/
  | lane (coordinate : Nat)
  /-- Evaluation of a layer's degree-46 product. -/
  | productPoint (layer : Nat)
  /-- Cubic pack or segment round. -/
  | packSegment (layer coordinate : Nat)
  /-- Cubic position round. -/
  | position (layer coordinate : Nat)
  /-- Quadratic batching of three shifted evaluations. -/
  | beta (layer : Nat)
  /-- Quadratic committed-middle slot round. -/
  | outputSlot (coordinate : Nat)
  /-- Quadratic input low-instance round. -/
  | inputLow (coordinate : Nat)
  /-- Quadratic input slot round. -/
  | inputSlot (coordinate : Nat)

/-- The degree tested by one fresh challenge. -/
def Challenge.numerator : Challenge → Nat
  | .initialInstance _ | .segment | .lane _ => 1
  | .productPoint _ => 46
  | .packSegment _ _ | .position _ _ => 3
  | .beta _ | .outputSlot _ | .inputLow _ | .inputSlot _ => 2

/-- A public prover coefficient vector or a fresh scalar verifier challenge. -/
inductive WireStep where
  /-- Prover message, with its complete coefficient-vector length. -/
  | message (arity : Nat)
  /-- Fresh verifier challenge, with its per-challenge loss. -/
  | challenge (kind : Challenge)

/-- A block of transmitted scalar messages and fresh challenges. -/
def roundSteps (count degree : Nat) (kind : Nat → Challenge) : List WireStep :=
  (List.range count).flatMap fun i => [.message (degree+1), .challenge (kind i)]

/-- A twelve-round segment layer's public messages, in source order. -/
def layerSteps (p d : Nat) : List WireStep :=
  [.message 47, .challenge (.productPoint d)] ++
    roundSteps (p+1) 1 (.packSegment d) ++ roundSteps 11 2 (.position d) ++
    [.message 3, .challenge (.beta d)]

/-- The complete public-coin schedule, including the external instance-point adapter. -/
def steps (p : Nat) : List WireStep :=
  (List.range (p+4)).map (fun i => .challenge (.initialInstance i)) ++
  [.challenge .segment] ++ (List.range 5).map (fun i => .challenge (.lane i)) ++
  [.message 1] ++ (List.range 12).flatMap (layerSteps p) ++
  roundSteps 6 1 .outputSlot ++ [.message 1] ++
  roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot ++ [.message 64]

/-- Decorated public protocol for the coefficient-message schedule. -/
def wireProtocol (E : Type) (steps : List WireStep) : Interaction.Oracle.Protocol :=
  List.rec Interaction.Oracle.Protocol.done (fun step _ suffix => match step with
    | .message n => Interaction.Oracle.Protocol.public .sender (Fin n → E) fun _ => suffix
    | .challenge _ => Interaction.Oracle.Protocol.public .receiver E fun _ => suffix) steps

/-- Construct each GKR continuation when its public move is read. -/
def wireProtocolLazy (E : Type) : List WireStep → Interaction.Oracle.Protocol
  | [] => .done
  | .message n :: rest => .public .sender (Fin n → E) fun _ => wireProtocolLazy E rest
  | .challenge _ :: rest => .public .receiver E fun _ => wireProtocolLazy E rest

/-- Lazy construction preserves the decorated coefficient-message protocol. -/
@[csimp] theorem wireProtocol_code : wireProtocol = wireProtocolLazy := by
  funext E steps
  induction steps with
  | nil => rfl
  | cons step rest ih => cases step <;> simp only [wireProtocol, wireProtocolLazy, ← ih]

/-- Interaction tree for the public message schedule. -/
def wireTree (E : Type) (steps : List WireStep) : Interaction.Oracle.TypeTree :=
  (wireProtocol E steps).tree

/-- Construct the public interaction tree without its erased protocol decorations. -/
def wireTreeLazy (E : Type) : List WireStep → Interaction.Oracle.TypeTree
  | [] => .done
  | .message n :: rest => .public (Fin n → E) fun _ => wireTreeLazy E rest
  | .challenge _ :: rest => .public E fun _ => wireTreeLazy E rest

/-- Direct interaction-tree construction preserves the decorated protocol's tree. -/
@[csimp] theorem wireTree_code : wireTree = wireTreeLazy := by
  funext E steps
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step <;> simp only [wireTree, wireProtocol, wireTreeLazy,
      Interaction.Oracle.Protocol.public, ← ih]

/-- Sender and receiver roles for every public move. -/
def wireRoles (E : Type) (steps : List WireStep) : (wireTree E steps).RoleDecoration :=
  (wireProtocol E steps).roles

/-- Read public roles without constructing the decorated protocol's tree. -/
def wireRolesLazy (E : Type) : (s : List WireStep) → (wireTree E s).RoleDecoration
  | [] => PUnit.unit
  | .message _ :: rest => ⟨.sender, fun _ => wireRolesLazy E rest⟩
  | .challenge _ :: rest => ⟨.receiver, fun _ => wireRolesLazy E rest⟩

/-- Direct role construction preserves the public protocol decoration. -/
@[csimp] theorem wireRoles_code : wireRoles = wireRolesLazy := by
  funext E steps
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step <;> simp only [wireRoles, wireProtocol, wireRolesLazy,
      Interaction.Oracle.Protocol.public, ← ih] <;> rfl

/-- The public GKR reduction runs after the enclosing PCS fixes the witness table. -/
def protocol (E : Type) (p : Nat) : Interaction.Oracle.TypeTree := wireTree E (steps p)

/-- The public message and fresh verifier-challenge roles. -/
def roles (E : Type) (p : Nat) : (protocol E p).RoleDecoration := wireRoles E (steps p)

/-- Uniform sampling derived from the field's finite enumeration. -/
noncomputable def uniformField (E : Type) [Fintype E] [Nonempty E] : ProbComp E :=
  letI := SampleableType.ofFintype E
  $ᵗ E

/-- Fresh uniform challenges and their losses, at every authored prefix. -/
noncomputable def wireChallenges (E : Type) [Fintype E] [Nonempty E] :
    (s : List WireStep) → RoundExtractor.ChallengeSchedule (wireTree E s) (wireRoles E s)
  | [] => PUnit.unit
  | .message _ :: rest => ⟨PUnit.unit, fun _ => wireChallenges E rest⟩
  | .challenge kind :: rest =>
      ⟨(uniformField E, (kind.numerator : ENNReal) / Fintype.card E), fun _ => wireChallenges E rest⟩

/-- Challenge schedule on the complete committed-oracle protocol. -/
noncomputable def challenges (E : Type) [Fintype E] [Nonempty E] (p : Nat) :
    RoundExtractor.ChallengeSchedule (protocol E p) (roles E p) :=
  wireChallenges E (steps p)

/-- Exact public message vectors retained by one execution path. -/
def pathMessages {E : Type} : (s : List WireStep) → (wireTree E s).ExecutionPath → List (List E)
  | [], _ => []
  | .message _ :: rest, path => List.ofFn path.1 :: pathMessages rest path.2
  | .challenge _ :: rest, path => [path.1] :: pathMessages rest path.2

/-- Wire encoding of transmitted sumcheck messages and scalar challenges. -/
def roundMessages {E : Type} {n degree : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage E degree) (point : Fin n → E) : List (List E) :=
  (List.ofFn fun i => [List.ofFn (messageVector (polys i)), [point i]]).flatten

/-- Wire encoding of one layer. -/
def layerMessages {E : Type} {p : Nat} (t : LayerTranscript E p) : List (List E) :=
  [List.ofFn t.product, [t.point]] ++ roundMessages t.packPolys t.packPoint ++
    roundMessages t.positionPolys t.positionPoint ++ [List.ofFn t.evaluations, [t.beta]]

/-- Wire encoding binds every prover polynomial before the challenge testing it. -/
def transcriptMessages {E : Type} {p : Nat} (t : Transcript E p) : List (List E) :=
  (List.ofFn fun i => [t.instancePoint i]) ++ [[t.segment]] ++
    (List.ofFn fun i => [t.lanePoint i]) ++ [[t.middleValue]] ++
    (List.ofFn fun d => layerMessages (t.layers d)).flatten ++
    roundMessages t.openings.outputPolys t.openings.outputPoint ++ [[t.openings.outputValue]] ++
    roundMessages t.openings.inputPolys t.openings.inputPoint ++ [List.ofFn t.openings.slices]

/-- Independence of the 64 lane powers in the field used by GKR. -/
def IndependentLanePowers {E : Type*} [CommRing E] [CharP E 2] (x : E) : Prop :=
  ∀ c : Fin 64 → ZMod 2,
    (∑ z, ZMod.castHom (dvd_refl 2) E (c z) * x^z.val) = 0 → ∀ z, c z = 0

/-- Packed linear-layer bits in the polynomial coefficient ring. -/
noncomputable def packedLinear {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600) : E[X] :=
  Embedding.kemb fun i : Fin 16 => ZMod.castHom (dvd_refl 2) E
    (linear (segmentState q (packInstance i b) m (11-d.val) (by omega)) j)

/-- The true weighted chi product polynomial, before projection and the iota correction. -/
noncomputable def honestProduct {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) : E[X] :=
  let ones : E[X] := Embedding.kemb fun _ => 1
  ∑ m : Fin 2, ∑ b : Fin (2^p), ∑ j : Fin 1600,
    (eqWeight c.point (b.val+2^p*m.val) * c.weights j) •
      (ones * packedLinear q d m b j +
        (ones + packedLinear q d m b (along j 1)) * packedLinear q d m b (along j 2))

/-- A cube weight splits into its highest coordinate and lower coordinates. -/
theorem eqWeight_last {E : Type*} [CommRing E] {p : Nat}
    (r : Fin (p+1) → E) (b : Fin (2^p)) (m : Fin 2) :
    eqWeight r (b.val+2^p*m.val) =
      eqWeight (fun i : Fin p => r i.castSucc) b.val *
        (if m.val = 0 then 1-r (Fin.last p) else r (Fin.last p)) := by
  unfold eqWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have low (i : Fin p) : (b.val+2^p*m.val).testBit i.val = b.val.testBit i.val := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add m.val b.isLt]
    simp only [i.isLt, ite_true]
  simp_rw [low]
  congr 1
  simp only [Nat.add_comm b.val, Nat.testBit_two_pow_mul_add m.val b.isLt]
  fin_cases m <;> simp

/-- Split a cube index into its highest bit and lower coordinates. -/
theorem cube_sum {E : Type*} [AddCommMonoid E] {p : Nat}
    (f : Fin (2^(p+1)) → E) :
    ∑ b, f b = ∑ m : Fin 2, ∑ b : Fin (2^p),
      f ⟨b.val+2^p*m.val, by
        rw [pow_succ]
        have hm : m.val = 0 ∨ m.val = 1 := by omega
        rcases hm with hm | hm <;> simp only [hm, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega⟩ := by
  let e : Fin 2 × Fin (2^p) ≃ Fin (2^(p+1)) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_succ]; omega))
  calc
    _ = ∑ b : Fin 2 × Fin (2^p), f (e b) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- All Boolean-cube weights sum to one. -/
theorem eqWeight_sum {E : Type*} [CommRing E] {p : Nat}
    (r : Fin p → E) : ∑ b : Fin (2^p), eqWeight r b.val = 1 := by
  induction p with
  | zero => simp [eqWeight]
  | succ p ih =>
    rw [cube_sum]
    simp_rw [eqWeight_last]
    simp only [← Finset.sum_mul, ih, one_mul]
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false]
    ring

/-- Summing over packs leaves the segment weight. -/
theorem sum_pack_weight {E : Type*} [CommRing E] {p : Nat}
    (r : Fin (p+1) → E) (m : Fin 2) :
    ∑ b : Fin (2^p), eqWeight r (b.val+2^p*m.val) =
      if m.val = 0 then 1-r (Fin.last p) else r (Fin.last p) := by
  simp only [eqWeight_last, ← Finset.sum_mul, eqWeight_sum, one_mul]

/-- Only the first lane contributes to the iota constant. -/
theorem sum_iota {E : Type*} [CommRing E] (w : Fin 1600 → E) (word : Nat) :
    (∑ j : Fin 1600, w j *
      (if j.val < 64 ∧ word.testBit j.val then 1 else 0)) =
      ∑ z : Fin 64, if word.testBit z.val then w ⟨z.val, by omega⟩ else 0 := by
  rw [Fin.sum_univ_add (a := 64) (b := 1536)]
  have upper (j : Fin 1536) : ¬ (64+j.val < 64 ∧ word.testBit (64+j.val)) := by omega
  simp only [Fin.val_castAdd, Fin.val_natAdd, upper, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro z _
  have hz : z.val < 64 := z.isLt
  simp only [hz, true_and, mul_ite, mul_one, mul_zero]
  rfl

/-- Projection of the honest product gives the coordinatewise chi expression. -/
theorem project_honest {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (i : Fin 16) :
    Embedding.kproj (honestProduct q d c) i =
      ∑ m : Fin 2, ∑ b : Fin (2^p), ∑ j : Fin 1600,
        (eqWeight c.point (b.val+2^p*m.val) * c.weights j) *
          ZMod.castHom (dvd_refl 2) E
            (let a := linear (segmentState q (packInstance i b) m (11-d.val) (by omega))
            a j + (1+a (along j 1))*a (along j 2)) := by
  simp only [honestProduct, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  dsimp only [packedLinear]
  rw [← Embedding.kemb_add, map_add, Embedding.kproj_kemb_mul, Embedding.kproj_kemb_mul]
  simp only [Pi.add_apply, one_mul, map_add, map_mul, map_one]

/-- A backwards layer removes exactly one round from each segment. -/
theorem segment_step {p : Nat} (q : Witness p) (b : Fin (2^(p+4)))
    (m : Fin 2) (d : Fin 12) :
    segmentState q b m (12-d.val) (by omega) =
      round ⟨12*(m.val+1)-d.val-1, by omega⟩
        (segmentState q b m (11-d.val) (by omega)) := by
  have transport (e f : Nat) (he : e ≤ 12) (hf : f ≤ 12) (h : e = f) :
      segmentState q b m e he = segmentState q b m f hf := by
    subst f
    rfl
  calc
    _ = segmentState q b m ((11-d.val)+1) (by omega) :=
      transport _ _ _ _ (by omega)
    _ = _ := by
      change round ⟨12*m.val+(11-d.val), by omega⟩ _ = _
      congr 1
      apply Fin.ext
      change 12*m.val+(11-d.val) = 12*(m.val+1)-d.val-1
      omega

/-- The weighted projection is the weighted chi claim. -/
theorem projected_chi {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) :
    (∑ i, c.mu i * Embedding.kproj (honestProduct q d c) i) =
      ∑ m : Fin 2, ∑ b : Fin (2^p), ∑ i : Fin 16, ∑ j : Fin 1600,
        eqWeight c.point (b.val+2^p*m.val) * c.mu i * c.weights j *
          ZMod.castHom (dvd_refl 2) E
            (let a := linear (segmentState q (packInstance i b) m (11-d.val) (by omega))
            a j + (1+a (along j 1))*a (along j 2)) := by
  simp_rw [project_honest]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The iota contribution is independent of the pack and instance coordinates. -/
theorem constant_sum {E : Type*} [CommRing E] {p : Nat}
    (d : Fin 12) (c : Claim E p) :
    (∑ m : Fin 2, ∑ b : Fin (2^p), ∑ i : Fin 16, ∑ j : Fin 1600,
      eqWeight c.point (b.val+2^p*m.val) * c.mu i * c.weights j *
        (if j.val < 64 ∧ (roundConstants ⟨12*(m.val+1)-d.val-1, by omega⟩).testBit j.val
          then 1 else 0)) = constantContribution d c := by
  have inner (m : Fin 2) (b : Fin (2^p)) :
      (∑ i : Fin 16, ∑ j : Fin 1600,
        eqWeight c.point (b.val+2^p*m.val) * c.mu i * c.weights j *
          (if j.val < 64 ∧ (roundConstants ⟨12*(m.val+1)-d.val-1, by omega⟩).testBit j.val
            then 1 else 0)) =
        eqWeight c.point (b.val+2^p*m.val) * (∑ i, c.mu i) *
          ∑ z : Fin 64, if (roundConstants ⟨12*(m.val+1)-d.val-1, by omega⟩).testBit z
            then c.weights ⟨z.val,by omega⟩ else 0 := by
    rw [← sum_iota c.weights
      (roundConstants ⟨12*(m.val+1)-d.val-1, by omega⟩)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [inner]
  simp only [← Finset.sum_mul, sum_pack_weight]
  unfold constantContribution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The RMFE projection and public iota correction equal the semantic layer claim. -/
theorem layer_projection_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) :
    ClaimHolds q d.castSucc c ↔
      (∑ i, c.mu i * Embedding.kproj (honestProduct q d c) i) +
        constantContribution d c = c.value := by
  rw [projected_chi, ← constant_sum]
  unfold ClaimHolds
  simp only [Fin.val_castSucc]
  simp_rw [segment_step q (d := d), round]
  have castif (P : Prop) [Decidable P] :
      ZMod.castHom (dvd_refl 2) E (if P then 1 else 0) = if P then 1 else 0 := by
    split <;> simp only [map_one, map_zero]
  simp only [map_add, map_mul, map_one, castif, mul_add, Finset.sum_add_distrib]
  exact eq_comm


/-- Total numerator of all fresh challenges; `kbatch = p+4`. -/
def totalNumerator (p : Nat) : Nat :=
  ((steps p).map fun s => match s with
    | .message _ => 0
    | .challenge kind => kind.numerator).sum

/-- Sum of numerator weights in a list of wire moves. -/
def numeratorSum (s : List WireStep) : Nat :=
  (s.map fun s => match s with | .message _ => 0 | .challenge k => k.numerator).sum

/-- Numerator weights add under concatenation. -/
theorem numeratorSum_append (a b : List WireStep) :
    numeratorSum (a ++ b) = numeratorSum a + numeratorSum b := by
  simp only [numeratorSum, List.map_append, List.sum_append]

/-- Numerator weights sum over concatenated blocks. -/
theorem numeratorSum_flatMap {α : Type*} (l : List α) (f : α → List WireStep) :
    numeratorSum (l.flatMap f) = (l.map (fun a => numeratorSum (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, numeratorSum_append, ih, List.map_cons, List.sum_cons]

/-- A uniform round block contributes its count times its local numerator. -/
theorem numeratorSum_rounds (count degree loss : Nat) (kind : Nat → Challenge)
    (h : ∀ i, (kind i).numerator = loss) :
    numeratorSum (roundSteps count degree kind) = count * loss := by
  rw [roundSteps, numeratorSum_flatMap]
  simp [numeratorSum, h]

/-- A layer contributes one product test, cubic rounds, and beta batching. -/
theorem numeratorSum_layer (p d : Nat) : numeratorSum (layerSteps p d) = 3*p+84 := by
  simp only [layerSteps, numeratorSum_append]
  rw [numeratorSum_rounds (loss := 3) _ _ _ (by intro; rfl),
      numeratorSum_rounds (loss := 3) _ _ _ (by intro; rfl)]
  simp [numeratorSum, Challenge.numerator]
  omega

/-- Annex C's three contributions are the start, twelve layers, and the two openings. -/
theorem totalNumerator_eq (p : Nat) :
    totalNumerator p = (p+4+6) + 12*(3*(p+4)+72) + (12+20) ∧
      totalNumerator p = 37*(p+4)+902 := by
  have h : totalNumerator p = 37*(p+4)+902 := by
    change numeratorSum (steps p) = _
    simp only [steps, numeratorSum_append]
    rw [numeratorSum_rounds (loss := 2) _ _ _ (by intro; rfl),
        numeratorSum_rounds (loss := 2) _ _ _ (by intro; rfl),
        numeratorSum_rounds (loss := 2) _ _ _ (by intro; rfl)]
    have layers : numeratorSum ((List.range 12).flatMap (layerSteps p)) = 12*(3*p+84) := by
      rw [numeratorSum_flatMap]
      simp only [numeratorSum_layer]
      simp
      omega
    rw [layers]
    simp [numeratorSum, Challenge.numerator, Function.comp_def]
    omega
  constructor
  · rw [h]; omega
  · exact h

/-- The sum of the certificate's per-challenge errors is the annex C public-coin bound.
This excludes Fiat-Shamir and the PCS, which must discharge `TerminalRelation`. -/
theorem totalError_eq {E : Type} [Fintype E] (p : Nat) :
    ((totalNumerator p : ENNReal) / Fintype.card E) =
      (37*(p+4)+902 : ENNReal) / Fintype.card E := by
  rw [(totalNumerator_eq p).2]
  norm_cast

/-- A deterministic public prover chooses each coefficient vector from the strict prefix.
Randomized provers are obtained by fixing their coins before this strategy is supplied. -/
abbrev Prover (E : Type) := List (List E) → (arity : Nat) → Fin arity → E

/-- Execute the public schedule using fresh independent uniform verifier challenges. -/
noncomputable def runWire (E : Type) [Fintype E] [Nonempty E] (prover : Prover E) :
    List WireStep → List (List E) → ProbComp (List (List E))
  | [], _ => pure []
  | .message n :: rest, history => do
      let message := List.ofFn (prover history n)
      let suffix ← runWire E prover rest (history ++ [message])
      pure (message :: suffix)
  | .challenge _ :: rest, history => do
      let r ← uniformField E
      let suffix ← runWire E prover rest (history ++ [[r]])
      pure ([r] :: suffix)

end CompStark.Keccak.Gkr
