/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.ToArkLib.GrandProduct and GrandProductSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Algebra.SumcheckBound
public import CompStark.Multilinear.Retained

/-! Three batched product trees over leaves of any shape, with constraint-residual riders over any witness. Normalized sumcheck messages contain the cofactor of the known equality factor, of degree four in radix four. The final layer progressively restricts the constraint riders on its own challenges; intermediate layers retain their full zeroness. -/

@[expose] public section

namespace CompStark.Multilinear.GrandProduct

open CompStark.BinaryFields
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec Polynomial


/-- The constraint-residual tables a grand-product GKR carries as riders over a witness `W`: a
predicate on well-shaped witnesses, `count` tables with fixed heights below `maxHeight`, and each
table's values on the Boolean rows. The final layer restricts every rider at its own challenges;
the riders vanish on Boolean rows when the witness's constraints hold. -/
structure Riders (W : Type) where
  /-- Witnesses of the committed shape. -/
  Fits : W → Prop
  /-- The number of rider tables. -/
  count : ℕ
  /-- Each table's number of variables. -/
  height : Fin count → ℕ
  /-- A bound on every table's number of variables. -/
  maxHeight : ℕ
  /-- Every table has at most `maxHeight` variables. -/
  height_le : ∀ i, height i ≤ maxHeight
  /-- Each table's values on the Boolean rows, low bit first. -/
  table : W → Fin count → ℕ → E

/-- A point shared by the three sides, with one value per side. -/
structure Claim where
  /-- Low-variable-first coordinates. -/
  point : List E
  /-- Push, pull, and count claims. -/
  values : Fin 3 → E

/-- Odd root-most binary contraction followed by radix-four contractions. -/
def layers (μ : ℕ) : List ℕ :=
  (if μ % 2 = 1 then [1] else []) ++ List.replicate (μ / 2) 2

/-- Products below each node of the layer with `m` variables. -/
def level (μ m : ℕ) (leaves : Fin 3 → ℕ → E) (side : Fin 3) (i : ℕ) : E :=
  ∏ j : Fin (2 ^ (μ - m)), leaves side (i * 2 ^ (μ - m) + j.val)

/-- Truth of a three-sided layer claim. -/
def Claim.Holds (μ m : ℕ) (leaves : Fin 3 → ℕ → E) (c : Claim) : Prop :=
  c.point.length = m ∧ ∀ side, c.values side = mle m (level μ m leaves side) c.point

/-- Batching by three successive powers at each layer. -/
def batch (lam : E) (v : Fin 3 → E) : E := ∑ s : Fin 3, lam ^ s.val * v s

/-- Child values at a point in the parent variables. -/
def childValue (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (side : Fin 3)
    (child : ℕ) (z : List E) : E :=
  mle m (fun i ↦ level μ (m + ρ) leaves side (child + 2 ^ ρ * i)) z

/-- Degree-`2^ρ` cofactor of the known equality weight in one batched layer. -/
def cofactor (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E) (z : List E) : E :=
  ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), childValue μ m ρ leaves s a.val z

/-- A normalized partial sum; already sampled equality factors are divided out algebraically. -/
def weightedPartial (m : ℕ) (f : List E → E) (point χ : List E) : E :=
  ∑ i : Fin (2 ^ (m - χ.length)),
    f (χ ++ List.ofFn (fun k : Fin (m - χ.length) ↦ bit i.val k.val)) *
      ∏ k : Fin (m - χ.length), eqFactor (point.getD (χ.length + k.val) 0) (bit i.val k.val)

/-- Full coefficients of a degree-bounded polynomial, constant term first. -/
abbrev Coefficients (d : ℕ) := Fin (d + 1) → E

/-- Transmitted cofactor coefficients of degrees one through `d`. -/
abbrev Message (d : ℕ) := Fin d → E

/-- Evaluate a degree-bounded coefficient message. -/
def evaluateCoefficients (d : ℕ) (q : Coefficients d) (x : E) : E :=
  ∑ i : Fin (d + 1), q i * x ^ i.val

/-- The univariate polynomial represented by a full coefficient vector. -/
noncomputable def messagePolynomial (d : ℕ) (q : Coefficients d) : Polynomial E :=
  ∑ i : Fin (d + 1), Polynomial.C (q i) * Polynomial.X ^ i.val

/-- Message evaluation is evaluation of its represented polynomial. -/
theorem messagePolynomial_eval (d : ℕ) (q : Coefficients d) (x : E) :
    (messagePolynomial d q).eval x = evaluateCoefficients d q x := by
  simp only [messagePolynomial, evaluateCoefficients, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The explicit coefficient range bounds the represented polynomial's degree. -/
theorem messagePolynomial_degree (d : ℕ) (q : Coefficients d) :
    (messagePolynomial d q).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- Reading a represented polynomial recovers each coefficient. -/
theorem messagePolynomial_coeff (d : ℕ) (q : Coefficients d) (j : Fin (d + 1)) :
    (messagePolynomial d q).coeff j.val = q j := by
  simp only [messagePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
  · intro i _ hij
    apply ite_eq_right_iff.mpr
    intro h
    exact (hij (Fin.ext h.symm)).elim
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Distinct full coefficient vectors represent distinct formal polynomials. -/
theorem messagePolynomial_injective (d : ℕ) : Function.Injective (messagePolynomial d) := by
  intro p q h
  funext j
  have hc := congrArg (fun f : Polynomial E ↦ f.coeff j.val) h
  simpa only [messagePolynomial_coeff] using hc

/-- Reconstruct the constant coefficient from the equality coordinate and running claim. -/
def decode (d : ℕ) (r current : E) (q : Message d) : Coefficients d :=
  Fin.cons (current - r * ∑ j, q j) q

/-- Evaluate the cofactor reconstructed at the verifier's current state. -/
def evaluate (d : ℕ) (r current : E) (q : Message d) (x : E) : E :=
  evaluateCoefficients d (decode d r current q) x

/-- The full cofactor polynomial decoded from a transmitted tail. -/
noncomputable def cofactorModel (d : ℕ) (r current : E) (q : Message d) : E⦃≤ d⦄[X] :=
  ⟨messagePolynomial d (decode d r current q),
    Polynomial.mem_degreeLE.mpr
      (Polynomial.natDegree_le_iff_degree_le.mp (messagePolynomial_degree _ _))⟩

/-- Claim-aware runtime operations for a fixed equality coordinate. -/
def cofactorOps (d : ℕ) (r : E) : Sumcheck.MessageOps E (Message d) where
  evaluate := evaluate d r
  accept _ _ := true

/-- The cofactor operations evaluate exactly their degree-bounded polynomial model. -/
theorem cofactorModel_evaluate_eq (d : ℕ) (r current : E) (q : Message d) (x : E) :
    (cofactorOps d r).evaluate current q x = (cofactorModel d r current q).val.eval x :=
  (messagePolynomial_eval d (decode d r current q) x).symm

/-- Reading the decoded constant recovers the verifier's reconstruction formula. -/
theorem decode_zero (d : ℕ) (r current : E) (q : Message d) :
    decode d r current q 0 = current - r * ∑ j, q j := rfl

/-- Every transmitted positive-degree coefficient survives reconstruction. -/
theorem decode_succ (d : ℕ) (r current : E) (q : Message d) (j : Fin d) :
    decode d r current q j.succ = q j := rfl

/-- Production's characteristic-two constant is the claim plus the weighted tail sum. -/
theorem decode_zero_eq_add (d : ℕ) (r current : E) (q : Message d) :
    decode d r current q 0 = current + r * ∑ j, q j := by
  rw [decode_zero, CharTwo.sub_eq_add]

/-- Decoding preserves the cofactor degree used by the weighted local bound. -/
theorem cofactorModel_degree (d : ℕ) (r current : E) (q : Message d) :
    (cofactorModel d r current q).val.natDegree ≤ d :=
  messagePolynomial_degree _ _

/-- Full coefficient evaluation at zero is the constant coefficient. -/
theorem evaluateCoefficients_zero (d : ℕ) (q : Coefficients d) :
    evaluateCoefficients d q 0 = q 0 := by
  rw [evaluateCoefficients, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- Full coefficient evaluation at one is the sum of all coefficients. -/
theorem evaluateCoefficients_one (d : ℕ) (q : Coefficients d) :
    evaluateCoefficients d q 1 = q 0 + ∑ j : Fin d, q j.succ := by
  simp only [evaluateCoefficients, one_pow, mul_one, Fin.sum_univ_succ]

/-- Encode a bounded cofactor by omitting its constant coefficient. -/
def encode (d : ℕ) (p : E⦃≤ d⦄[X]) : Message d :=
  fun j ↦ p.val.coeff j.succ.val

/-- A bounded polynomial is determined by its complete coefficient vector. -/
theorem messagePolynomial_coefficients (d : ℕ) (p : E⦃≤ d⦄[X]) :
    messagePolynomial d (fun j ↦ p.val.coeff j.val) = p.val := by
  have hd : p.val.natDegree ≤ d :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp p.property)
  have h := p.val.as_sum_range_C_mul_X_pow' (n := d + 1) (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h.symm

/-- The weighted claim determines precisely the omitted constant coefficient. -/
theorem decode_encode (d : ℕ) (r current : E) (p : E⦃≤ d⦄[X])
    (hsum : (1 - r) * p.val.eval 0 + r * p.val.eval 1 = current) :
    decode d r current (encode d p) = fun j ↦ p.val.coeff j.val := by
  have he (x : E) : evaluateCoefficients d (fun j ↦ p.val.coeff j.val) x = p.val.eval x := by
    rw [← messagePolynomial_eval, messagePolynomial_coefficients]
  rw [← he 0, ← he 1, evaluateCoefficients_zero, evaluateCoefficients_one] at hsum
  simp only [Fin.val_zero] at hsum
  have hc : current = p.val.coeff 0 + r * ∑ j : Fin d, p.val.coeff j.succ.val := by
    rw [← hsum]
    ring
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · rw [decode_zero, hc]
    simp only [encode, Fin.val_zero]
    ring
  · exact decode_succ d r current (encode d p) k

/-- Encoding and decoding an honest weighted cofactor recovers its formal polynomial. -/
theorem cofactorModel_encode (d : ℕ) (r current : E) (p : E⦃≤ d⦄[X])
    (hsum : (1 - r) * p.val.eval 0 + r * p.val.eval 1 = current) :
    cofactorModel d r current (encode d p) = p := by
  apply Subtype.ext
  change messagePolynomial d (decode d r current (encode d p)) = p.val
  rw [decode_encode d r current p hsum, messagePolynomial_coefficients]

/-- Encoding a decoded cofactor returns exactly the transmitted tail. -/
theorem encode_cofactorModel (d : ℕ) (r current : E) (q : Message d) :
    encode d (cofactorModel d r current q) = q := by
  funext j
  exact (messagePolynomial_coeff d (decode d r current q) j.succ).trans
    (decode_succ d r current q j)

/-- Reconstructed cofactors satisfy the weighted check at every verifier state. -/
theorem cofactor_weighted_sum (d : ℕ) (r current : E) (q : Message d) :
    (1 - r) * evaluate d r current q 0 + r * evaluate d r current q 1 = current := by
  simp only [evaluate, evaluateCoefficients_zero, evaluateCoefficients_one,
    decode_zero, decode_succ]
  ring

/-- Cofactor acceptance is the weighted equality check, rather than the Boolean sum. -/
theorem cofactorModel_accept_iff (d : ℕ) (r current : E) (q : Message d) :
    (cofactorOps d r).accept current q = true ↔
      (1 - r) * (cofactorModel d r current q).val.eval 0 +
        r * (cofactorModel d r current q).val.eval 1 = current := by
  rw [← cofactorModel_evaluate_eq, ← cofactorModel_evaluate_eq]
  exact iff_of_true rfl (cofactor_weighted_sum d r current q)

/-- Known-equality-factor check for the reconstructed degree-bounded cofactor. -/
def check (d : ℕ) (r current : E) (q : Message d) : Bool :=
  (cofactorOps d r).accept current q

/-- Every transmitted cofactor tail reconstructs to a passing weighted check. -/
theorem check_eq_true (d : ℕ) (r current : E) (q : Message d) :
    check d r current q = true := rfl

/-- Evaluation access supplies both the equality coordinate and running claim. -/
@[reducible] def messageInterface (d : ℕ) : OracleInterface (Message d) where
  Query := E × E × E
  toOC.spec := (E × E × E) →ₒ E
  toOC.impl query := do return (cofactorOps d query.1).evaluate query.2.1 (← read) query.2.2

/-- Normalized sumcheck with public rejection; no rejected branch exports leaf claims. -/
def roundsProtocol (d : ℕ) (tail : Protocol) : ℕ → Protocol
  | 0 => tail
  | n + 1 => .oracleWith (Message d) (messageInterface d)
      (.public .receiver (Option E) fun
        | none => .done
        | some _ => roundsProtocol d tail n)

/-- One fresh scalar for each child coordinate. -/
def interpolationProtocol (tail : Protocol) : ℕ → Protocol
  | 0 => tail
  | n + 1 => .public .receiver E fun _ ↦ interpolationProtocol tail n

/-- A layer combiner, a normalized sumcheck, the descendants, and their multilinear combination. -/
def layerProtocol (ρ m : ℕ) (tail : Protocol) : Protocol :=
  .public .receiver E fun _ ↦ roundsProtocol (2 ^ ρ)
    (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ) m

/-- The complete product-tree descent, with a specified terminal protocol. -/
def protocol (tail : Protocol) : List ℕ → ℕ → Protocol
  | [], _ => tail
  | ρ :: rest, m => layerProtocol ρ m (protocol tail rest (m + ρ))

/-- Every rider table vanishes on its Boolean rows. -/
def RidersZero {W : Type} (R : Riders W) (q : W) : Prop :=
  ∀ i, ∀ j : Fin (2 ^ R.height i), R.table q i j.val = 0

/-- The multilinear extension of one rider table. -/
def rider {W : Type} (R : Riders W) (q : W) (i : Fin R.count) (z : List E) : E :=
  mle (R.height i) (R.table q i) z

/-- A rider restricted at exactly the coordinates already sampled in the final layer. -/
def RidersRestricted {W : Type} (R : Riders W) (q : W)
    (σ : ℕ → Option E) : Prop :=
  ∀ i, ∀ z : List E, z.length = R.height i →
    (∀ k, ∀ a, σ k = some a → k < R.height i → z[k]?.getD 0 = a) → rider R q i z = 0

/-- Partial point of the final layer: child coordinates first, followed by sumcheck coordinates. -/
def partialPoint (ρ : ℕ) (χ u : List E) (k : ℕ) : Option E :=
  if k < u.length then u[k]? else if ρ ≤ k then χ[k - ρ]? else none

/-- Intermediate layers preserve full riders; the last layer restricts them on the actual sampled coordinates. -/
def riderState {W : Type} (R : Riders W) (last : Bool) (ρ : ℕ)
    (χ u : List E) (q : W) : Prop :=
  if last then RidersRestricted R q (partialPoint ρ χ u) else RidersZero R q

/-- Unrestricted residual riders vanish exactly when their entire Boolean residual tables vanish. -/
theorem ridersRestricted_none_iff {W : Type} (R : Riders W) (q : W) :
    RidersRestricted R q (fun _ ↦ none) ↔ RidersZero R q := by
  constructor
  · intro h i j
    have hz := h i (List.ofFn fun k : Fin (R.height i) ↦ bit j.val k.val)
      (List.length_ofFn) (by intro k a hn; cases hn)
    simpa only [rider, mle_bits] using hz
  · intro h i z _ _
    unfold rider mle
    apply Finset.sum_eq_zero
    intro j _
    exact mul_eq_zero_of_left (h i j) _

/-- A layer's rider condition at the empty prefix retains the complete residual tables. -/
theorem riderState_empty_iff {W : Type} (R : Riders W) (last : Bool) (ρ : ℕ) (q : W) :
    riderState R last ρ [] [] q ↔ RidersZero R q := by
  have hp : partialPoint ρ [] [] = fun _ ↦ (none : Option E) := by
    funext k
    simp only [partialPoint, List.length_nil, Nat.not_lt_zero, ↓reduceIte, List.getElem?_nil, ite_self]
  cases last with
  | false => rfl
  | true => simpa only [riderState, ↓reduceIte, hp] using ridersRestricted_none_iff R q

/-- Knowledge before each normalized sumcheck round. -/
def roundRelation {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point : List E)
    (lam current : E) (χ : List E) (active : Bool) (q : W) : Prop :=
  active = true ∧ R.Fits q ∧ point.length = m ∧ riderState R last ρ χ [] q ∧
    current = weightedPartial m (cofactor μ m ρ (leaves q) lam) point χ

/-- Interpolating the supplied descendant tables at a partial child point. -/
def interpolated (ρ : ℕ) (children : Fin 3 → Fin (2 ^ ρ) → E)
    (u : List E) (side : Fin 3) (rest : ℕ) : E :=
  mle u.length (fun a ↦ children side
    ⟨(a + 2 ^ u.length * rest) % 2 ^ ρ, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) u

/-- All remaining Boolean child assignments agree, while riders follow the same partial point. -/
def interpolationRelation {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (q : W) : Prop :=
  active = true ∧ R.Fits q ∧ riderState R last ρ χ u q ∧
    ∀ s, ∀ a : Fin (2 ^ (ρ - u.length)),
      interpolated ρ children u s a.val =
        mle u.length (fun b ↦ childValue μ m ρ (leaves q) s (b + 2 ^ u.length * a.val) χ) u

/-- Identity-witness annotations on interpolation challenges. -/
def interpolationLabels {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (tail : Protocol)
    (out : Claim → Bool → Retained.Labels (W) tail.tree) :
    (n : ℕ) → List E → Retained.Labels (W) (interpolationProtocol tail n).tree
  | 0, u => out ⟨u ++ χ, fun s ↦ interpolated ρ children u s 0⟩ active
  | n + 1, u => ⟨interpolationRelation R μ m ρ leaves last χ u children active,
      fun r ↦ interpolationLabels R μ m ρ leaves last χ children active tail out n (u ++ [r])⟩

/-- Labels after the sumcheck: supplied descendants must reproduce its last cofactor claim. -/
def childrenLabels {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (tail : Protocol)
    (out : Claim → Bool → Retained.Labels (W) tail.tree) :
    Retained.Labels (W)
      (Protocol.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ).tree :=
  ⟨roundRelation R μ m ρ leaves last point lam current χ active, fun children ↦
    interpolationLabels R μ m ρ leaves last χ children
      (active && decide (current = ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), children s a))
      tail out ρ []⟩

/-- Every normalized round keeps the same stack, including rejected branches. -/
def roundsLabels {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point : List E)
    (lam : E) (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree) :
    (n : ℕ) → List E → E → Bool →
    Retained.Labels (W)
      (roundsProtocol (2 ^ ρ)
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ) n).tree
  | 0, χ, current, active => childrenLabels R μ m ρ leaves last point χ lam current active tail out
  | n + 1, χ, current, active =>
    ⟨roundRelation R μ m ρ leaves last point lam current χ active, fun message ↦
      ⟨roundRelation R μ m ρ leaves last point lam current χ active, fun
        | none => fun _ ↦ False
        | some r => roundsLabels R μ m ρ leaves last point lam tail out n (χ ++ [r])
            (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r)
            (active && check (2 ^ ρ) (point.getD χ.length 0) current message)⟩⟩

/-- The scalar claim remains the input predicate when the normalized rounds reach their child-value message. -/
theorem roundsLabels_input {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point : List E)
    (lam : E) (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (n : ℕ) (χ : List E) (current : E) (active : Bool) :
    Retained.input (roundsLabels R μ m ρ leaves last point lam tail out n χ current active) =
      roundRelation R μ m ρ leaves last point lam current χ active := by
  cases n <;> rfl

/-- Layer-boundary predicate before the batching scalar. -/
def layerRelation {W : Type} (R : Riders W) (μ m : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (c : Claim) (active : Bool) (q : W) : Prop :=
  active = true ∧ R.Fits q ∧ RidersZero R q ∧ c.Holds μ m (leaves q)

/-- All GKR prefix predicates, with the final layer using progressive rider restrictions. -/
def labels {W : Type} (R : Riders W) (μ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (tail : Protocol)
    (out : Claim → Bool → Retained.Labels (W) tail.tree) :
    (steps : List ℕ) → (m : ℕ) → Claim → Bool →
    Retained.Labels (W) (protocol tail steps m).tree
  | [], _, c, active => out c active
  | ρ :: rest, m, c, active =>
    ⟨layerRelation R μ m leaves c active, fun lam ↦
      roundsLabels R μ m ρ leaves rest.isEmpty c.point lam (protocol tail rest (m + ρ))
        (fun next nextActive ↦ labels R μ leaves tail out rest (m + ρ) next nextActive) m [] (batch lam c.values) active⟩

/-- Uniform fresh challenge, or explicit public rejection if the round check fails. -/
noncomputable def roundSample (d : ℕ) (r current : E) (message : Message d) : ProbComp (Option E) :=
  if check d r current message then some <$> ($ᵗ E) else pure none

/-- Uniform interpolation samplers, carrying the actual next layer point into its schedule. -/
noncomputable def interpolationSchedule (ρ : ℕ) (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E)
    (tail : Protocol) (next : Claim → RoundExtractor.ChallengeSchedule tail.tree tail.roles) :
    (n : ℕ) → List E → RoundExtractor.ChallengeSchedule (interpolationProtocol tail n).tree
      (interpolationProtocol tail n).roles
  | 0, u => next ⟨u ++ χ, fun s ↦ interpolated ρ children u s 0⟩
  | n + 1, u => ⟨⟨$ᵗ E, overE 1⟩, fun r ↦ interpolationSchedule ρ χ children tail next n (u ++ [r])⟩

/-- Normalized round samplers and errors at every authored message prefix. -/
noncomputable def roundsSchedule (d : ℕ) (point : List E) (tail : Protocol)
    (next : List E → E → RoundExtractor.ChallengeSchedule tail.tree tail.roles) :
    (n : ℕ) → List E → E → RoundExtractor.ChallengeSchedule (roundsProtocol d tail n).tree
      (roundsProtocol d tail n).roles
  | 0, χ, current => next χ current
  | n + 1, χ, current => fun message ↦
    ⟨⟨roundSample d (point.getD χ.length 0) current message, overE d⟩, fun
      | none => PUnit.unit
      | some r => roundsSchedule d point tail next n (χ ++ [r]) (evaluate d (point.getD χ.length 0) current message r)⟩

/-- Complete GKR challenge schedule; batching three trees costs two roots per combiner. -/
noncomputable def challenges (tail : Protocol) (next : RoundExtractor.ChallengeSchedule tail.tree tail.roles) :
    (steps : List ℕ) → (m : ℕ) → Claim →
    RoundExtractor.ChallengeSchedule (protocol tail steps m).tree (protocol tail steps m).roles
  | [], _, _ => next
  | ρ :: rest, m, c =>
    ⟨⟨$ᵗ E, overE 2⟩, fun lam ↦ roundsSchedule (2 ^ ρ) c.point
      (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol (protocol tail rest (m + ρ)) ρ)
      (fun χ _ ↦ ⟨PUnit.unit, fun children ↦
        interpolationSchedule ρ χ children (protocol tail rest (m + ρ))
          (challenges tail next rest (m + ρ)) ρ []⟩) m [] (batch lam c.values)⟩

/-- Parse interpolation messages while keeping the exact terminal protocol path. -/
def interpolationResult (ρ : ℕ) (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E)
    (tail : Protocol) : (n : ℕ) → List E →
    (interpolationProtocol tail n).tree.ExecutionPath → Claim × tail.tree.ExecutionPath
  | 0, u, path => (⟨u ++ χ, fun s ↦ interpolated ρ children u s 0⟩, path)
  | n + 1, u, path =>
      let r : E := path.1
      interpolationResult ρ χ children tail n (u ++ [r]) path.2

/-- Parse normalized rounds; public rejection has no terminal claim. -/
def roundsResult (d : ℕ) (point : List E) (tail : Protocol) : (n : ℕ) → List E → E → Bool →
    (roundsProtocol d tail n).tree.ExecutionPath → Option (List E × E × Bool × tail.tree.ExecutionPath)
  | 0, χ, current, active, path => some (χ, current, active, path)
  | n + 1, χ, current, active, path => match path with
    | ⟨_, none, _⟩ => none
    | ⟨message, some r, rest⟩ => roundsResult d point tail n (χ ++ [r]) (evaluate d (point.getD χ.length 0) current message r)
        (active && check d (point.getD χ.length 0) current message) rest

/-- Parse the actual shared leaf point and retain all check results. -/
def result (tail : Protocol) : (steps : List ℕ) → (m : ℕ) → Claim → Bool →
    (protocol tail steps m).tree.ExecutionPath → Option (Claim × Bool × tail.tree.ExecutionPath)
  | [], _, c, active, path => some (c, active, path)
  | ρ :: rest, m, c, active, path => do
      let lam : E := path.1
      let (χ, current, good, descendants) ← roundsResult (2 ^ ρ) c.point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦
          interpolationProtocol (protocol tail rest (m + ρ)) ρ)
        m [] (batch lam c.values) active path.2
      let children : Fin 3 → Fin (2 ^ ρ) → E := descendants.1
      let (next, finalPath) := interpolationResult ρ χ children
        (protocol tail rest (m + ρ)) ρ [] descendants.2
      result tail rest (m + ρ) next
        (good && decide (current = ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), children s a)) finalPath

/-- Interpolation parsing recovers the exact authored continuation predicate. -/
theorem interpolation_endpoint {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (tail : Protocol)
    (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (n : ℕ) (u : List E) (path : (interpolationProtocol tail n).tree.ExecutionPath) :
    Retained.endpoint (interpolationLabels R μ m ρ leaves last χ children active tail out n u) path =
      let parsed := interpolationResult ρ χ children tail n u path
      Retained.endpoint (out parsed.1 active) parsed.2 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => exact ih (u ++ [(show E from path.1)]) path.2

/-- Normalized-round parsing preserves the endpoint predicate and makes aborts false. -/
theorem rounds_endpoint {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point : List E)
    (lam : E) (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (n : ℕ) (χ : List E) (current : E) (active : Bool)
    (path : (roundsProtocol (2 ^ ρ)
      (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ) n).tree.ExecutionPath) :
    Retained.endpoint (roundsLabels R μ m ρ leaves last point lam tail out n χ current active) path =
      match roundsResult (2 ^ ρ) point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ)
        n χ current active path with
      | none => fun _ ↦ False
      | some (χ', current', good, rest) =>
          Retained.endpoint (childrenLabels R μ m ρ leaves last point χ' lam current' good tail out) rest := by
  induction n generalizing χ current active with
  | zero => rfl
  | succ n ih =>
    rcases path with ⟨message, choice, path⟩
    cases choice with
    | none => rfl
    | some r => exact ih _ _ _ path

set_option backward.isDefEq.respectTransparency false in
/-- The parsed product-tree result has exactly the authored terminal predicate. -/
theorem result_endpoint {W : Type} (R : Riders W) (μ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (tail : Protocol)
    (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (steps : List ℕ) (m : ℕ) (c : Claim) (active : Bool)
    (path : (protocol tail steps m).tree.ExecutionPath) :
    Retained.endpoint (labels R μ leaves tail out steps m c active) path =
      match result tail steps m c active path with
      | none => fun _ ↦ False
      | some (c', good, rest) => Retained.endpoint (out c' good) rest := by
  induction steps generalizing m c active with
  | nil => rfl
  | cons ρ steps ih =>
    let lam : E := path.1
    let restPath := path.2
    change Retained.endpoint (roundsLabels R μ m ρ leaves steps.isEmpty c.point lam
      (protocol tail steps (m + ρ))
      (fun next good ↦ labels R μ leaves tail out steps (m + ρ) next good)
      m [] (batch lam c.values) active) restPath = _
    rw [rounds_endpoint]
    unfold result
    change _ = match (roundsResult (2 ^ ρ) c.point
      (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦
        interpolationProtocol (protocol tail steps (m + ρ)) ρ)
      m [] (batch lam c.values) active restPath).bind _ with
      | none => fun _ ↦ False
      | some (c', good, rest) => Retained.endpoint (out c' good) rest
    cases hr : roundsResult (2 ^ ρ) c.point
      (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦
        interpolationProtocol (protocol tail steps (m + ρ)) ρ)
      m [] (batch lam c.values) active restPath with
    | none => simp only [Option.bind_none]
    | some parsed =>
      rcases parsed with ⟨χ, current, good, descendants⟩
      simp only [Option.bind_some]
      change Retained.endpoint (interpolationLabels _ _ _ _ _ _ _ _ _ _ _ _ _) descendants.2 = _
      rw [interpolation_endpoint, ih]
      rfl

/-- Sum of the local GKR error numerators, including the root-most binary layer when present. -/
def errorNumerator : List ℕ → ℕ → ℕ
  | [], _ => 0
  | ρ :: rest, m => 2 + m * 2 ^ ρ + ρ + errorNumerator rest (m + ρ)

/-- Interpolation consumes one unit of error per new child coordinate. -/
theorem interpolation_budget (ρ : ℕ) (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E)
    (tail : Protocol) (next : Claim → RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (δ : ENNReal) (hnext : ∀ c, Retained.Budget tail.roles (next c) δ)
    (n : ℕ) (u : List E) :
    Retained.Budget (interpolationProtocol tail n).roles
      (interpolationSchedule ρ χ children tail next n u) (overE n + δ) := by
  induction n generalizing u with
  | zero => simpa only [interpolationProtocol, interpolationSchedule, overE_zero, zero_add] using hnext _
  | succ n ih =>
    refine ⟨overE n + δ, le_of_eq ?_, fun r ↦ ih (u ++ [r])⟩
    rw [overE_add]
    ac_rfl

/-- Normalized sumcheck consumes its cofactor degree at each round, including aborts. -/
theorem rounds_budget (d : ℕ) (point : List E) (tail : Protocol)
    (next : List E → E → RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (δ : ENNReal) (hnext : ∀ χ current, Retained.Budget tail.roles (next χ current) δ)
    (n : ℕ) (χ : List E) (current : E) :
    Retained.Budget (roundsProtocol d tail n).roles
      (roundsSchedule d point tail next n χ current) (overE (n * d) + δ) := by
  induction n generalizing χ current with
  | zero => simpa only [roundsProtocol, roundsSchedule, Nat.zero_mul, overE_zero, zero_add] using hnext χ current
  | succ n ih =>
    intro message
    refine ⟨overE (n * d) + δ, le_of_eq ?_, ?_⟩
    · simp only [roundsSchedule, Nat.succ_mul, overE_add]
      ac_rfl
    · intro choice
      cases choice with
      | none => trivial
      | some r => exact ih _ _

/-- The GKR schedule's total budget is the sum of its named per-challenge errors. -/
theorem challenges_budget (tail : Protocol)
    (next : RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (δ : ENNReal) (hnext : Retained.Budget tail.roles next δ)
    (steps : List ℕ) (m : ℕ) (c : Claim) :
    Retained.Budget (protocol tail steps m).roles (challenges tail next steps m c)
      (overE (errorNumerator steps m) + δ) := by
  induction steps generalizing m c with
  | nil => simpa only [protocol, challenges, errorNumerator, overE_zero, zero_add] using hnext
  | cons ρ rest ih =>
    refine ⟨overE (m * 2 ^ ρ) + (overE ρ + (overE (errorNumerator rest (m + ρ)) + δ)),
      le_of_eq ?_, ?_⟩
    · simp only [challenges, errorNumerator, overE_add]
      ac_rfl
    · intro lam
      apply rounds_budget
      intro χ current children
      exact interpolation_budget ρ χ children _ _ _ (fun nextClaim ↦ ih (m + ρ) nextClaim) ρ []

/-- A node is the product of its radix-sized descendant block. -/
theorem level_grouping (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (s : Fin 3) (i : ℕ)
    (hdepth : m + ρ ≤ μ) :
    level μ m leaves s i = ∏ a : Fin (2 ^ ρ), level μ (m + ρ) leaves s (a.val + 2 ^ ρ * i) := by
  have hsub : μ - m = ρ + (μ - (m + ρ)) := by omega
  have hpow : 2 ^ ρ * 2 ^ (μ - (m + ρ)) = 2 ^ (μ - m) := by rw [hsub, pow_add]
  let e : Fin (2 ^ ρ) × Fin (2 ^ (μ - (m + ρ))) ≃ Fin (2 ^ (μ - m)) :=
    finProdFinEquiv.trans (finCongr hpow)
  unfold level
  conv_lhs => rw [← e.prod_comp, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro b _
  apply congrArg (leaves s)
  simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
  rw [hsub, pow_add]
  ring
/-- On each Boolean point, the cofactor evaluates to the batch of parent-node values. -/
theorem cofactor_bits (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (i : Fin (2 ^ m)) (hdepth : m + ρ ≤ μ) :
    cofactor μ m ρ leaves lam (List.ofFn fun k : Fin m ↦ bit i.val k.val) =
      batch lam (fun s ↦ level μ m leaves s i.val) := by
  simp only [cofactor, childValue, mle_bits, batch]
  apply Finset.sum_congr rfl
  intro s _
  rw [level_grouping μ m ρ leaves s i.val hdepth]

/-- Before a layer's rounds, its normalized partial sum is the batch of true layer evaluations. -/
theorem weightedPartial_initial (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point : List E) (hdepth : m + ρ ≤ μ) :
    weightedPartial m (cofactor μ m ρ leaves lam) point [] =
      batch lam (fun s ↦ mle m (level μ m leaves s) point) := by
  simp only [weightedPartial, List.length_nil, Nat.sub_zero, List.nil_append, Nat.zero_add,
    cofactor_bits μ m ρ leaves lam _ hdepth, batch, mle, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At a fixed prefix, a three-tree batch has at most two roots. -/
theorem combiner_local_le (truth claims : Fin 3 → E) (hne : truth ≠ claims) :
    Pr{let lam ← ($ᵗ E)}[batch lam truth = batch lam claims] ≤ overE 2 := by
  have heq (lam : E) (v : Fin 3 → E) : batch lam v =
      (messagePolynomial 2 v).eval lam := by
    rw [messagePolynomial_eval]
    exact Finset.sum_congr rfl fun s _ ↦ mul_comm _ _
  simp only [heq]
  exact sumcheck_polynomial_eval_eq_le _ _ _
    (fun h ↦ hne (messagePolynomial_injective 2 h))
    (messagePolynomial_degree 2 truth) (messagePolynomial_degree 2 claims)

/-- A fixed nonzero constraint rider can disappear at at most one value of a newly fixed coordinate. -/
theorem rider_coordinate_local_le {W : Type} (R : Riders W) (q₀ : W)
    (σ : ℕ → Option E) (k : ℕ) (_hfresh : σ k = none) (hne : ¬ RidersRestricted R q₀ σ) :
    Pr{let r ← ($ᵗ E)}[RidersRestricted R q₀ (Function.update σ k (some r))] ≤ overE 1 := by
  classical
  rw [overE, SampleableType.prEvent_uniformSample_le_div_iff]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha := (Finset.mem_filter.mp ha).2
  have hb := (Finset.mem_filter.mp hb).2
  by_contra hab
  apply hne
  intro i z hz hfix
  by_cases hk : k < R.height i
  · have good (r : E) (hr : RidersRestricted R q₀ (Function.update σ k (some r))) :
        rider R q₀ i (z.set k r) = 0 := by
      apply hr i _ (by simpa only [List.length_set] using hz)
      intro j x hx hj
      by_cases hjk : j = k
      · subst j
        have hxr : r = x := Option.some.inj (by simpa only [Function.update_self] using hx)
        subst x
        simp only [List.getElem?_set_self (hz ▸ hk), Option.getD_some]
      · rw [Function.update_of_ne hjk] at hx
        rw [List.getElem?_set_ne (Ne.symm hjk)]
        exact hfix j x hx hj
    have ea := good a ha
    have eb := good b hb
    rw [rider, mle_set _ _ z hz k hk a] at ea
    rw [rider, mle_set _ _ z hz k hk b] at eb
    let A := rider R q₀ i (z.set k 0)
    let B := rider R q₀ i (z.set k 1)
    change (1 - a) * A + a * B = 0 at ea
    change (1 - b) * A + b * B = 0 at eb
    have hBA : B = A := by
      have hmul : (a - b) * (B - A) = 0 := by linear_combination ea - eb
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab))
    have hA : A = 0 := by rw [hBA] at ea; linear_combination ea
    have hs : z.set k (z.getD k 0) = z := by
      rw [List.getD_eq_getElem _ _ (hz ▸ hk), List.set_getElem_self]
    rw [← hs, rider, mle_set _ _ z hz k hk (z.getD k 0)]
    change (1 - z.getD k 0) * A + z.getD k 0 * B = 0
    rw [hBA, hA, mul_zero, mul_zero, add_zero]
  · apply ha i z hz
    intro j x hx hj
    rw [Function.update_of_ne (by omega : j ≠ k)] at hx
    exact hfix j x hx hj

/-- A wrong descendant table agrees after a fresh multilinear coordinate at at most one root. -/
theorem interpolation_local_le (n : ℕ) (P Q : ℕ → E) (u : List E)
    (hne : ∃ a : Fin (2 ^ n), mle u.length (fun b ↦ P (b + 2 ^ u.length * a.val)) u ≠
      mle u.length (fun b ↦ Q (b + 2 ^ u.length * a.val)) u) :
    Pr{let r ← ($ᵗ E)}[∀ a : Fin (2 ^ (n - 1)),
      mle (u.length + 1) (fun b ↦ P (b + 2 ^ (u.length + 1) * a.val)) (u ++ [r]) =
      mle (u.length + 1) (fun b ↦ Q (b + 2 ^ (u.length + 1) * a.val)) (u ++ [r])] ≤ overE 1 := by
  classical
  obtain ⟨a, wrong⟩ := hne
  have hhalf : a.val / 2 < 2 ^ (n - 1) := by
    cases n with
    | zero => have := a.isLt; norm_num at this ⊢
    | succ n =>
      have ha : a.val < 2 ^ n * 2 := by simpa only [pow_succ] using a.isLt
      simpa only [Nat.add_sub_cancel] using (by omega : a.val / 2 < 2 ^ n)
  let half : Fin (2 ^ (n - 1)) := ⟨a.val / 2, hhalf⟩
  let A := mle u.length (fun b ↦ P (b + 2 ^ (u.length + 1) * half.val)) u -
    mle u.length (fun b ↦ Q (b + 2 ^ (u.length + 1) * half.val)) u
  let B := mle u.length (fun b ↦ P (b + 2 ^ u.length + 2 ^ (u.length + 1) * half.val)) u -
    mle u.length (fun b ↦ Q (b + 2 ^ u.length + 2 ^ (u.length + 1) * half.val)) u
  rw [overE, SampleableType.prEvent_uniformSample_le_div_iff]
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have er := (Finset.mem_filter.mp hr).2 half
  have es := (Finset.mem_filter.mp hs).2 half
  rw [mle_snoc, mle_snoc] at er es
  have er' : (1 - r) * A + r * B = 0 := by dsimp only [A, B]; linear_combination er
  have es' : (1 - s) * A + s * B = 0 := by dsimp only [A, B]; linear_combination es
  by_contra hrs
  have hBA : B = A := by
    have hmul : (r - s) * (B - A) = 0 := by linear_combination er' - es'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hrs))
  have hA : A = 0 := by rw [hBA] at er'; linear_combination er'
  have hB : B = 0 := hBA.trans hA
  have hmod := Nat.mod_lt a.val (by decide : 0 < 2)
  rcases (by omega : a.val % 2 = 0 ∨ a.val % 2 = 1) with heven | hodd
  · have hidx (b : ℕ) : b + 2 ^ u.length * a.val = b + 2 ^ (u.length + 1) * half.val := by
      have ha : a.val = 2 * half.val := by dsimp only [half]; omega
      rw [ha, pow_succ]
      ring
    apply wrong
    apply sub_eq_zero.mp
    simpa only [A, hidx] using hA
  · have hidx (b : ℕ) : b + 2 ^ u.length * a.val = b + 2 ^ u.length + 2 ^ (u.length + 1) * half.val := by
      have ha : a.val = 1 + 2 * half.val := by dsimp only [half]; omega
      rw [ha, pow_succ]
      ring
    apply wrong
    apply sub_eq_zero.mp
    simpa only [B, hidx] using hB

/-- Distinct normalized degree-four (or binary degree-two) messages coincide at at most their degree many fresh challenges. -/
theorem round_local_le (d : ℕ) (equality current : E) (p q : Message d) (hne : p ≠ q) :
    Pr{let r ← ($ᵗ E)}[evaluate d equality current p r = evaluate d equality current q r] ≤ overE d := by
  simp only [evaluate, ← messagePolynomial_eval]
  apply sumcheck_polynomial_eval_eq_le _ _ _ _ (messagePolynomial_degree _ _)
    (messagePolynomial_degree _ _)
  intro h
  have hd := messagePolynomial_injective d h
  apply hne
  funext j
  exact congrFun hd j.succ

set_option maxHeartbeats 1600000 in
/-- The three-tree combiner's actual existential bad-witness event, at one fixed layer prefix. -/
theorem combiner_badChallenge_le {W : Type} (R : Riders W) (q₀ : W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (rest : List ℕ) (c : Claim) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hc : c.point.length = m) (hdepth : m + ρ ≤ μ) :
    Pr{let lam ← ($ᵗ E)}[RoundExtractor.badChallenge
      (Retained.extractor q₀ (labels R μ leaves tail out (ρ :: rest) m c active)) lam] ≤ overE 2 := by
  classical
  let truth := fun side ↦ mle m (level μ m (leaves q₀) side) c.point
  have inclusion (lam : E) (bad : RoundExtractor.badChallenge
      (Retained.extractor q₀ (labels R μ leaves tail out (ρ :: rest) m c active)) lam) :
      truth ≠ c.values ∧ batch lam truth = batch lam c.values := by
    change ∃ q, ¬ (q = q₀ ∧ layerRelation R μ m leaves c active q) ∧ q = q₀ ∧
      Retained.input (roundsLabels R μ m ρ leaves rest.isEmpty c.point lam
        (protocol tail rest (m + ρ))
        (fun next good ↦ labels R μ leaves tail out rest (m + ρ) next good)
        m [] (batch lam c.values) active) q at bad
    obtain ⟨q, bad, same, good⟩ := bad
    subst q
    rw [roundsLabels_input] at good
    obtain ⟨ha, hf, _, hr, hvalue⟩ := good
    have riders := (riderState_empty_iff R rest.isEmpty ρ q₀).mp hr
    constructor
    · intro eq
      apply bad
      exact ⟨rfl, ha, hf, riders, hc, fun side ↦ congrFun eq.symm side⟩
    · rw [weightedPartial_initial μ m ρ (leaves q₀) lam c.point hdepth] at hvalue
      exact hvalue.symm
  by_cases hne : truth ≠ c.values
  · exact (prEvent_mono _ _ _ fun lam bad ↦ (inclusion lam bad).2).trans
      (combiner_local_le truth c.values hne)
  · apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun lam bad ↦ hne (inclusion lam bad).1)
    simp only [prEvent_false, zero_le]

/-- A child-coordinate challenge fixes exactly its new rider coordinate. -/
theorem partialPoint_snoc_left (ρ : ℕ) (χ u : List E) (r : E) :
    partialPoint ρ χ (u ++ [r]) = Function.update (partialPoint ρ χ u) u.length (some r) := by
  funext k
  by_cases hk : k < u.length
  · rw [Function.update_of_ne (by omega : k ≠ u.length)]
    simp only [partialPoint, List.length_append, List.length_singleton, hk,
      show k < u.length + 1 from by omega, ↓reduceIte, List.getElem?_append_left hk]
  · by_cases heq : k = u.length
    · subst k
      simp only [Function.update_self, partialPoint, List.length_append, List.length_singleton,
        Nat.lt_succ_self, ↓reduceIte, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    · rw [Function.update_of_ne heq]
      simp only [partialPoint, List.length_append, List.length_singleton, hk,
        show ¬ k < u.length + 1 from by omega, ↓reduceIte]
/-- The next child-coordinate is absent from the rider prefix. -/
theorem partialPoint_fresh_left (ρ : ℕ) (χ u : List E) (hu : u.length < ρ) :
    partialPoint ρ χ u u.length = none := by
  simp only [partialPoint, lt_self_iff_false, ↓reduceIte, not_le.mpr hu]
/-- A sumcheck challenge fixes its high physical coordinate in the rider prefix. -/
theorem partialPoint_snoc_right (ρ : ℕ) (χ : List E) (r : E) :
    partialPoint ρ (χ ++ [r]) [] =
      Function.update (partialPoint ρ χ []) (ρ + χ.length) (some r) := by
  funext k
  by_cases heq : k = ρ + χ.length
  · subst k
    simp only [Function.update_self, partialPoint, List.length_nil, Nat.not_lt_zero,
      ↓reduceIte, Nat.le_add_right, Nat.add_sub_cancel_left,
      List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · rw [Function.update_of_ne heq]
    unfold partialPoint
    simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
    split_ifs with hk
    · by_cases h : k - ρ < χ.length
      · exact List.getElem?_append_left h
      · rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega), List.getElem?_eq_none (by omega)]
    · rfl
/-- The next high coordinate is absent from the rider prefix. -/
theorem partialPoint_fresh_right (ρ : ℕ) (χ : List E) :
    partialPoint ρ χ [] (ρ + χ.length) = none := by
  simp only [partialPoint, List.length_nil, Nat.not_lt_zero, ↓reduceIte,
    Nat.le_add_right, Nat.add_sub_cancel_left, List.getElem?_length]
/-- A false rider condition survives one child-coordinate restriction with probability at most one over the field size. -/
theorem rider_interpolation_local_le {W : Type} (R : Riders W) (q : W)
    (last : Bool) (ρ : ℕ) (χ u : List E) (hu : u.length < ρ)
    (hne : ¬ riderState R last ρ χ u q) :
    Pr{let r ← ($ᵗ E)}[riderState R last ρ χ (u ++ [r]) q] ≤ overE 1 := by
  cases last with
  | false =>
    have he : ∀ r, ¬ riderState R false ρ χ (u ++ [r]) q := fun _ ↦ hne
    exact (prEvent_mono _ _ (fun _ ↦ False) (fun r hr ↦ he r hr)).trans (by simp only [prEvent_false, zero_le])
  | true =>
    simp only [riderState, ↓reduceIte, partialPoint_snoc_left ρ χ u _]
    exact rider_coordinate_local_le R q (partialPoint ρ χ u) u.length
      (partialPoint_fresh_left ρ χ u hu) hne
/-- A false rider condition survives one high-coordinate restriction with probability at most one over the field size. -/
theorem rider_sumcheck_local_le {W : Type} (R : Riders W) (q : W)
    (last : Bool) (ρ : ℕ) (χ : List E)
    (hne : ¬ riderState R last ρ χ [] q) :
    Pr{let r ← ($ᵗ E)}[riderState R last ρ (χ ++ [r]) [] q] ≤ overE 1 := by
  cases last with
  | false =>
    have he : ∀ r, ¬ riderState R false ρ (χ ++ [r]) [] q := fun _ ↦ hne
    exact (prEvent_mono _ _ (fun _ ↦ False) (fun r hr ↦ he r hr)).trans (by simp only [prEvent_false, zero_le])
  | true =>
    simp only [riderState, ↓reduceIte, partialPoint_snoc_right]
    exact rider_coordinate_local_le R q (partialPoint ρ χ []) (ρ + χ.length)
      (partialPoint_fresh_right ρ χ) hne

/-- Splitting a point splits the Boolean table into contiguous low-coordinate blocks. -/
theorem mle_append (values : ℕ → E) (u v : List E) :
    mle (u.length + v.length) values (u ++ v) =
      mle v.length (fun i ↦ mle u.length (fun b ↦ values (b + 2 ^ u.length * i)) u) v := by
  let U : Vector E u.length := ⟨u.toArray, by simp only [List.size_toArray]⟩
  let V : Vector E v.length := ⟨v.toArray, by simp only [List.size_toArray]⟩
  have hU : U.toList = u := by simp only [U, Vector.toList_mk]
  have hV : V.toList = v := by simp only [V, Vector.toList_mk]
  have hpoint : (U ++ V).toList = u ++ v := by rw [Vector.toList_append, hU, hV]
  let T := Vector.ofFn fun i : Fin (2 ^ (u.length + v.length)) ↦ values i.val
  have he (j : Fin (2 ^ v.length)) :
      CompPoly.CMlPolynomialEval.evalMle (Algebra.slice T j) U =
      mle u.length (fun i ↦ values (i + 2 ^ u.length * j.val)) u := by
    have hs : Algebra.slice T j = Vector.ofFn (fun i : Fin (2 ^ u.length) ↦
        values (i.val + 2 ^ u.length * j.val)) := by
      apply Vector.ext
      intro k hk
      simp only [Algebra.slice, T, Fin.getElem_fin, Vector.getElem_ofFn, Algebra.cubeIndex]
    rw [hs]
    exact (mle_toList u.length (fun i ↦ values (i + 2 ^ u.length * j.val)) U).symm.trans
      (congrArg (mle u.length _) hU)
  rw [← hpoint, mle_toList, Algebra.evalMle_split]
  change (∑ j : Fin (2 ^ v.length), (CompPoly.CMlPolynomialEval.lagrangeBasis V)[j] *
    CompPoly.CMlPolynomialEval.evalMle (Algebra.slice T j) U) = _
  simp only [he, mle]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin]
  rw [Algebra.lagrangeBasis_getElem_nat]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  have hk : V[k.val]'k.isLt = v.getD k.val 0 := by
    simp only [V, Vector.getElem_mk, List.getElem_toArray, List.getD_eq_getElem _ _ k.isLt]
  simp only [Fin.getElem_fin]
  rw [hk]
  dsimp only [eqFactor, bit]
  split <;> simp only [sub_zero, sub_self, mul_one, mul_zero, zero_add, add_zero]

/-- At full length the partial point is exactly the concatenated physical point. -/
theorem partialPoint_full (ρ : ℕ) (χ u : List E) (hu : u.length = ρ) :
    partialPoint ρ χ u = fun k ↦ (u ++ χ)[k]? := by
  funext k
  unfold partialPoint
  by_cases hk : k < u.length
  · simp only [hk, ↓reduceIte, List.getElem?_append_left hk]
  · rw [ite_eq_right hk, ite_eq_left (by omega : ρ ≤ k),
      List.getElem?_append_right (by omega : u.length ≤ k), hu]

/-- Restricting every coordinate of a rider is its evaluation at that point. -/
theorem ridersRestricted_full_iff {W : Type} (R : Riders W) (q : W)
    (z : List E) (hz : R.maxHeight ≤ z.length) :
    RidersRestricted R q (fun k ↦ z[k]?) ↔
      ∀ i, rider R q i (z.take (R.height i)) = 0 := by
  constructor
  · intro h i
    apply h i
    · rw [List.length_take, Nat.min_eq_left ((R.height_le i).trans hz)]
    · intro k a ha hk
      simp only [List.getElem?_take_of_lt hk, ha, Option.getD_some]
  · intro h i w hw hfix
    rw [rider, mle_congr (R.height i) _ w (z.take (R.height i)) ?_]
    · exact h i
    · intro k hk
      have hkz : k < z.length := hk.trans_le ((R.height_le i).trans hz)
      have hf := hfix k z[k] (List.getElem?_eq_getElem hkz) hk
      simpa only [List.getD, List.getElem?_take_of_lt hk,
        List.getElem?_eq_getElem hkz, Option.getD_some] using hf
/-- A full child interpolation is the next product-tree layer evaluation. -/
theorem childValue_interpolation (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E)
    (s : Fin 3) (χ u : List E) (hχ : χ.length = m) (hu : u.length = ρ) :
    mle (m + ρ) (level μ (m + ρ) leaves s) (u ++ χ) =
      mle u.length (fun b ↦ childValue μ m ρ leaves s b χ) u := by
  rw [show m + ρ = u.length + χ.length by omega, mle_append]
  unfold childValue
  rw [← hχ, ← hu]
  simp only [Nat.add_comm χ.length u.length]
  simp only [mle, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Interpolation labels retain the interpolation predicate through their full-point boundary. -/
theorem interpolationLabels_input {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (χ u : List E) (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hχ : χ.length = m) (n : ℕ) (hu : u.length + n = ρ)
    (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q)) (q : W) :
    Retained.input (interpolationLabels R μ m ρ leaves last χ children active tail out n u) q ↔
      interpolationRelation R μ m ρ leaves last χ u children active q := by
  cases n with
  | succ n => rfl
  | zero =>
    have hu : u.length = ρ := by omega
    change Retained.input (out ⟨u ++ χ, fun s ↦ interpolated ρ children u s 0⟩ active) q ↔ _
    rw [hout]
    have hr : (if last then ∀ i,
        rider R q i ((u ++ χ).take (R.height i)) = 0 else RidersZero R q) ↔
        riderState R last ρ χ u q := by
      cases last with
      | false => rfl
      | true =>
        simp only [riderState, ↓reduceIte, partialPoint_full ρ χ u hu]
        exact (ridersRestricted_full_iff R q (u ++ χ) (by
          simp only [List.length_append, hχ, hu]; have := hcover rfl; omega)).symm
    rw [hr]
    simp only [Claim.Holds, List.length_append, hχ, hu, Nat.add_comm ρ m,
      true_and, childValue_interpolation μ m ρ (leaves q) _ χ u hχ hu]
    unfold interpolationRelation
    constructor
    · rintro ⟨ha, hf, hc, hr⟩
      refine ⟨ha, hf, hr, fun s a ↦ ?_⟩
      have he : a.val = 0 := by
        have hb : a.val < 1 := by simpa only [hu, Nat.sub_self, pow_zero] using a.isLt
        omega
      simpa only [he, hu, Nat.mul_zero, Nat.add_zero] using hc s
    · rintro ⟨ha, hf, hr, hc⟩
      refine ⟨ha, hf, fun s ↦ ?_, hr⟩
      simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, hu] using hc s ⟨0, Nat.two_pow_pos _⟩

/-- Interpolation of two endpoint values as a formal univariate polynomial. -/
noncomputable def affinePolynomial (a b : E) : Polynomial E :=
  Polynomial.C a * (1 - Polynomial.X) + Polynomial.X * Polynomial.C b
/-- The endpoint interpolation polynomial has degree at most one. -/
theorem affinePolynomial_degree (a b : E) : (affinePolynomial a b).natDegree ≤ 1 := by
  unfold affinePolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_mul_le).trans (by
      have h := Polynomial.natDegree_sub_le (1 : Polynomial E) Polynomial.X
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_one, Polynomial.natDegree_X] at *
      omega)
  · simpa only [Polynomial.natDegree_X, Polynomial.natDegree_C, Nat.add_zero] using (Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Polynomial.C b))
/-- List updates insert exactly the next prefix coordinate. -/
theorem prefix_set (χ v : List E) (r : E) :
    (χ ++ [0] ++ v).set χ.length r = χ ++ [r] ++ v := by
  rw [List.append_assoc, List.set_append_right χ.length r (le_refl _), Nat.sub_self]
  simp only [List.cons_append, List.set_cons_zero, List.append_assoc]
/-- Restriction of a multilinear extension to the next coordinate is endpoint interpolation. -/
theorem childValue_affine (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (s : Fin 3) (a : ℕ)
    (χ v : List E) (hlen : χ.length + 1 + v.length = m) (r : E) :
    childValue μ m ρ leaves s a (χ ++ [r] ++ v) =
      (affinePolynomial (childValue μ m ρ leaves s a (χ ++ [0] ++ v))
        (childValue μ m ρ leaves s a (χ ++ [1] ++ v))).eval r := by
  have hz : (χ ++ [0] ++ v).length = m := by simp only [List.length_append, List.length_singleton]; omega
  have h := mle_set m (fun i ↦ level μ (m + ρ) leaves s (a + 2 ^ ρ * i))
    (χ ++ [0] ++ v) hz χ.length (by omega) r
  simp only [prefix_set] at h
  rw [childValue, h]
  simp only [affinePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C, childValue]
  ring
/-- Honest cofactor polynomial with the remaining Boolean coordinates fixed. -/
noncomputable def cofactorPolynomial (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (χ v : List E) : Polynomial E :=
  ∑ s : Fin 3, Polynomial.C (lam ^ s.val) * ∏ a : Fin (2 ^ ρ),
    affinePolynomial (childValue μ m ρ leaves s a.val (χ ++ [0] ++ v))
      (childValue μ m ρ leaves s a.val (χ ++ [1] ++ v))
/-- Each child contributes degree one to the cofactor. -/
theorem cofactorPolynomial_degree (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (χ v : List E) : (cofactorPolynomial μ m ρ leaves lam χ v).natDegree ≤ 2 ^ ρ := by
  unfold cofactorPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _
  apply le_trans (Polynomial.natDegree_C_mul_le _ _)
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    Finset.sum_le_sum (s := Finset.univ) (fun (a : Fin (2 ^ ρ)) _ ↦ affinePolynomial_degree
      (childValue μ m ρ leaves s a.val (χ ++ [0] ++ v))
      (childValue μ m ρ leaves s a.val (χ ++ [1] ++ v)))
/-- Evaluation of the honest cofactor polynomial recovers the restricted cofactor. -/
theorem cofactorPolynomial_eval (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (χ v : List E) (hlen : χ.length + 1 + v.length = m) (r : E) :
    (cofactorPolynomial μ m ρ leaves lam χ v).eval r =
      cofactor μ m ρ leaves lam (χ ++ [r] ++ v) := by
  simp only [cofactorPolynomial, cofactor, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, ← childValue_affine μ m ρ leaves _ _ χ v hlen r]
/-- Boolean indices split into their low and high coordinate lists. -/
theorem bits_cubeIndex (k n : ℕ) (i : Fin (2 ^ k)) (j : Fin (2 ^ n)) :
    (List.ofFn fun a : Fin (k + n) ↦ bit (Algebra.cubeIndex i j).val a.val) =
      (List.ofFn fun a : Fin k ↦ bit i.val a.val) ++
        List.ofFn (fun a : Fin n ↦ bit j.val a.val) := by
  have h := congrArg Vector.toList (Algebra.boolVec_append (R := E) i j)
  simpa only [Algebra.boolVec, Vector.toList_ofFn, Vector.toList_append, bit] using h.symm

/-- Summing over the Boolean cube separates its first coordinate. -/
theorem cube_sum_head (n : ℕ) (f : List E → E) :
    (∑ i : Fin (2 ^ (n + 1)), f (List.ofFn fun k : Fin (n + 1) ↦ bit i.val k.val)) =
      ∑ i : Fin (2 ^ n),
        (f (0 :: List.ofFn (fun k : Fin n ↦ bit i.val k.val)) +
          f (1 :: List.ofFn (fun k : Fin n ↦ bit i.val k.val))) := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1, Algebra.sum_cube_split]
  apply Finset.sum_congr rfl
  intro j _
  have hb (a : Fin (2 ^ 1)) :
      (List.ofFn fun k : Fin (1 + n) ↦ bit (Algebra.cubeIndex a j).val k.val) =
        bit a.val 0 :: List.ofFn (fun k : Fin n ↦ bit j.val k.val) := by
    rw [bits_cubeIndex]
    rfl
  rw [Finset.sum_congr rfl (fun a _ ↦ congrArg f (hb a))]
  change (∑ a : Fin 2, f (bit a.val 0 :: List.ofFn (fun k : Fin n ↦ bit j.val k.val))) = _
  rw [Fin.sum_univ_two]
  rfl
/-- A normalized Boolean tail sum with its dimension kept explicit. -/
def weightedCube (n : ℕ) (f : List E → E) (point χ : List E) : E :=
  ∑ i : Fin (2 ^ n), f (χ ++ List.ofFn (fun k : Fin n ↦ bit i.val k.val)) *
    ∏ k : Fin n, eqFactor (point.getD (χ.length + k.val) 0) (bit i.val k.val)
/-- Exposing the tail dimension preserves the normalized partial sum. -/
theorem weightedPartial_eq_weightedCube (m : ℕ) (f : List E → E) (point χ : List E) :
    weightedPartial m f point χ = weightedCube (m - χ.length) f point χ := rfl
set_option maxHeartbeats 1600000 in
/-- A normalized partial sum is the equality-weighted sum of its two Boolean successors. -/
theorem weightedPartial_snoc (m n : ℕ) (f : List E → E) (point χ : List E)
    (hlen : χ.length + (n + 1) = m) :
    weightedPartial m f point χ =
      (1 - point.getD χ.length 0) * weightedPartial m f point (χ ++ [0]) +
        point.getD χ.length 0 * weightedPartial m f point (χ ++ [1]) := by
  have hd : m - χ.length = n + 1 := by omega
  have hn : m - (χ.length + 1) = n := by omega
  simp only [weightedPartial_eq_weightedCube, List.length_append, List.length_singleton, hd, hn]
  unfold weightedCube
  let F := fun z : List E ↦ f (χ ++ z) *
    ∏ k : Fin (n + 1), eqFactor (point.getD (χ.length + k.val) 0) (z.getD k.val 0)
  have hc (i : Fin (2 ^ (n + 1))) :
      F (List.ofFn fun k : Fin (n + 1) ↦ bit i.val k.val) =
        f (χ ++ List.ofFn (fun k : Fin (n + 1) ↦ bit i.val k.val)) *
          ∏ k : Fin (n + 1), eqFactor (point.getD (χ.length + k.val) 0) (bit i.val k.val) := by
    dsimp only [F]
    apply congrArg (fun a : E ↦ f (χ ++ List.ofFn (fun k : Fin (n + 1) ↦ bit i.val k.val)) * a)
    apply Finset.prod_congr rfl
    intro k _
    apply congrArg (eqFactor (point.getD (χ.length + k.val) 0))
    exact (List.getD_eq_getElem (List.ofFn fun j : Fin (n + 1) ↦ bit i.val j.val) 0
      (by simpa only [List.length_ofFn] using k.isLt)).trans (by simp only [List.getElem_ofFn])
  rw [show (∑ i : Fin (2 ^ (n + 1)),
      f (χ ++ List.ofFn (fun k : Fin (n + 1) ↦ bit i.val k.val)) *
        ∏ k : Fin (n + 1), eqFactor (point.getD (χ.length + k.val) 0) (bit i.val k.val)) =
      ∑ i : Fin (2 ^ (n + 1)), F (List.ofFn fun k : Fin (n + 1) ↦ bit i.val k.val) from
        Finset.sum_congr rfl (fun i _ ↦ (hc i).symm), cube_sum_head]
  simp only [F, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Finset.sum_add_distrib,
    List.length_append, List.length_singleton, List.append_assoc, List.cons_append, List.nil_append,
    eqFactor, sub_zero, sub_self, mul_one, mul_zero, zero_add, add_zero]
  simp only [Nat.add_assoc, Nat.add_comm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : E ↦ a + b)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring
/-- The honest univariate normalized message at a fixed prefix. -/
noncomputable def partialPolynomial (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) : Polynomial E :=
  ∑ i : Fin (2 ^ (m - (χ.length + 1))),
    Polynomial.C (∏ k : Fin (m - (χ.length + 1)),
      eqFactor (point.getD (χ.length + 1 + k.val) 0) (bit i.val k.val)) *
    cofactorPolynomial μ m ρ leaves lam χ
      (List.ofFn fun k : Fin (m - (χ.length + 1)) ↦ bit i.val k.val)
/-- Averaging over remaining Boolean coordinates preserves the cofactor degree. -/
theorem partialPolynomial_degree (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) : (partialPolynomial μ m ρ leaves lam point χ).natDegree ≤ 2 ^ ρ := by
  unfold partialPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (cofactorPolynomial_degree μ m ρ leaves lam χ _)
/-- Evaluation of the honest normalized message is the next partial sum. -/
theorem partialPolynomial_eval (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) (hχ : χ.length < m) (r : E) :
    (partialPolynomial μ m ρ leaves lam point χ).eval r =
      weightedPartial m (cofactor μ m ρ leaves lam) point (χ ++ [r]) := by
  rw [weightedPartial_eq_weightedCube]
  have hd : m - (χ ++ [r]).length = m - (χ.length + 1) := by
    simp only [List.length_append, List.length_singleton]
  rw [hd]
  simp only [partialPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, weightedCube]
  apply Finset.sum_congr rfl
  intro i _
  rw [cofactorPolynomial_eval μ m ρ leaves lam χ _ (by simp only [List.length_ofFn]; omega) r]
  simp only [List.length_append, List.length_singleton]
  rw [List.append_assoc, mul_comm]

/-- The honest transmitted tail of the weighted partial cofactor at a fixed prefix. -/
noncomputable def partialMessage (μ m ρ : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) : Message (2 ^ ρ) :=
  encode (2 ^ ρ) ⟨partialPolynomial μ m ρ leaves lam point χ,
    Polynomial.mem_degreeLE.mpr
      (Polynomial.natDegree_le_iff_degree_le.mp
        (partialPolynomial_degree μ m ρ leaves lam point χ))⟩

/-- An honest tail decoded at the true running claim recovers the partial cofactor. -/
theorem partialMessage_model (μ m ρ n : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) (hχ : χ.length + (n + 1) = m) :
    (cofactorModel (2 ^ ρ) (point.getD χ.length 0)
      (weightedPartial m (cofactor μ m ρ leaves lam) point χ)
      (partialMessage μ m ρ leaves lam point χ)).val =
        partialPolynomial μ m ρ leaves lam point χ := by
  apply congrArg Subtype.val (cofactorModel_encode _ _ _ _ ?_)
  change (1 - point.getD χ.length 0) * (partialPolynomial μ m ρ leaves lam point χ).eval 0 +
    point.getD χ.length 0 * (partialPolynomial μ m ρ leaves lam point χ).eval 1 = _
  rw [partialPolynomial_eval μ m ρ leaves lam point χ (by omega) 0,
    partialPolynomial_eval μ m ρ leaves lam point χ (by omega) 1,
    ← weightedPartial_snoc m n _ point χ hχ]

/-- Honest transmitted cofactor messages update to the next weighted partial sum. -/
theorem partialMessage_evaluate (μ m ρ n : ℕ) (leaves : Fin 3 → ℕ → E) (lam : E)
    (point χ : List E) (hχ : χ.length + (n + 1) = m) (x : E) :
    evaluate (2 ^ ρ) (point.getD χ.length 0)
      (weightedPartial m (cofactor μ m ρ leaves lam) point χ)
      (partialMessage μ m ρ leaves lam point χ) x =
        weightedPartial m (cofactor μ m ρ leaves lam) point (χ ++ [x]) := by
  rw [show evaluate _ _ _ _ x = _ from cofactorModel_evaluate_eq _ _ _ _ x,
    partialMessage_model μ m ρ n leaves lam point χ hχ,
    partialPolynomial_eval μ m ρ leaves lam point χ (by omega) x]

set_option maxHeartbeats 1600000 in
/-- A normalized round's actual bad-witness event, including riders restricted on this same challenge. -/
theorem normalized_round_badChallenge_le {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ n : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (point χ : List E) (lam current : E) (active : Bool) (message : Message (2 ^ ρ))
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (_hρ : ρ = 1 ∨ ρ = 2) (hc : point.length = m) (hχ : χ.length + (n + 1) = m) :
    Pr{let r ← roundSample (2 ^ ρ) (point.getD χ.length 0) current message}[
      RoundExtractor.badChallenge
        ((Retained.extractor q₀ (roundsLabels R μ m ρ leaves last point lam tail out
          (n + 1) χ current active) message).2.2) r] ≤ overE (2 ^ ρ) := by
  classical
  have next (r : E) (bad : RoundExtractor.badChallenge
      ((Retained.extractor q₀ (roundsLabels R μ m ρ leaves last point lam tail out
        (n + 1) χ current active) message).2.2) (some r)) :
      ¬ roundRelation R μ m ρ leaves last point lam current χ active q₀ ∧
        roundRelation R μ m ρ leaves last point lam (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r) (χ ++ [r])
          (active && check (2 ^ ρ) (point.getD χ.length 0) current message) q₀ := by
    change ∃ q, ¬ (q = q₀ ∧ roundRelation R μ m ρ leaves last point lam current χ active q) ∧
      q = q₀ ∧ Retained.input (roundsLabels R μ m ρ leaves last point lam tail out n (χ ++ [r])
        (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r) (active && check (2 ^ ρ) (point.getD χ.length 0) current message)) q at bad
    obtain ⟨q, bad, same, good⟩ := bad
    subst q
    rw [roundsLabels_input] at good
    exact ⟨fun h ↦ bad ⟨rfl, h⟩, good⟩
  have empty : ¬ RoundExtractor.badChallenge
      ((Retained.extractor q₀ (roundsLabels R μ m ρ leaves last point lam tail out
        (n + 1) χ current active) message).2.2) none := by
    rintro ⟨q, _, _, impossible⟩
    exact impossible.elim
  by_cases hcheck : check (2 ^ ρ) (point.getD χ.length 0) current message = true
  · simp only [roundSample, hcheck, ↓reduceIte, prEvent_map]
    by_cases hr : riderState R last ρ χ [] q₀
    · by_cases hscalar : current = weightedPartial m (cofactor μ m ρ (leaves q₀) lam) point χ
      · apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun r bad ↦ ?_)
        · simp only [prEvent_false, zero_le]
        · obtain ⟨wrong, good⟩ := next r bad
          exact wrong ⟨(Bool.and_eq_true_iff.mp good.1).1, good.2.1, hc, hr, hscalar⟩
      · let P := (cofactorModel (2 ^ ρ) (point.getD χ.length 0) current message).val
        let Q := partialPolynomial μ m ρ (leaves q₀) lam point χ
        have hne : P ≠ Q := by
          intro heq
          have he (r : E) : evaluate (2 ^ ρ) (point.getD χ.length 0) current message r =
              weightedPartial m (cofactor μ m ρ (leaves q₀) lam) point (χ ++ [r]) := by
            rw [show evaluate (2 ^ ρ) (point.getD χ.length 0) current message r = P.eval r from
              cofactorModel_evaluate_eq _ _ _ _ _, heq]
            exact partialPolynomial_eval μ m ρ (leaves q₀) lam point χ (by omega) r
          have hpass := cofactor_weighted_sum (2 ^ ρ) (point.getD χ.length 0) current message
          rw [he 0, he 1, ← weightedPartial_snoc m n _ point χ hχ] at hpass
          exact hscalar hpass.symm
        apply le_trans (prEvent_mono _ _ _ ?_)
          (sumcheck_polynomial_eval_eq_le _ _ _ hne (cofactorModel_degree _ _ _ message)
            (partialPolynomial_degree μ m ρ (leaves q₀) lam point χ))
        intro r bad
        have hg := (next r bad).2.2.2.2.2
        exact (cofactorModel_evaluate_eq (2 ^ ρ) (point.getD χ.length 0) current message r).symm.trans
          (hg.trans (partialPolynomial_eval μ m ρ (leaves q₀) lam point χ (by omega) r).symm)
    · apply le_trans (prEvent_mono _ _ _ fun r bad ↦ (next r bad).2.2.2.2.1)
        ((rider_sumcheck_local_le R q₀ last ρ χ hr).trans ?_)
      unfold overE
      exact ENNReal.div_le_div_right (by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ ρ)) _
  · simp only [roundSample, hcheck, Bool.false_eq_true, ↓reduceIte, prEvent_pure, empty, zero_le]


/-- A child-coordinate's actual bad-witness event, with the progressive rider restriction included. -/
theorem interpolation_badChallenge_le {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ n : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (χ u : List E) (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hχ : χ.length = m) (hu : u.length + (n + 1) = ρ)
    (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q)) :
    Pr{let r ← ($ᵗ E)}[RoundExtractor.badChallenge
      (Retained.extractor q₀ (interpolationLabels R μ m ρ leaves last χ children active
        tail out (n + 1) u)) r] ≤ overE 1 := by
  classical
  have next (r : E) (bad : RoundExtractor.badChallenge
      (Retained.extractor q₀ (interpolationLabels R μ m ρ leaves last χ children active
        tail out (n + 1) u)) r) :
      ¬ interpolationRelation R μ m ρ leaves last χ u children active q₀ ∧
        interpolationRelation R μ m ρ leaves last χ (u ++ [r]) children active q₀ := by
    change ∃ q, ¬ (q = q₀ ∧ interpolationRelation R μ m ρ leaves last χ u children active q) ∧
      q = q₀ ∧ Retained.input (interpolationLabels R μ m ρ leaves last χ children active tail out n (u ++ [r])) q at bad
    obtain ⟨q, bad, same, good⟩ := bad
    subst q
    exact ⟨fun h ↦ bad ⟨rfl, h⟩, (interpolationLabels_input R μ m ρ leaves last χ (u ++ [r])
      children active tail out hχ n (by simp only [List.length_append, List.length_singleton]; omega)
      hcover hout q₀).mp good⟩
  by_cases hr : riderState R last ρ χ u q₀
  · by_cases hc : ∀ s, ∀ a : Fin (2 ^ (ρ - u.length)),
        interpolated ρ children u s a.val =
          mle u.length (fun b ↦ childValue μ m ρ (leaves q₀) s (b + 2 ^ u.length * a.val) χ) u
    · apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun r bad ↦ ?_)
      · simp only [prEvent_false, zero_le]
      · obtain ⟨wrong, good⟩ := next r bad
        exact wrong ⟨good.1, good.2.1, hr, hc⟩
    · obtain ⟨s, hs⟩ := not_forall.mp hc
      obtain ⟨a, ha⟩ := not_forall.mp hs
      let P := fun b ↦ children s ⟨b % 2 ^ ρ, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let Q := fun b ↦ childValue μ m ρ (leaves q₀) s b χ
      have hne : ∃ a : Fin (2 ^ (ρ - u.length)),
          mle u.length (fun b ↦ P (b + 2 ^ u.length * a.val)) u ≠
            mle u.length (fun b ↦ Q (b + 2 ^ u.length * a.val)) u := ⟨a, ha⟩
      apply le_trans (prEvent_mono _ _ _ ?_) (interpolation_local_le (ρ - u.length) P Q u hne)
      intro r bad
      have hg := (next r bad).2.2.2.2 s
      have he : ρ - (u ++ [r]).length = (ρ - u.length) - 1 := by
        simp only [List.length_append, List.length_singleton]; omega
      intro a
      have hga := hg ⟨a.val, by rw [he]; exact a.isLt⟩
      simpa only [interpolated, List.length_append, List.length_singleton, P, Q] using hga
  · exact (prEvent_mono _ _ _ fun r bad ↦ (next r bad).2.2.2.1).trans
      (rider_interpolation_local_le R q₀ last ρ χ u (by omega) hr)



/-- A zero-variable extension reads its only cell. -/
theorem mle_zero (values : ℕ → E) (z : List E) : mle 0 values z = values 0 := by
  simp only [mle, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin 1, values i.val) = values 0
  rw [Fin.sum_univ_one]
  rfl
/-- With all sumcheck coordinates sampled, the normalized partial sum is its cofactor evaluation. -/
theorem weightedPartial_full (m : ℕ) (f : List E → E) (point χ : List E)
    (hχ : χ.length = m) : weightedPartial m f point χ = f χ := by
  unfold weightedPartial
  rw [show m - χ.length = 0 by omega]
  simp only [List.ofFn_zero, List.append_nil, Fin.prod_univ_zero, mul_one]
  change (∑ _ : Fin 1, f χ) = f χ
  exact Fin.sum_univ_one _
/-- Child-coordinate challenges preserve prover preservation of their continuation. -/
theorem interpolation_prover_preserving {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hout : ∀ c good, c.point.length = m + ρ →
      (Retained.extractor q₀ (out c good)).IsProverPreserving tail.roles)
    (hχ : χ.length = m) (n : ℕ) (u : List E) (hu : u.length + n = ρ) :
    (Retained.extractor q₀ (interpolationLabels R μ m ρ leaves last χ children active tail out n u)).IsProverPreserving
      (interpolationProtocol tail n).roles := by
  induction n generalizing u with
  | zero =>
    apply hout
    simp only [List.length_append]
    omega
  | succ n ih =>
    refine ⟨?_, fun r ↦ ih (u ++ [r]) (by simp only [List.length_append, List.length_singleton]; omega)⟩
    intro r impossible
    cases impossible
/-- Honest descendant values passing the scalar check preserve the final normalized state. -/
theorem children_prover_preserving {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (point χ : List E) (lam current : E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hχ : χ.length = m) (hc : point.length = m)
    (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q))
    (hpres : ∀ c good, c.point.length = m + ρ →
      (Retained.extractor q₀ (out c good)).IsProverPreserving tail.roles) :
    (Retained.extractor q₀ (childrenLabels R μ m ρ leaves last point χ lam current active tail out)).IsProverPreserving
      (Protocol.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ).roles := by
  refine ⟨?_, fun children ↦ interpolation_prover_preserving R q₀ μ m ρ leaves last χ children _ tail out hpres hχ ρ [] (by simp only [List.length_nil, Nat.zero_add])⟩
  intro children _ q known
  change q = q₀ ∧ Retained.input (interpolationLabels R μ m ρ leaves last χ children
    (active && decide (current = ∑ s : Fin 3, lam ^ s.val * ∏ a : Fin (2 ^ ρ), children s a))
      tail out ρ []) q at known
  obtain ⟨same, good⟩ := known
  have good := (interpolationLabels_input R μ m ρ leaves last χ [] children _ tail out hχ ρ
    (by simp only [List.length_nil, Nat.zero_add]) hcover hout q).mp good
  obtain ⟨ha, hf, hr, values⟩ := good
  obtain ⟨ha, hcheck⟩ := Bool.and_eq_true_iff.mp ha
  have hvalues (s : Fin 3) (a : Fin (2 ^ ρ)) : children s a = childValue μ m ρ (leaves q) s a.val χ := by
    have h := values s a
    simpa only [interpolated, List.length_nil, Nat.sub_zero, mle_zero, pow_zero,
      Nat.zero_add, Nat.one_mul, Nat.mod_eq_of_lt a.isLt, Fin.eta] using h
  refine ⟨same, ha, hf, hc, hr, ?_⟩
  change current = weightedPartial m (cofactor μ m ρ (leaves q) lam) point χ
  rw [weightedPartial_full m _ point χ hχ]
  exact (of_decide_eq_true hcheck).trans (by simp only [cofactor, hvalues])
/-- Normalized oracle rounds preserve the backward identity maps of the descendant phase. -/
theorem rounds_prover_preserving {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (point : List E) (lam : E)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hc : point.length = m)
    (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q))
    (hpres : ∀ c good, c.point.length = m + ρ →
      (Retained.extractor q₀ (out c good)).IsProverPreserving tail.roles)
    (n : ℕ) (χ : List E) (current : E) (active : Bool) (hχ : χ.length + n = m) :
    (Retained.extractor q₀ (roundsLabels R μ m ρ leaves last point lam tail out n χ current active)).IsProverPreserving
      (roundsProtocol (2 ^ ρ)
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ) n).roles := by
  induction n generalizing χ current active with
  | zero =>
    exact children_prover_preserving R q₀ μ m ρ leaves last point χ lam current active
      tail out (by omega) hc hcover hout hpres
  | succ n ih =>
    refine ⟨fun _ _ known ↦ known, fun message ↦ ⟨?_, ?_⟩⟩
    · intro choice impossible
      cases impossible
    · intro choice
      cases choice with
      | none => trivial
      | some r =>
        apply ih
        simp only [List.length_append, List.length_singleton]
        omega
/-- A complete layer descent preserves its terminal protocol's prover maps. -/
theorem labels_prover_preserving {W : Type} (R : Riders W) (q₀ : W)
    (μ : ℕ) (leaves : W → Fin 3 → ℕ → E)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (hcover : R.maxHeight ≤ μ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ μ (leaves q) ∧
        ∀ i, rider R q i (c.point.take (R.height i)) = 0)
    (hpres : ∀ c good, c.point.length = μ →
      (Retained.extractor q₀ (out c good)).IsProverPreserving tail.roles)
    (steps : List ℕ) (m : ℕ) (c : Claim) (active : Bool)
    (hc : c.point.length = m) (hfinish : m + steps.sum = μ) :
    (Retained.extractor q₀ (labels R μ leaves tail out steps m c active)).IsProverPreserving
      (protocol tail steps m).roles := by
  induction steps generalizing m c active with
  | nil =>
    have hm : m = μ := by simpa only [List.sum_nil, Nat.add_zero] using hfinish
    exact hpres c active (hc.trans hm)
  | cons ρ rest ih =>
    refine ⟨?_, fun lam ↦ ?_⟩
    · intro lam impossible
      cases impossible
    · apply rounds_prover_preserving R q₀ μ m ρ leaves rest.isEmpty c.point lam
        (protocol tail rest (m + ρ))
        (fun next good ↦ labels R μ leaves tail out rest (m + ρ) next good) hc
      · intro hl
        have hr : rest = [] := List.isEmpty_iff.mp hl
        subst rest
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hfinish
        omega
      · intro next good q
        cases rest with
        | nil =>
          have hm : m + ρ = μ := by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using hfinish
          simp only [labels, List.isEmpty_nil, ↓reduceIte, hm]
          exact hout next good q
        | cons σ rest =>
          change layerRelation R μ (m + ρ) leaves next good q ↔ _
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, layerRelation]
          constructor
          · rintro ⟨ha, hf, hr, hc⟩
            exact ⟨ha, hf, hc, hr⟩
          · rintro ⟨ha, hf, hc, hr⟩
            exact ⟨ha, hf, hr, hc⟩
      · intro next good hn
        exact ih (m + ρ) next good hn (by simpa only [List.sum_cons, Nat.add_assoc] using hfinish)
      · simp only [List.length_nil, Nat.zero_add]


/-- Each interpolation prefix uses its named one-root local bound. -/
theorem interpolation_locally_bounded {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (χ : List E) (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (next : Claim → RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (hχ : χ.length = m) (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q))
    (hbound : ∀ c good, c.point.length = m + ρ →
      (Retained.extractor q₀ (out c good)).IsLocallyBounded tail.roles (next c))
    (n : ℕ) (u : List E) (hu : u.length + n = ρ) :
    (Retained.extractor q₀ (interpolationLabels R μ m ρ leaves last χ children active tail out n u)).IsLocallyBounded
      (interpolationProtocol tail n).roles (interpolationSchedule ρ χ children tail next n u) := by
  induction n generalizing u with
  | zero =>
    apply hbound
    simp only [List.length_append]
    omega
  | succ n ih =>
    constructor
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      exact interpolation_badChallenge_le R q₀ μ m ρ n leaves last χ u children active tail out hχ hu hcover hout
    · intro r
      apply ih
      simp only [List.length_append, List.length_singleton]
      omega
/-- Each normalized prefix uses its named cofactor bound and every descendant uses its interpolation bound. -/
theorem rounds_locally_bounded {W : Type} (R : Riders W) (q₀ : W)
    (μ m ρ : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (point : List E) (lam : E)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (next : Claim → RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (hρ : ρ = 1 ∨ ρ = 2) (hc : point.length = m)
    (hcover : last = true → R.maxHeight ≤ m + ρ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q))
    (hbound : ∀ c good, c.point.length = m + ρ →
      (Retained.extractor q₀ (out c good)).IsLocallyBounded tail.roles (next c))
    (n : ℕ) (χ : List E) (current : E) (active : Bool) (hχ : χ.length + n = m) :
    (Retained.extractor q₀ (roundsLabels R μ m ρ leaves last point lam tail out n χ current active)).IsLocallyBounded
      (roundsProtocol (2 ^ ρ)
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ) n).roles
      (roundsSchedule (2 ^ ρ) point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ ↦ interpolationProtocol tail ρ)
        (fun χ _ ↦ ⟨PUnit.unit, fun children ↦ interpolationSchedule ρ χ children tail next ρ []⟩)
        n χ current) := by
  induction n generalizing χ current active with
  | zero =>
    intro children
    exact interpolation_locally_bounded R q₀ μ m ρ leaves last χ children _ tail out next
      (by omega) hcover hout hbound ρ [] (by simp only [List.length_nil, Nat.zero_add])
  | succ n ih =>
    intro message
    constructor
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      exact normalized_round_badChallenge_le R q₀ μ m ρ n leaves last point χ lam current active message tail out hρ hc hχ
    · intro choice
      cases choice with
      | none => trivial
      | some r =>
        apply ih
        simp only [List.length_append, List.length_singleton]
        omega
/-- The layer descent assembles its combiner, cofactor, and child-coordinate local bounds. -/
theorem labels_locally_bounded {W : Type} (R : Riders W) (q₀ : W)
    (μ : ℕ) (leaves : W → Fin 3 → ℕ → E)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (next : RoundExtractor.ChallengeSchedule tail.tree tail.roles)
    (hcover : R.maxHeight ≤ μ)
    (hout : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ μ (leaves q) ∧
        ∀ i, rider R q i (c.point.take (R.height i)) = 0)
    (hbound : ∀ c good, c.point.length = μ →
      (Retained.extractor q₀ (out c good)).IsLocallyBounded tail.roles next)
    (steps : List ℕ) (m : ℕ) (c : Claim) (active : Bool)
    (hsteps : ∀ ρ ∈ steps, ρ = 1 ∨ ρ = 2)
    (hc : c.point.length = m) (hfinish : m + steps.sum = μ) :
    (Retained.extractor q₀ (labels R μ leaves tail out steps m c active)).IsLocallyBounded
      (protocol tail steps m).roles (challenges tail next steps m c) := by
  induction steps generalizing m c active with
  | nil =>
    have hm : m = μ := by simpa only [List.sum_nil, Nat.add_zero] using hfinish
    exact hbound c active (hc.trans hm)
  | cons ρ rest ih =>
    constructor
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      apply combiner_badChallenge_le R q₀ μ m ρ leaves rest c active tail out hc
      simp only [List.sum_cons] at hfinish
      omega
    · intro lam
      apply rounds_locally_bounded R q₀ μ m ρ leaves rest.isEmpty c.point lam
        (protocol tail rest (m + ρ))
        (fun next good ↦ labels R μ leaves tail out rest (m + ρ) next good)
        (challenges tail next rest (m + ρ))
        (hsteps ρ List.mem_cons_self) hc
      · intro hl
        have hr : rest = [] := List.isEmpty_iff.mp hl
        subst rest
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hfinish
        omega
      · intro next good q
        cases rest with
        | nil =>
          have hm : m + ρ = μ := by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using hfinish
          simp only [labels, List.isEmpty_nil, ↓reduceIte, hm]
          exact hout next good q
        | cons σ rest =>
          change layerRelation R μ (m + ρ) leaves next good q ↔ _
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, layerRelation]
          constructor
          · rintro ⟨ha, hf, hr, hc⟩
            exact ⟨ha, hf, hc, hr⟩
          · rintro ⟨ha, hf, hc, hr⟩
            exact ⟨ha, hf, hr, hc⟩
      · intro next good hn
        exact ih (m + ρ) next good (fun σ hσ ↦ hsteps σ (List.mem_cons_of_mem _ hσ)) hn
          (by simpa only [List.sum_cons, Nat.add_assoc] using hfinish)
      · simp only [List.length_nil, Nat.zero_add]


/-- The scheduled binary and radix-four contractions consume every leaf variable. -/
theorem layers_sum (μ : ℕ) : (layers μ).sum = μ := by
  have hdiv := Nat.mod_add_div μ 2
  have hmod := Nat.mod_lt μ (by decide : 0 < 2)
  unfold layers
  rw [List.sum_append, List.sum_replicate]
  split_ifs with h
  · simp only [List.sum_cons, List.sum_nil, add_zero, nsmul_eq_mul, Nat.cast_id]
    omega
  · simp only [List.sum_nil, zero_add, nsmul_eq_mul, Nat.cast_id]
    omega
/-- Every scheduled contraction has binary or radix-four arity. -/
theorem mem_layers (μ ρ : ℕ) (hρ : ρ ∈ layers μ) : ρ = 1 ∨ ρ = 2 := by
  unfold layers at hρ
  rcases List.mem_append.mp hρ with hρ | hρ
  · split_ifs at hρ
    · exact Or.inl (List.mem_singleton.mp hρ)
    · exact (List.not_mem_nil hρ).elim
  · exact Or.inr (List.mem_replicate.mp hρ).2
/-- The deepest tree level consists of its original leaves. -/
theorem level_full (μ : ℕ) (leaves : Fin 3 → ℕ → E) (s : Fin 3) (i : ℕ) :
    level μ μ leaves s i = leaves s i := by
  unfold level
  rw [Nat.sub_self]
  change (∏ j : Fin 1, leaves s (i * 1 + j.val)) = leaves s i
  rw [Fin.prod_univ_one]
  simp only [mul_one, Fin.val_zero, add_zero]


end CompStark.Multilinear.GrandProduct
