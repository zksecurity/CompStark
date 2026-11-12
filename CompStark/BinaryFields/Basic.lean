/-
Copyright (c) 2026 zkSecurity.
Adapted from leanerVM (Apache-2.0).
  CompStark.BinaryFields.Basic

  The leanVM fields `K = GF(2^64)` and `E = GF(2^192)` as CompPoly's computable carriers, and
  the limb view of `E`.
-/

module

public import CompPoly.Fields.Binary.BF64
import Mathlib.Tactic.LinearCombination

/-!
# Binary fields and limb coordinates

The carriers are CompPoly’s `BF64` and `BF64.Ext3`, with polynomial bases modulo
`x^64 + x^4 + x^3 + x + 1` and `y^3 + y + 1`. Wire bits and limbs follow §2 of the VM specification.
-/

namespace CompStark.BinaryFields

@[expose] public section

open CompPoly.Extension

/-! ## The fields -/

/-- `K = GF(2^64)`, CompPoly's `BF64`: a wrapper of `BitVec 64` with bit `i` the
coefficient of `x^i`. -/
abbrev K : Type := BF64

/-- Decode a polynomial-basis word, reducing its integer representation modulo `2^64`.
This is a wire encoding, distinct from the characteristic-two natural-number cast. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- Decide equality through bit coordinates, keeping kernel comparisons of computed words
free of the dependent transport introduced by the upstream derived instance. -/
instance instDecidableEqK : DecidableEq K := fun a b ↦
  decidable_of_iff (a.toBitVec = b.toBitVec) BF64.toBitVec_injective.eq_iff

/-- A proof-only enumeration of `K`; executable code uses its explicit bit coordinates. -/
noncomputable instance : Fintype K := Fintype.ofFinite K

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`: a `Vector K 3` in limb order
`c0 + c1·y + c2·y²`. -/
abbrev E : Type := BF64.Ext3

/-- The adjoined root `y` of `y^3 + y + 1`. -/
def y : E := BF64.ext3Gen

/-- The defining relation of `E`: `y^3 = y + 1`. -/
theorem y_pow_three : y ^ 3 = y + 1 := BF64.ext3Gen_pow_three

/-! ## Limbs -/

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 3) : K := Ext.coeff x i

/-- The word `c0 + c1·y + c2·y²`, as the literal limb vector. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]

/-- A word lies in `K`: its `y` and `y²` limbs are zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0 ∧ x.limb 2 = 0

/-- A canonical 128-bit word: its `y²` limb is zero. -/
def IsCanonical128 (x : E) : Prop := x.limb 2 = 0

/-- The two-limb cell `c0 + c1·y`, with zero top limb. -/
def E.ofCell (v : Vector K 2) : E := E.ofLimbs v[0] v[1] 0

deriving instance Decidable for IsInK, IsCanonical128

/-- Hexadecimal rendering `E(0x<c2><c1><c0>)`, highest limb first. -/
instance : ToString E :=
  ⟨fun x ↦
    let hi := (x.limb 2).toBitVec.toHex
    let mid := (x.limb 1).toBitVec.toHex
    let lo := (x.limb 0).toBitVec.toHex
    s!"E(0x{hi}{mid}{lo})"⟩

/-! ## Load-bearing lemmas -/

/-- Words with the same limbs are equal. -/
theorem E.ext {x z : E} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

/-- The limbs of `E.ofLimbs c0 c1 c2` are `c0, c1, c2`. -/
@[simp] theorem limb_ofLimbs (c0 c1 c2 : K) (i : Fin 3) :
    (E.ofLimbs c0 c1 c2).limb i = ![c0, c1, c2] i := by
  fin_cases i <;> rfl

/-- `ofK a` has `a` in limb `0` and zero elsewhere. -/
@[simp] theorem limb_ofK (a : K) (i : Fin 3) :
    (ofK a).limb i = if (i : ℕ) = 0 then a else 0 :=
  Ext.coeff_ofBase (P := BF64.ext3Params) a i

/-- `ofK` is injective. -/
theorem ofK_injective : Function.Injective ofK := by
  intro a b h
  simpa using congrArg (fun z : E ↦ z.limb 0) h

/-- Every word is its limbs in the basis `1, y, y²`. -/
theorem E.eq_sum_limbs (x : E) :
    x = ofK (x.limb 0) + ofK (x.limb 1) * y + ofK (x.limb 2) * y ^ 2 := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 3,
      algebraMap K (AdjoinRoot BF64.ext3Params.poly) (x.limb i) *
        Ext.rt BF64.ext3Params ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_three]
  simp [y]

/-- `E.ofLimbs c0 c1 c2 = c0 + c1·y + c2·y²`. -/
theorem ofLimbs_eq (c0 c1 c2 : K) :
    E.ofLimbs c0 c1 c2 = ofK c0 + ofK c1 * y + ofK c2 * y ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs (E.ofLimbs c0 c1 c2)]
  simp

/-- Rebuilding a word from its limbs is the identity. -/
theorem ofLimbs_limb (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) = x :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- `IsInK` is exactly the image of `ofK`. -/
theorem isInK_iff (x : E) : IsInK x ↔ ∃ a, x = ofK a := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x.limb 0, E.ext fun i ↦ by fin_cases i <;> simp [h1, h2]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨by simp, by simp⟩

/-- Limb `i` of a sum is the sum of the limbs (CompPoly's `Ext.coeff_add`). -/
theorem limb_add (x z : E) (i : Fin 3) : (x + z).limb i = x.limb i + z.limb i :=
  Ext.coeff_add x z i

/-- Limb `i` of the zero word is zero. -/
theorem limb_zero (i : Fin 3) : (0 : E).limb i = 0 :=
  Ext.coeff_zero (P := BF64.ext3Params) i

/-- `ofK` preserves sums: it is `algebraMap K E`. -/
theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- `ofK` preserves products: it is `algebraMap K E`. -/
theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- `ofK a` is the word with limbs `(a, 0, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

/-- A word in `K` is its low limb with zeros above. -/
theorem ofLimbs_of_isInK {x : E} (h : IsInK x) : E.ofLimbs (x.limb 0) 0 0 = x :=
  calc E.ofLimbs (x.limb 0) 0 0 = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) := by rw [h.1, h.2]
    _ = x := ofLimbs_limb x

/-- A single-limb word is zero exactly when its limb is. -/
theorem ofLimbs_eq_zero_iff (c : K) : E.ofLimbs c 0 0 = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simpa only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero] using this
  · rintro rfl
    exact E.ext fun i ↦ by rw [limb_zero]; fin_cases i <;> simp

/-- The sum of two words, limb by limb: addition in `E` is bitwise `XOR` in each limb, never
integer addition with carries (the `XOR` table's result coordinates, specification §7.1). -/
theorem add_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 + E.ofLimbs b0 b1 b2 = E.ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) :=
  E.ext fun i ↦ by rw [limb_add]; fin_cases i <;> simp

/-- Multiplication in the three-limb basis, reduced by `y^3 = y + 1`. -/
theorem mul_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 * E.ofLimbs b0 b1 b2 =
      E.ofLimbs (a0 * b0 + a1 * b2 + a2 * b1)
        (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y² + p₃·y³ + p₄·y⁴`; `y³ = y + 1` folds `p₃` and `p₄`.
  linear_combination (ofK a1 * ofK b2 + ofK a2 * ofK b1 + ofK a2 * ofK b2 * y) * y_pow_three

end
end CompStark.BinaryFields
