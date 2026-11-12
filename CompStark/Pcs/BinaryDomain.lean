/-
Adapted from Verified-zkEVM/leanerVM, LeanerVM/Protocol/NovelBasis.lean (Apache-2.0).
-/
module

public import CompStark.BinaryFields.Generator
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness
public import ArkLib.ProofSystem.Whir.Basic

/-! # The ordered flat basis and binary domain of leanVM's additive encoder. -/

@[expose] public section

open CompStark.BinaryFields Polynomial Module
namespace CompStark.Pcs

/-- The polynomial basis `1, g, ..., g^63` in its wire order. -/
def basis (i : Fin 64) : K := g ^ i.val

/-- The coordinates of a point of `K` in the `F_2`-basis `e_c`: the bits of its word. -/
private def bitsOf (x : K) : Fin 64 → ZMod 2 := fun c ↦ if x.toBitVec[c.val] then 1 else 0

/-- Bit coordinates turn base-field addition into binary-vector addition. -/
private theorem bitsOf_add (x y : K) : bitsOf (x + y) = bitsOf x + bitsOf y := by
  funext c
  have h : (x + y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl
  simp only [bitsOf, Pi.add_apply, h, BitVec.getElem_xor]
  cases x.toBitVec[c.val] <;> cases y.toBitVec[c.val] <;> decide

/-- Each polynomial-basis vector has its corresponding single bit set. -/
private theorem bitsOf_basis (c : Fin 64) : bitsOf (basis c) = Pi.single c 1 := by
  funext j
  have h : ∀ c j : Fin 64, (basis c).toBitVec[j.val] = decide (j = c) := by decide +kernel
  simp [bitsOf, h, Pi.single_apply]

/-- `e_0, ..., e_63` are linearly independent over `F_2` (so they are a basis of `K`, which has
`2 ^ 64` elements): the premise of CompPoly's additive NTT at `β = e`. Stated for any module
structure of `K` over `ZMod 2`, since the proof uses the module laws only. -/
theorem basis_linearIndependent [Module (ZMod 2) K] :
    LinearIndependent (ZMod 2) (fun c : Fin 64 ↦ basis c) := by
  let f : K →ₗ[ZMod 2] (Fin 64 → ZMod 2) :=
    { toFun := bitsOf
      map_add' := bitsOf_add
      map_smul' := fun c x ↦ by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl <;> (funext j; simp [bitsOf]) }
  refine LinearIndependent.of_comp f ?_
  convert (Pi.basisFun (ZMod 2) (Fin 64)).linearIndependent using 1
  funext c
  simp [f, bitsOf_basis]


/-- The normalized basis starts at one. -/
theorem basis_zero : basis 0 = 1 := pow_zero g

/-- The little-endian bits of a bounded numeric index. -/
def mask (n : ℕ) (x : Fin (2 ^ n)) : Whir.Cube n := fun i => x.val.testBit i.val

/-- Bounded numeric indices are determined by these bits. -/
theorem mask_injective (n : ℕ) : Function.Injective (mask n) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_eq_false_of_lt (y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- The numeric index whose little-endian bits are the supplied Boolean vertex. -/
def cubeIndex (n : ℕ) (u : Whir.Cube n) : Fin (2 ^ n) :=
  ((BitVec.ofBoolListLE (List.ofFn u)).cast (List.length_ofFn)).toFin

/-- Assemble little-endian bits without constructing intermediate bounded bitvectors. -/
def bitsIndex : List Bool → Nat
  | [] => 0
  | bit :: bits => bitsIndex bits * 2 + bit.toNat

/-- Natural-number assembly is exactly the bounded bitvector's numeric value. -/
theorem bitsIndex_eq (bits : List Bool) :
    bitsIndex bits = (BitVec.ofBoolListLE bits).toNat := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [bitsIndex, BitVec.ofBoolListLE, BitVec.toNat_concat, ih]

/-- Convert a Boolean vertex using only natural-number multiplication and addition. -/
def cubeIndexNat (n : Nat) (u : Whir.Cube n) : Fin (2 ^ n) :=
  ⟨bitsIndex (List.ofFn u), by
    rw [bitsIndex_eq]
    simpa only [List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn u)).isLt⟩

/-- The direct numeric conversion preserves every Boolean coordinate index. -/
@[csimp] theorem cubeIndex_code : cubeIndex = cubeIndexNat := by
  funext n u
  apply Fin.ext
  change _ = bitsIndex (List.ofFn u)
  rw [bitsIndex_eq]
  rfl

/-- Appended high bits contribute after the complete low-bit prefix. -/
theorem bitsIndex_append (xs ys : List Bool) :
    bitsIndex (xs ++ ys) = bitsIndex xs + 2^xs.length * bitsIndex ys := by
  induction xs with
  | nil => simp only [List.nil_append, bitsIndex, List.length_nil, pow_zero, one_mul, zero_add]
  | cons bit xs ih =>
    simp only [List.cons_append, bitsIndex, List.length_cons, pow_succ, ih]
    ring
/-- Decode a Boolean prefix from high to low without allocating a list. -/
def cubeIndexLoop {n : Nat} (u : Whir.Cube n) : (count : Nat) → count ≤ n → Nat → Nat
  | 0, _, acc => acc
  | count+1, h, acc => cubeIndexLoop u count (by omega)
      (2*acc + (u ⟨count,by omega⟩).toNat)
/-- Direct decoding preserves the ordered bit prefix and incoming high bits. -/
theorem cubeIndexLoop_eq {n : Nat} (u : Whir.Cube n) (count : Nat) (h : count ≤ n) (acc : Nat) :
    cubeIndexLoop u count h acc =
      bitsIndex (List.ofFn fun i : Fin count => u ⟨i.val,by omega⟩) + 2^count*acc := by
  induction count generalizing acc with
  | zero => simp only [cubeIndexLoop, List.ofFn_zero, bitsIndex, pow_zero, one_mul, zero_add]
  | succ count ih =>
    rw [cubeIndexLoop.eq_2, ih, List.ofFn_succ_last, bitsIndex_append]
    simp only [List.length_ofFn, bitsIndex, Fin.val_castSucc, Fin.val_last, pow_succ]
    ring
/-- Assemble a complete bounded numeric index by direct coordinate callbacks. -/
def cubeIndexDirect (n : Nat) (u : Whir.Cube n) : Fin (2^n) :=
  ⟨cubeIndexLoop u n (by omega) 0, by
    simpa only [cubeIndexLoop_eq, mul_zero, add_zero, Fin.eta, cubeIndexNat] using (cubeIndexNat n u).isLt⟩
/-- Direct numeric assembly has the original little-endian index on every vertex. -/
@[csimp] theorem cubeIndexNat_direct : cubeIndexNat = cubeIndexDirect := by
  funext n u
  apply Fin.ext
  simp only [cubeIndexNat, cubeIndexDirect, cubeIndexLoop_eq, mul_zero, add_zero, Fin.eta]

/-- Reading the constructed numeric index returns each supplied bit. -/
theorem mask_cubeIndex (n : ℕ) (u : Whir.Cube n) : mask n (cubeIndex n u) = u := by
  funext i
  change (((BitVec.ofBoolListLE (List.ofFn u)).cast (List.length_ofFn)).getLsbD i.val) = u i
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

/-- Numeric masks enumerate every Boolean vertex once, with an explicit inverse. -/
def cubeEquiv (n : ℕ) : Fin (2 ^ n) ≃ Whir.Cube n where
  toFun := mask n
  invFun := cubeIndex n
  left_inv x := mask_injective n (mask_cubeIndex n (mask n x))
  right_inv := mask_cubeIndex n

/-- The forward cube equivalence reads the numeric index's little-endian bits. -/
@[simp] theorem cubeEquiv_apply (n : ℕ) (x : Fin (2 ^ n)) : cubeEquiv n x = mask n x := rfl

/-- The additive-domain point selected by the bits of a column index. -/
def domainValue {dim : ℕ} (h : dim ≤ 64) (x : Fin (2 ^ dim)) : K :=
  ∑ i : Fin dim, if x.val.testBit i.val then basis (Fin.castLE h i) else 0

/-- The binary algebra structure on K, used by CompPoly's basis construction. -/
noncomputable instance : Algebra (ZMod 2) K := (ZMod.castHom (by decide) K).toAlgebra

/-- The basis independence premise of the generic CompPoly encoder. -/
instance : Fact (LinearIndependent (ZMod 2) basis) := ⟨basis_linearIndependent⟩

/-- The first basis vector has the normalization required by CompPoly. -/
instance : Fact (basis 0 = 1) := ⟨basis_zero⟩

/-- The binary scalar field has two elements. -/
instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩

/-- The binary scalar characteristic is prime. -/
instance : Fact (Nat.Prime (ringChar (ZMod 2))) := ⟨by rw [ZMod.ringChar_zmod_n]; exact Nat.prime_two⟩

/-- Every binary scalar is zero or one. -/
theorem binary_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- The linear combination map for a prefix of the flat basis. -/
noncomputable def spanMap {dim : ℕ} (h : dim ≤ 64) : (Fin dim → ZMod 2) →ₗ[ZMod 2] K where
  toFun c := ∑ i, c i • basis (Fin.castLE h i)
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]

/-- Numeric domain points are exactly binary linear combinations of the basis prefix. -/
theorem range_domainValue {dim : ℕ} (h : dim ≤ 64) :
    Set.range (domainValue h) = Set.range (spanMap h) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun i => if a.val.testBit i.val then 1 else 0, ?_⟩
    simp only [spanMap, LinearMap.coe_mk, AddHom.coe_mk, domainValue]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [one_smul, zero_smul]
  · rintro ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (cubeEquiv dim).surjective (fun i => decide (c i = 1))
    refine ⟨a, ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    have hi : a.val.testBit i.val = decide (c i = 1) := congrFun ha i
    rcases binary_cases (c i) with hc | hc <;> simp only [hi, hc, zero_ne_one,
      decide_false, Bool.false_eq_true, ↓reduceIte, zero_smul, decide_true, one_smul]

/-- The domain is injective even when its dimension is exactly 64. -/
theorem domainValue_injective {dim : ℕ} (h : dim ≤ 64) : Function.Injective (domainValue h) := by
  intro x y hxy
  have li := basis_linearIndependent.comp (Fin.castLE h) (Fin.castLE_injective h)
  let c (x : Fin (2 ^ dim)) (i : Fin dim) : ZMod 2 := if x.val.testBit i.val then 1 else 0
  have hc : ∀ i, c x i - c y i = 0 := by
    apply Fintype.linearIndependent_iff.mp li
    have hs : ∀ a, domainValue h a = ∑ i, c a i • basis (Fin.castLE h i) := by
      intro a
      apply Finset.sum_congr rfl
      intro i _
      simp only [c]; split_ifs <;> simp only [one_smul, zero_smul]
    rw [hs x, hs y] at hxy
    simpa only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero, Function.comp_apply] using hxy
  apply mask_injective dim
  funext i
  have hi := sub_eq_zero.mp (hc i)
  dsimp only [c] at hi
  cases hx : x.val.testBit i.val <;> cases hy : y.val.testBit i.val <;>
    simp only [mask, hx, hy, Bool.false_eq_true, ↓reduceIte, zero_ne_one, one_ne_zero] at hi ⊢

/-- The exact ordered additive domain for all dimensions at most 64. -/
def domain {dim : ℕ} (h : dim ≤ 64) : Fin (2 ^ dim) ↪ K :=
  ⟨domainValue h, domainValue_injective h⟩

/-- The domain image is an additive subgroup, including the full-field boundary. -/
theorem domain_additive {dim : ℕ} (h : dim ≤ 64) :
    ∃ S : AddSubgroup K, Set.range (domain h) = (S : Set K) :=
  ⟨(spanMap h).range.toAddSubgroup, range_domainValue h⟩

/-- A flat basis vector is its single polynomial-basis bit word. -/
def basisWord (i : Fin 64) : K := K.ofBits (2^i.val)

/-- Native domain evaluation reads each basis bit without field exponentiation. -/
@[csimp] theorem basis_word : basis = basisWord := by
  have certificate : ∀ i : Fin 64, basis i = basisWord i := by decide +kernel
  exact funext certificate

end CompStark.Pcs
