/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Packed
public import CompStark.Keccak.Embedding
public import CompPoly.Fields.Binary.BF64.MaskedProducts
/-! Certified byte-pair products for the sixteen-bit binary RMFE inputs. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
/-- Materialize a scalar coordinate function in a bounded machine-indexed buffer. -/
def fixedWordsOfFn (n : Nat) (hn : n < 2^29) (f : Fin n → UInt64) : FixedWords n :=
  let b := Packed.ofFn n (fun i => ⟨f i⟩)
  ⟨b.val.bytes, by rw [b.val.byteSize, b.property]; exact ⟨rfl,hn⟩⟩
/-- Machine-indexed reads of a materialized scalar buffer recover the defining function. -/
theorem getUWord_fixedWordsOfFn (n : Nat) (hn : n < 2^29) (f : Fin n → UInt64)
    (i : USize) (hi : i < n.toUSize) :
    getUWord (fixedWordsOfFn n hn f) i hi = f ⟨i.toNat, by
      have hn' : n < USize.size := lt_of_lt_of_le (lt_trans hn (by decide)) USize.le_size
      simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn'] using hi⟩ := by
  let a := fixedWordsOfFn n hn f
  have hn' : n < USize.size := lt_of_lt_of_le (lt_trans hn (by decide)) USize.le_size
  have hi' : i.toNat < n := by
    simpa only [USize.lt_iff_toNat_lt, Nat.toUSize, USize.toNat_ofNat_of_lt' hn'] using hi
  have h := congrArg Word.val (Packed.read_ofFn n (fun j => ⟨f j⟩) ⟨i.toNat,hi'⟩)
  change (a.val.ugetUInt32LE (8*i) _).toUInt64 |||
    ((a.val.ugetUInt32LE (8*i+4) _).toUInt64 <<< 32) = _
  simp only [ByteArray.ugetUInt32LE, (wordOffsets a i hi).1, (wordOffsets a i hi).2]
  exact h

/-- Materialized certified binary embedding columns. -/
def embeddingColumns : Array Nat := Array.ofFn CompStark.Keccak.Embedding.embeddingWords
/-- A byte's first coefficient columns in a binary linear embedding. -/
def embeddingPart (shift : Nat) (a : UInt8) : Nat → UInt64
  | 0 => 0
  | n+1 => embeddingPart shift a n ^^^
      (if a.toNat.testBit n then embeddingColumns[shift+n]!.toUInt64 else 0)
/-- The full byte contribution at an eight-column offset. -/
def embeddingByte (shift : Nat) (a : UInt8) : UInt64 := embeddingPart shift a 8
/-- Evaluate the linear binary embedding on the low sixteen input bits. -/
def embeddingRaw (a : UInt64) : UInt64 :=
  embeddingByte 0 a.toUInt8 ^^^ embeddingByte 8 (a >>> 8).toUInt8
/-- Exchange the middle operands in four packed XOR summands. -/
theorem xor_shuffle (a b c d : UInt64) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;>
    cases c.toBitVec.getLsbD i <;> cases d.toBitVec.getLsbD i <;> rfl
/-- Each byte contribution commutes with XOR addition. -/
theorem embeddingPart_xor (shift : Nat) (a b : UInt8) (n : Nat) :
    embeddingPart shift (a ^^^ b) n = embeddingPart shift a n ^^^ embeddingPart shift b n := by
  induction n with
  | zero => simp only [embeddingPart, UInt64.xor_self]
  | succ n ih =>
    simp only [embeddingPart, ih, UInt8.toNat_xor, Nat.testBit_xor]
    rw [xor_shuffle]
    cases a.toNat.testBit n <;> cases b.toNat.testBit n <;>
      simp
/-- The sixteen-bit raw embedding is a binary linear map. -/
theorem embeddingRaw_xor (a b : UInt64) :
    embeddingRaw (a ^^^ b) = embeddingRaw a ^^^ embeddingRaw b := by
  simp only [embeddingRaw, embeddingByte, UInt64.toUInt8_xor,
    UInt64.shiftRight_xor, embeddingPart_xor]
  exact xor_shuffle _ _ _ _
/-- Carry-less multiplication of two degree-at-most-23 binary polynomials. -/
@[inline] def binaryProduct (a b : UInt64) : UInt64 := Word.clMul32 a b
/-- The word product is the full binary polynomial product of its low limbs. -/
theorem binaryProduct_poly (a b : UInt64) : BinaryField.toPoly (binaryProduct a b).toBitVec = BinaryField.toPoly (a.toBitVec.setWidth 32) * BinaryField.toPoly (b.toBitVec.setWidth 32) := Word.clMul32_poly a b
/-- Binary polynomial coordinates determine their packed word uniquely. -/
theorem wordPolynomial_injective {a b : UInt64}
    (h : BinaryField.toPoly a.toBitVec = BinaryField.toPoly b.toBitVec) : a = b := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc := congrArg (fun p => Polynomial.coeff p i) h
  simp only [BinaryField.toPoly_coeff, hi, dite_true] at hc
  change (if a.toBitVec.getLsbD i then (1 : ZMod 2) else 0) = (if b.toBitVec.getLsbD i then 1 else 0) at hc
  cases ha : a.toBitVec.getLsbD i <;> cases hb : b.toBitVec.getLsbD i <;>
    simp_all
/-- Binary multiplication is additive in its first packed operand. -/
theorem binaryProduct_xor_left (a b c : UInt64) :
    binaryProduct (a ^^^ b) c = binaryProduct a c ^^^ binaryProduct b c := by
  apply wordPolynomial_injective
  simp only [binaryProduct_poly, UInt64.toBitVec_xor, BinaryField.toPoly_xor,
    BitVec.setWidth_xor, add_mul]
/-- Binary multiplication is additive in its second packed operand. -/
theorem binaryProduct_xor_right (a b c : UInt64) :
    binaryProduct a (b ^^^ c) = binaryProduct a b ^^^ binaryProduct a c := by
  apply wordPolynomial_injective
  simp only [binaryProduct_poly, UInt64.toBitVec_xor, BinaryField.toPoly_xor,
    BitVec.setWidth_xor, mul_add]
/-- Packed binary polynomial multiplication is commutative. -/
theorem binaryProduct_comm (a b : UInt64) : binaryProduct a b = binaryProduct b a := by
  apply wordPolynomial_injective
  rw [binaryProduct_poly, binaryProduct_poly, mul_comm]

/-- Prepared low and high embedding bytes. -/
def embeddingBytes (shift : Nat) : Array UInt64 :=
  Array.ofFn fun a : Fin 256 => embeddingByte shift a.val.toUInt8
/-- Every cached byte is the specified binary linear combination. -/
theorem embeddingBytes_get (shift : Nat) (a : UInt8) :
    (embeddingBytes shift)[a.toNat]! = embeddingByte shift a := by
  rw [getElem!_pos _ _ (by simpa only [embeddingBytes, Array.size_ofFn] using a.toNat_lt)]
  simp only [embeddingBytes, Array.getElem_ofFn, Nat.toUInt8, UInt8.ofNat_toNat]
/-- Packed byte-pair products and the affine all-ones contribution. -/
structure RmfeProducts where
  /-- Low/low, low/high and high/high binary products. -/
  pairs : FixedWords (3*65536)
  /-- The product with the embedding of sixteen ones. -/
  linear : FixedWords 65536
/-- Cache all byte pairs and the all-ones linear map once. -/
def prepareRmfeProducts : RmfeProducts :=
  let lo := embeddingBytes 0
  let hi := embeddingBytes 8
  let ones := lo[255]! ^^^ hi[255]!
  ⟨fixedWordsOfFn (3*65536) (by decide) (fun i =>
    let a := i.val%256
    let b := i.val%65536/256
    let x := if i.val < 131072 then lo[a]! else hi[a]!
    let y := if i.val < 65536 then lo[b]! else hi[b]!
    binaryProduct x y),
   fixedWordsOfFn 65536 (by decide) (fun i =>
    binaryProduct ones (lo[i.val%256]! ^^^ hi[i.val/256]!))⟩
/-- Machine index of one byte pair in one of the three product tables. -/
@[inline] def bytePairIndex (block : Fin 3) (a b : UInt8) : USize :=
  (65536*block.val).toUSize+a.toUSize+256*b.toUSize
/-- Byte-pair machine coordinates do not wrap on either target width. -/
theorem bytePairIndex_toNat (block : Fin 3) (a b : UInt8) :
    (bytePairIndex block a b).toNat = 65536*block.val+a.toNat+256*b.toNat := by
  have hb := block.isLt
  have ha := a.toNat_lt
  have hc := b.toNat_lt
  have hs := USize.le_size
  simp only [bytePairIndex, USize.toNat_add, USize.toNat_mul, UInt8.toNat_toUSize]
  have hn : (65536*block.val).toUSize.toNat = 65536*block.val := by
    rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]
  have h256 : (256 : USize).toNat = 256 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [hn,h256]
  change ((65536*block.val+a.toNat)%USize.size+(256*b.toNat)%USize.size)%USize.size = _
  have h1 : 65536*block.val+a.toNat < USize.size := by omega
  have h2 : 256*b.toNat < USize.size := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  exact Nat.mod_eq_of_lt (by omega)
/-- Every byte pair indexes the packed product buffer. -/
theorem bytePairIndex_bound (block : Fin 3) (a b : UInt8) :
    bytePairIndex block a b < (3*65536).toUSize := by
  have hn : (3*65536).toUSize.toNat = 196608 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.lt_iff_toNat_lt, bytePairIndex_toNat, hn]
  have := block.isLt
  have := a.toNat_lt
  have := b.toNat_lt
  omega
/-- One prepared pair lookup is exactly the corresponding product of byte embeddings. -/
theorem prepareRmfeProducts_pair (block : Fin 3) (a b : UInt8) :
    readUWord prepareRmfeProducts.pairs (bytePairIndex block a b) =
      binaryProduct (embeddingByte (if block.val < 2 then 0 else 8) a)
        (embeddingByte (if block.val = 0 then 0 else 8) b) := by
  rw [readUWord, dite_eq_left (bytePairIndex_bound block a b)]
  rw [prepareRmfeProducts, getUWord_fixedWordsOfFn]
  simp only [bytePairIndex_toNat]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hmod : (65536*block.val+a.toNat+256*b.toNat)%256 = a.toNat := by omega
  have hdiv : (65536*block.val+a.toNat+256*b.toNat)%65536/256 = b.toNat := by omega
  rw [hmod,hdiv]
  fin_cases block <;> simp_all [embeddingBytes_get] <;> split_ifs <;> first | rfl | omega
/-- The low/low machine index has a literal zero table offset. -/
theorem bytePairIndex_zero (a b : UInt8) :
    bytePairIndex 0 a b = a.toUSize+256*b.toUSize := by
  have hn : (0 : Nat).toUSize = (0 : USize) := by
    apply USize.toNat_inj.mp
    rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
    exact (USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)).symm
  change (0 : Nat).toUSize+a.toUSize+256*b.toUSize = _
  rw [hn,USize.zero_add]
/-- The mixed machine index has a literal one-table offset. -/
theorem bytePairIndex_one (a b : UInt8) :
    bytePairIndex 1 a b = 65536+a.toUSize+256*b.toUSize := by
  have hn : (65536 : Nat).toUSize = (65536 : USize) := by
    apply USize.toNat_inj.mp
    rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
    exact (USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)).symm
  change (65536 : Nat).toUSize+a.toUSize+256*b.toUSize = _
  rw [hn]
/-- The high/high machine index has a literal two-table offset. -/
theorem bytePairIndex_two (a b : UInt8) :
    bytePairIndex 2 a b = 131072+a.toUSize+256*b.toUSize := by
  have hn : (131072 : Nat).toUSize = (131072 : USize) := by
    apply USize.toNat_inj.mp
    rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
    exact (USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)).symm
  change (131072 : Nat).toUSize+a.toUSize+256*b.toUSize = _
  rw [hn]

/-- Four pair reads multiply the embeddings of two raw sixteen-bit assignments. -/
@[inline] def RmfeProducts.mul (maps : RmfeProducts) (a b : UInt64) : UInt64 :=
  let a0 := a.toUInt8
  let a1 := (a >>> 8).toUInt8
  let b0 := b.toUInt8
  let b1 := (b >>> 8).toUInt8
  getUWord maps.pairs (a0.toUSize+256*b0.toUSize) (by rw [←bytePairIndex_zero]; exact bytePairIndex_bound 0 a0 b0) ^^^
    getUWord maps.pairs (65536+a0.toUSize+256*b1.toUSize) (by rw [←bytePairIndex_one]; exact bytePairIndex_bound 1 a0 b1) ^^^
    getUWord maps.pairs (65536+b0.toUSize+256*a1.toUSize) (by rw [←bytePairIndex_one]; exact bytePairIndex_bound 1 b0 a1) ^^^
    getUWord maps.pairs (131072+a1.toUSize+256*b1.toUSize) (by rw [←bytePairIndex_two]; exact bytePairIndex_bound 2 a1 b1)
/-- The prepared byte-pair product equals the word binary polynomial product. -/
theorem prepareRmfeProducts_mul (a b : UInt64) :
    prepareRmfeProducts.mul a b = binaryProduct (embeddingRaw a) (embeddingRaw b) := by
  simp only [RmfeProducts.mul, getUWord_eq_readUWord, ←bytePairIndex_zero, ←bytePairIndex_one, ←bytePairIndex_two, prepareRmfeProducts_pair]
  change ((binaryProduct (embeddingByte 0 a.toUInt8) (embeddingByte 0 b.toUInt8) ^^^
    binaryProduct (embeddingByte 0 a.toUInt8) (embeddingByte 8 (b >>> 8).toUInt8)) ^^^
    binaryProduct (embeddingByte 0 b.toUInt8) (embeddingByte 8 (a >>> 8).toUInt8)) ^^^
    binaryProduct (embeddingByte 8 (a >>> 8).toUInt8) (embeddingByte 8 (b >>> 8).toUInt8) = _
  rw [binaryProduct_comm (embeddingByte 0 b.toUInt8) (embeddingByte 8 (a >>> 8).toUInt8)]
  simp only [embeddingRaw, binaryProduct_xor_left, binaryProduct_xor_right, UInt64.xor_assoc]
  apply congrArg (fun x => binaryProduct (embeddingByte 0 a.toUInt8) (embeddingByte 0 b.toUInt8) ^^^ x)
  simpa only [UInt64.zero_xor] using xor_shuffle 0
    (binaryProduct (embeddingByte 0 a.toUInt8) (embeddingByte 8 (b >>> 8).toUInt8))
    (binaryProduct (embeddingByte 8 (a >>> 8).toUInt8) (embeddingByte 0 b.toUInt8))
    (binaryProduct (embeddingByte 8 (a >>> 8).toUInt8) (embeddingByte 8 (b >>> 8).toUInt8))
/-- One lookup multiplies by the all-ones embedding. -/
@[inline] def RmfeProducts.ones (maps : RmfeProducts) (a : UInt64) : UInt64 :=
  readUWord maps.linear a.toUInt16.toUSize
/-- The prepared affine map is the exact all-ones word product. -/
theorem prepareRmfeProducts_ones (a : UInt64) :
    prepareRmfeProducts.ones a = binaryProduct (embeddingRaw 65535) (embeddingRaw a) := by
  have ha : a.toUInt16.toNat < 65536 := a.toUInt16.toNat_lt
  have hn : (65536 : Nat).toUSize.toNat = 65536 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  have hi : a.toUInt16.toUSize < (65536 : Nat).toUSize := by
    simpa only [USize.lt_iff_toNat_lt, UInt16.toNat_toUSize, hn] using ha
  rw [RmfeProducts.ones, readUWord, dite_eq_left hi, prepareRmfeProducts, getUWord_fixedWordsOfFn]
  simp only [UInt16.toNat_toUSize]
  have hl : a.toUInt16.toNat%256 = a.toUInt8.toNat := by
    simp only [UInt64.toNat_toUInt16, UInt64.toNat_toUInt8]
    omega
  have hh : a.toUInt16.toNat/256 = (a >>> 8).toUInt8.toNat := by
    simp only [UInt64.toNat_toUInt16, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    rw [Nat.shiftRight_eq_div_pow]
    change a.toNat%65536/256 = (a.toNat/256)%256
    omega
  rw [hl,hh,embeddingBytes_get,embeddingBytes_get]
  change binaryProduct ((embeddingBytes 0)[(255 : UInt8).toNat]! ^^^
    (embeddingBytes 8)[(255 : UInt8).toNat]!) _ = _
  rw [embeddingBytes_get,embeddingBytes_get]
  rfl
end CompStark.Keccak.GkrProver
