/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.FriFold
public import CompStark.Fs.StarkAccept
public import CompStark.Merkle.Extract

/-! # FRI's committed words, extracted

`Binding`: every accepted opening against a commitment opens the rows extracted from a cache
(`leafRow`), and `CapBinding` the same for every entry of a cap; an accepted opening against a
binding cap opens the extracted rows (`extractCapRow_of_verifyCapH`). Commitment `i`'s leaf `r`
holds the group of `2 ^ arity` values of word `i` at the indices `r 2 ^ arity + k` in bit-reversed
order (`friWordAt`, `friWordAt_group`), so an accepted fold's commitment holds the running value at
the query's index (`friWordAt_eval`). The final polynomial is the proof's, substituted to the
coset (`finalPoly`, `eval_finalPoly`).
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.Sound Polynomial Fri.Spec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Extraction -/

section Extract
variable (cache : Merkle.Cache F (Digest F))

/-- Accepted openings against `root` of matrices of one height open the rows extracted from
`cache`. -/
def Binding (H : Primitives F Id) (root : Digest F) : Prop :=
  ∀ (n k i : Nat) (values : List (List F)) (path : List (Digest F)), 0 < n →
    verifyBatchH H root (List.replicate n (2 ^ k)) i values path = true →
      Merkle.extractRow cache k i root = some values.flatten

/-- Accepted openings against every entry of the cap `cap` bind, and so do those against the
zero digest, which an index past the cap reads. -/
def CapBinding (H : Primitives F Id) (cap : Cap F) : Prop :=
  ∀ j, Binding cache H (cap.toList.getD j 0)

/-- The row extracted at leaf `i` of the depth-`k` tree under the cap `cap` of height `h`, empty
if there is none. -/
noncomputable def leafRow (k h i : Nat) (cap : Cap F) : List F :=
  (Merkle.extractCapRow cache k h i cap.toList).getD []

/-- An accepted opening against a binding cap opens the extracted rows. -/
theorem extractCapRow_of_verifyCapH (H : Primitives F Id) (cap : Cap F)
    (hbind : CapBinding cache H cap) (h n k index : Nat) (values : List (List F))
    (path : List (Digest F)) (hn : 0 < n) (hv : verifyCapH H cap h n k index values path = true) :
    Merkle.extractCapRow cache k h index cap.toList = some values.flatten :=
  hbind _ n _ _ values path hn hv

/-- The value at index `z` of a FRI word of size `2 ^ m` folded by `2 ^ a`, committed under the
cap `cap` of height `h`: entry `rev z % 2 ^ a` of leaf `rev z >>> a`. -/
noncomputable def friWordAt (cap : Cap F) (h m a z : Nat) : 𝕂 :=
  Challenge.toSpec ((unflatten (leafRow cache (m - a) h (reverseBits z m >>> a) cap)).getD
    (reverseBits z m % 2 ^ a) 0)

end Extract

section Final
variable {lookups : List (Lookup F)} (T : Iop.Setup EF lookups)

/-- `log₂ |L|`. -/
abbrev _root_.CompStark.Iop.Setup.logSize : Nat := T.logN + T.params.logBlowup

/-- The shift of the final polynomial's domain: `g ^ 2 ^ (logN - logFinalPolyLen)`. -/
noncomputable def _root_.CompStark.Iop.Setup.finalShift : 𝕂 :=
  lift gen ^ 2 ^ (T.logN - T.params.logFinalPolyLen)

/-- The final polynomial on the coset: `∑ᵢ cᵢ (X / s) ^ i`, `s` the final domain's shift. -/
noncomputable def finalPoly (coeffs : Array EF) : 𝕂[X] :=
  ∑ i ∈ Finset.range coeffs.size,
    Polynomial.C (Challenge.toSpec (coeffs.getD i 0) * (T.finalShift)⁻¹ ^ i) * Polynomial.X ^ i

/-! ### The final polynomial -/

/-- The extracted final polynomial at the final domain's point of index `rev I` is Plonky3's
final polynomial at the subgroup's point. -/
theorem eval_finalPoly (coeffs : Array EF) (I : Nat)
    (hI : I < 2 ^ (T.params.logBlowup + T.params.logFinalPolyLen)) :
    (finalPoly T coeffs).eval (lift gen ^ 2 ^ (T.logN - T.params.logFinalPolyLen) *
        lift (twoAdicGen (T.params.logBlowup + T.params.logFinalPolyLen) ^
          reverseBits I (T.params.logBlowup + T.params.logFinalPolyLen))) =
      Challenge.toSpec (coeffs.foldr (fun c acc ↦
        acc * Ext.ofBase (powF (twoAdicGen T.logSize) (reverseBits I T.logSize)) + c) 0) := by
  set L := T.params.logBlowup + T.params.logFinalPolyLen
  have hn : T.logSize = (T.logN - T.params.logFinalPolyLen) + L := by
    have := T.valid.finalPolyFits; unfold Iop.Setup.logSize; omega
  have hpt : Challenge.toSpec (Ext.ofBase (powF (twoAdicGen T.logSize) (reverseBits I T.logSize)) :
      EF) = lift (twoAdicGen L ^ reverseBits I L) := by
    rw [Challenge.toSpec_ofBase', ← lift, powF_eq, hn, reverseBits_low L _ I hI,
      pow_mul, Nat.add_comm _ L,
      BaseField.twoAdicGen_pow (F := F) L _
        (by have := T.valid.twoAdic; have := T.valid.finalPolyFits; omega)]
  rw [← Array.foldr_toList, toSpec_horner_list, Array.length_toList, hpt, finalPoly,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Iop.Setup.finalShift, Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, Array.getElem?_toList, mul_assoc, ← mul_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ lift_gen_ne_zero), one_mul]

end Final

variable (S : Iop.Setup EF) [S.Folds]

/-! ### A fold's opened group is the extracted word -/

theorem groupOf_getD (s : QueryFold EF) (index : Nat) (eval : EF) (k : Nat)
    (hk : k < 2 ^ s.logArity) :
    (groupOf s index eval).getD k 0 =
      if k < index % 2 ^ s.logArity then s.siblings.getD k 0
      else if k = index % 2 ^ s.logArity then eval else s.siblings.getD (k - 1) 0 := by
  rw [groupOf, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

theorem groupOf_pos (s : QueryFold EF) (index : Nat) (eval : EF) :
    (groupOf s index eval).getD (index % 2 ^ s.logArity) 0 = eval := by
  rw [groupOf_getD s index eval _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [lt_irrefl, ↓reduceIte]

theorem length_groupOf (s : QueryFold EF) (index : Nat) (eval : EF) :
    (groupOf s index eval).length = 2 ^ s.logArity := by
  rw [groupOf, List.length_map, List.length_range]

/-- **An accepted fold opens the extracted word.** If fold `x` passes its checks at index `I` of
height `2 ^ m` and its commitment binds, the extracted word holds the opened group around `I`. -/
theorem friWordAt_group (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (h : Nat)
    (commit : Cap F) (x : EF × QueryFold EF) (e : EF) (I m : Nat) (hI : I < 2 ^ m)
    (ha : x.2.logArity ≤ m) (hok : StepOk H h commit x (e, I, m))
    (hbind : CapBinding cache H commit) (k : Nat) (hk : k < 2 ^ x.2.logArity) :
    friWordAt cache commit h m x.2.logArity
        (reverseBits ((I >>> x.2.logArity) * 2 ^ x.2.logArity + k) m) =
      Challenge.toSpec ((groupOf x.2 I e).getD k 0) := by
  set a := x.2.logArity
  have hshift : I >>> a < 2 ^ (m - a) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' ha]; exact hI)
  have hlt : (I >>> a) * 2 ^ a + k < 2 ^ m := by
    have : (I >>> a + 1) * 2 ^ a ≤ 2 ^ (m - a) * 2 ^ a := Nat.mul_le_mul_right _ hshift
    rw [← pow_add, Nat.sub_add_cancel ha, Nat.succ_mul] at this
    omega
  obtain ⟨path, hpath⟩ := hok.2.2
  have hrow := extractCapRow_of_verifyCapH cache H commit hbind h 1 (m - a) (I >>> a) _ _
    Nat.one_pos hpath
  have hdiv : ((I >>> a) * 2 ^ a + k) >>> a = I >>> a := by
    rw [Nat.shiftRight_eq_div_pow ((I >>> a) * 2 ^ a + k), Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hk, Nat.zero_add]
  have hmod : ((I >>> a) * 2 ^ a + k) % 2 ^ a = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  unfold friWordAt leafRow
  rw [reverseBits_reverseBits hlt, hdiv, hmod, hrow]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Option.getD_some,
    unflatten_flatMap]

theorem shiftRight_mul_add_mod (I a : Nat) : (I >>> a) * 2 ^ a + I % 2 ^ a = I := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]; exact Nat.div_add_mod I (2 ^ a)

theorem finMod_val {m r : Nat} (hr : r < 2 ^ m) : (finMod m r).val = r := Nat.mod_eq_of_lt hr

/-- An accepted fold's commitment holds the running value at the query's index. -/
theorem friWordAt_eval (cache : Merkle.Cache F (Digest F)) (H : Primitives F Id) (h : Nat)
    (commit : Cap F) (x : EF × QueryFold EF) (st : EF × Nat × Nat) (m : Nat) (hm : st.2.2 = m)
    (hI : st.2.1 < 2 ^ m) (ha : x.2.logArity ≤ m) (hok : StepOk H h commit x st)
    (hbind : CapBinding cache H commit) :
    friWordAt cache commit h m x.2.logArity (reverseBits st.2.1 m) = Challenge.toSpec st.1 := by
  obtain ⟨e, I, m'⟩ := st
  dsimp only at hm hI ⊢
  subst hm
  have hg := friWordAt_group cache H h commit x e I m' hI ha hok hbind (I % 2 ^ x.2.logArity)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  rwa [shiftRight_mul_add_mod, groupOf_pos] at hg

end CompStark.Fs
