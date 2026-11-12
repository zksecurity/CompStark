/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Decoder
public import CompStark.Pcs.PackedCodeword

/-! Exact codeword recognition before general scalar decoding. -/

set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields CompPoly CompPoly.GuruswamiSudan

/-- Agreement on at least the scalar dimension identifies an encoded interleaved word. -/
theorem eq_of_codeword_agreement {vars lanes : Nat} (enc : Whir.Encoding K vars)
    (contract : Whir.EncodingContract enc (RingHom.id K))
    (f g : Whir.Table K (lanes + vars))
    (close : 2 ^ vars ≤ agreementCount enc (RingHom.id K) (enc.interleave (RingHom.id K) f) g) :
    g = f := by
  apply Whir.interleave_injective enc (RingHom.id K) contract
  funext x row
  let samples := Finset.univ.filter fun x =>
    enc.interleave (RingHom.id K) f x = enc.interleave (RingHom.id K) g x
  have first := Whir.interleave_mem enc (RingHom.id K) contract f row
  have second := Whir.interleave_mem enc (RingHom.id K) contract g row
  have same := ReedSolomon.eq_of_agree_of_card_le first second close
    (fun t ht => congrFun (Finset.mem_filter.mp ht).2 row)
  exact (congrFun same x).symm

/-- Full simultaneous agreement means literal equality of all supplied rows. -/
theorem word_eq_of_full_agreement {vars lanes : Nat} (enc : Whir.Encoding K vars)
    (word : Whir.Word K lanes (2 ^ (vars + enc.rate))) (f : Whir.Table K (lanes + vars))
    (full : agreementCount enc (RingHom.id K) word f = 2 ^ (vars + enc.rate)) :
    word = enc.interleave (RingHom.id K) f := by
  have same : Finset.univ.filter (fun x => word x = enc.interleave (RingHom.id K) f x) =
      Finset.univ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by simpa only [agreementCount, Finset.card_univ, Fintype.card_fin] using full.ge)
  funext x row
  have member : x ∈ Finset.univ.filter (fun x => word x = enc.interleave (RingHom.id K) f x) :=
    same.symm ▸ Finset.mem_univ x
  have equal : word x = enc.interleave (RingHom.id K) f x := (Finset.mem_filter.mp member).2
  exact congrFun equal row

/-- A recognized codeword is the exact singleton returned by the general decoder. -/
theorem gsDecode_codeword (vars rate lanes : Nat) (h : vars + rate ≤ 64)
    (positive : 0 < rate) (cutoff : Nat) (low : 2 ^ vars ≤ cutoff)
    (high : cutoff ≤ 2 ^ (vars + rate))
    (coverage : GsRowCoverage (RingHom.id K) vars rate lanes h baseGsContext cutoff)
    (f : Whir.Table K (lanes + vars)) :
    (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff)
      ((encoding vars rate h).interleave (RingHom.id K) f) = [f] := by
  have membership (g : Whir.Table K (lanes + vars)) :
      g ∈ (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff)
        ((encoding vars rate h).interleave (RingHom.id K) f) ↔ g ∈ [f] := by
    rw [gsDecode_mem_iff _ _ _ _ _ _ _ coverage]
    constructor
    · intro close
      exact List.mem_singleton.mpr (eq_of_codeword_agreement _
        (baseEncodingContract vars rate h positive) f g (low.trans close))
    · intro same
      rcases List.mem_singleton.mp same with rfl
      simpa only [agreementCount, Finset.filter_true_of_mem, Finset.filter_true, Finset.card_univ,
        Fintype.card_fin] using high
  exact List.perm_singleton.mp ((List.perm_ext_iff_of_nodup
    (gsDecode_nodup _ _ _ _ _ _ _ _) (List.nodup_singleton f)).mpr membership)

/-- Recover a candidate's packed novel coefficients from the first evaluation coset. -/
@[noinline, nospecialize] def recoverCodeword (vars rate lanes : Nat) (h : vars < 64)
    (word : Whir.Word K lanes (2 ^ (vars + rate))) : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes) :=
  let input := BF64.Packed.ofFn _ fun j =>
    let pair := finProdFinEquiv.symm j
    BF64.Word.ofField (word
      ⟨pair.1.val, pair.1.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))⟩
      (mask lanes pair.2))
  let plan := AdditiveNTT.Packed.Plan.create AdditiveNTT.Packed.flatBasis vars h
  AdditiveNTT.Packed.inverse plan vars (Nat.le_refl _) (2 ^ lanes) input

/-- Read the recovered candidate in the original lane-first Boolean variable order. -/
def recoveredTable (vars lanes : Nat) (coefficients : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) :
    Whir.Table K (lanes + vars) := fun u =>
  (BF64.Packed.read coefficients (finProdFinEquiv
    ((cubeEquiv vars).symm (fun i => u (Fin.natAdd lanes i)),
      (cubeEquiv lanes).symm (fun i => u (Fin.castAdd vars i))))).toField

/-- A lane-first vertex has the concatenated low-lane and high-column numeric index. -/
theorem cubeIndex_laneColumn {lanes vars : Nat} (u : Whir.Cube (lanes+vars)) :
    (cubeIndex (lanes+vars) u).val =
      (cubeIndex lanes (fun i => u (Fin.castAdd vars i))).val + 2^lanes *
        (cubeIndex vars (fun i => u (Fin.natAdd lanes i))).val := by
  let low := cubeIndex lanes (fun i => u (Fin.castAdd vars i))
  let high := cubeIndex vars (fun i => u (Fin.natAdd lanes i))
  let index : Fin (2^(lanes+vars)) :=
    ⟨low.val + 2^lanes*high.val, by
      have h := (finProdFinEquiv (high,low)).isLt
      change low.val + 2^lanes*high.val < 2^vars * 2^lanes at h
      simpa only [pow_add, Nat.mul_comm] using h⟩
  have same : cubeIndex (lanes+vars) u = index := by
    apply mask_injective (lanes+vars)
    rw [mask_cubeIndex]
    funext j
    symm
    change (low.val + 2^lanes*high.val).testBit j.val = u j
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add high.val low.isLt]
    split_ifs with lower
    · have bit := congrFun (mask_cubeIndex lanes (fun i => u (Fin.castAdd vars i))) ⟨j.val, lower⟩
      change low.val.testBit j.val = _ at bit
      simpa only [Fin.castAdd_mk] using bit
    · have bound : j.val-lanes < vars := by have := j.isLt; omega
      have bit := congrFun (mask_cubeIndex vars (fun i => u (Fin.natAdd lanes i))) ⟨j.val-lanes,bound⟩
      change high.val.testBit (j.val-lanes) = _ at bit
      rw [bit]
      congr 1
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
  exact congrArg Fin.val same

/-- Read recovered coefficients through one lane-first numeric coordinate index. -/
@[macro_inline] def recoveredTableDirect (vars lanes : Nat)
    (coefficients : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) : Whir.Table K (lanes + vars) :=
  let n := lanes+vars
  fun u => (BF64.Packed.read coefficients
    ⟨(cubeIndex n u).val, by
      have h := (cubeIndex n u).isLt
      simpa only [n, pow_add, Nat.mul_comm] using h⟩).toField

/-- The unified numeric coefficient index preserves the complete recovered table. -/
@[csimp] theorem recoveredTable_direct : recoveredTable = recoveredTableDirect := by
  funext vars lanes coefficients u
  unfold recoveredTable recoveredTableDirect
  apply congrArg BF64.Word.toField
  apply congrArg (BF64.Packed.read coefficients)
  apply Fin.ext
  exact (cubeIndex_laneColumn (lanes := lanes) (vars := vars) u).symm

/-- Compare recovered coefficients with every supplied codeword column. -/
def baseCodewordCheck (vars rate lanes : Nat) (h : vars + rate < 64)
    (word : Whir.Word K lanes (2 ^ (vars + rate)))
    (coefficients : BF64.Packed.Buffer (2 ^ vars * 2 ^ lanes)) : Bool :=
  decide (candidateAgreementCount (RingHom.id K) vars rate lanes h.le baseGsContext word
    (recoveredTable vars lanes coefficients) = 2 ^ (vars + rate))

/-- A packed transform and numeric lane comparison preserve full codeword recognition. -/
@[csimp] theorem baseCodewordCheck_code : @baseCodewordCheck = @packedCodewordCheck := by
  funext vars rate lanes h word coefficients
  rw [packedCodewordCheck_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [baseCodewordCheck, decide_eq_true_eq, candidateAgreementCount_eq]
  change agreementCount (encoding vars rate h.le) (RingHom.id K) word
    (recoveredTable vars lanes coefficients) = 2 ^ (vars + rate) ↔
      word = (encoding vars rate h.le).interleave (RingHom.id K)
        (recoveredTable vars lanes coefficients)
  constructor
  · exact word_eq_of_full_agreement (encoding vars rate h.le) word _
  · intro same
    rw [same]
    simp only [agreementCount, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]

/-- Recognize an exact codeword and otherwise run the same general ordered list decoder. -/
def checkedBaseDecode (vars rate lanes : Nat) (h : vars + rate ≤ 64) (cutoff : Nat) :
    Whir.Word K lanes (2 ^ (vars + rate)) → List (Whir.Table K (lanes + vars)) :=
  fun word =>
    if bounds : vars + rate < 64 ∧ 0 < rate ∧ 2 ^ vars ≤ cutoff ∧ cutoff ≤ 2 ^ (vars + rate) then
      match selected : finiteGSParamSelector.choose (2 ^ vars) (2 ^ (vars + rate))
          (2 ^ (vars + rate) - cutoff) with
      | none => (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff) word
      | some _ =>
        let coefficients := recoverCodeword vars rate lanes (by omega) word
        let candidate := recoveredTable vars lanes coefficients
        if baseCodewordCheck vars rate lanes bounds.1 word coefficients then [candidate]
        else (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff) word
    else (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff) word

attribute [local irreducible] recoverCodeword recoveredTable gsDecode baseCodewordCheck

/-- Checked recognition preserves every general-decoder result and its order on every word. -/
theorem checkedBaseDecode_eq (vars rate lanes : Nat) (h : vars + rate ≤ 64) (cutoff : Nat) :
    checkedBaseDecode vars rate lanes h cutoff =
      gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff := by
  funext word
  unfold checkedBaseDecode
  split_ifs with bounds
  · split
    · rfl
    · rename_i params selected
      dsimp only
      split_ifs with full
      · simp only [baseCodewordCheck, decide_eq_true_eq, candidateAgreementCount_eq] at full
        have same := word_eq_of_full_agreement (encoding vars rate h) word
          (recoveredTable vars lanes (recoverCodeword vars rate lanes (by omega) word)) full
        have result := gsDecode_codeword vars rate lanes h bounds.2.1 cutoff
          bounds.2.2.1 bounds.2.2.2
          (gsRowCoverage_of_selection _ _ _ _ _ _ _ bounds.2.2.2 params selected)
          (recoveredTable vars lanes (recoverCodeword vars rate lanes (by omega) word))
        exact ((congrArg (gsDecode (RingHom.id K) vars rate lanes h baseGsContext cutoff)
          same).trans result).symm
      · rfl
  · rfl

/-- Recognize complete codewords in the zero-filled backend and filter by revealed-column agreement. -/
def checkedBaseDecoder (vars rate lanes : Nat) (h : vars + rate ≤ 64) (cutoff : Nat) :
    Whir.ListDecoder (E := K) (encoding vars rate h) lanes :=
  maskedListDecoder (RingHom.id K) vars rate lanes h baseGsContext cutoff
    (checkedBaseDecode vars rate lanes h cutoff)

/-- Masked codeword recognition preserves the exact candidate list and ordering. -/
theorem checkedBaseDecoder_eq (vars rate lanes : Nat) (h : vars + rate ≤ 64) (cutoff : Nat) :
    checkedBaseDecoder vars rate lanes h cutoff =
      gsListDecoder (RingHom.id K) vars rate lanes h baseGsContext cutoff := by
  unfold checkedBaseDecoder gsListDecoder
  rw [checkedBaseDecode_eq]

end CompStark.Pcs
