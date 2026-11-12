/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.ProductSemantics
public import CompStark.Keccak.GkrProver.PackTrace
public import CompStark.Keccak.GkrProver.CofactorBlocks

/-! Committed-witness interpretation of retained pack factors and their tensor boundary. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- The native retained row count removes exactly four low pack coordinates. -/
theorem retainedRows_eq (w : SlicedWitness) {h : Nat} (hn : w.nLog=h+8) :
    2^(w.nLog-4)/16=2^h := by
  rw [hn,show h+8-4=h+4 by omega,pow_add]
  exact Nat.mul_div_cancel _ (by decide)

/-- A native RMFE factor is the committed pre-chi factor evaluated at the product challenge. -/
theorem rmfeFactor_protocol (w : SlicedWitness) {p : Nat} (q : Witness p) (hw : PreChiRefines w q)
    (d : Fin 12) (m : Fin 2) (b : Fin (2^p)) (j : Fin 1600) (s : W) :
    rmfeValue s (lane ((w.layers[12*(m.val+1)-d.val]!)[j.val*(2^w.nLog/64)+b.val/4]!
      >>> (16*(b.val%4)).toUInt64)) = (packedLinear q d m b j).eval s := by
  rw [← rmfeValue_mask16]
  exact congrArg (fun P : Polynomial W => P.eval s) (productFactor_protocol w q hw d m b j)

/-- Every retained native cell interpolates the committed pre-chi factors over the four low pack challenges. -/
theorem packedTable_get_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W)
    (point : Array W) (hp : point.size=4) (m : Fin 2) (b : Fin (2^h)) (j : Fin 1600) :
    (packedTable w d.val (instanceWeights s) point).get ((m.val*2^h+b.val)*1600+j.val) =
      mle (n := 4) (fun u : Fin 16 =>
        (packedLinear q d m ⟨16*b.val+u.val,by
          rw [pow_add,show 2^4=(16 : Nat) from rfl]
          have := b.isLt
          have := u.isLt
          omega⟩ j).eval s) (fun i : Fin 4 => point[i.val]!) := by
  have hr := retainedRows_eq w hn
  have hb : b.val < 2^(w.nLog-4)/16 := by rw [hr]; exact b.isLt
  have hh := packedTable_get_rmfe w d.val s point m b.val hb j
  rw [hr] at hh
  rw [hh]
  unfold mle
  apply Finset.sum_congr rfl
  intro u _
  rw [eqTable_get_dimension point 4 hp u]
  congr 1
  have hd : (16*b.val+u.val)/4=4*b.val+u.val/4 := by omega
  have hm : (16*b.val+u.val)%4=u.val%4 := by omega
  simpa only [hd,hm,Nat.add_assoc] using rmfeFactor_protocol w q hw d m
    ⟨16*b.val+u.val,by rw [pow_add,show 2^4=(16 : Nat) from rfl]; have := b.isLt; have := u.isLt; omega⟩ j s

/-- One retained row of the protocol pack cube, with its four low coordinates evaluated. -/
noncomputable def retainedFactor {F : Type} [CommRing F] [CharP F 2] {h : Nat}
    (q : Witness (h+4)) (d : Fin 12) (s : F) (low : Fin 4 → F)
    (j : Fin 1600) (row : Fin (2^(h+1))) : F :=
  mle (n := 4) (fun u : Fin 16 => packTable q d s j
    ⟨u.val+16*row.val,by
      have hu := u.isLt
      have hr := row.isLt
      calc
        _ < 16*2^(h+1) := by omega
        _ = 2^(h+4+1) := by rw [show h+4+1=(h+1)+4 by omega,pow_add]; ring⟩) low

/-- The segmented retained row has the same pack and segment addresses as the protocol cube. -/
theorem retainedFactor_segment {F : Type} [CommRing F] [CharP F 2] {h : Nat}
    (q : Witness (h+4)) (d : Fin 12) (s : F) (low : Fin 4 → F)
    (j : Fin 1600) (m : Fin 2) (b : Fin (2^h)) :
    retainedFactor q d s low j ⟨m.val*2^h+b.val,by
      simpa only [pow_succ,Nat.mul_comm] using row_index_lt b.isLt m⟩ =
      mle (n := 4) (fun u : Fin 16 =>
        (packedLinear q d m ⟨16*b.val+u.val,by
          rw [pow_add,show 2^4=(16 : Nat) from rfl]; have := b.isLt; have := u.isLt; omega⟩ j).eval s) low := by
  unfold retainedFactor
  apply congrArg (fun table : Fin 16 → F => mle (n := 4) table low)
  funext u
  have hb : 16*b.val+u.val < 2^(h+4) := by
    rw [pow_add,show 2^4=(16 : Nat) from rfl]; have := b.isLt; have := u.isLt; omega
  have hi : u.val+16*(m.val*2^h+b.val) = (16*b.val+u.val)+2^(h+4)*m.val := by
    rw [pow_add,show 2^4=(16 : Nat) from rfl]; ring
  unfold packTable
  simp only [hi,Nat.add_mul_div_left _ _ (by positivity : 0<2^(h+4)),
    Nat.div_eq_of_lt hb,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb]

/-- Every retained native table entry equals the corresponding committed protocol factor. -/
theorem packedTable_retainedFactor (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W)
    (point : Array W) (hp : point.size=4) (row : Fin (2^(h+1))) (j : Fin 1600) :
    (packedTable w d.val (instanceWeights s) point).get (row.val*1600+j.val) =
      retainedFactor q d s (fun i : Fin 4 => point[i.val]!) j row := by
  let m : Fin 2 := ⟨row.val/2^h,by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [pow_succ,Nat.mul_comm] using row.isLt⟩
  let b : Fin (2^h) := ⟨row.val%2^h,Nat.mod_lt _ (by positivity)⟩
  have hr : row = ⟨m.val*2^h+b.val,by simpa only [pow_succ,Nat.mul_comm] using row_index_lt b.isLt m⟩ := by
    apply Fin.ext
    dsimp only [m,b]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod row.val (2^h)).symm
  rw [hr,retainedFactor_segment]
  exact packedTable_get_protocol w q hn hw d s point hp m b j

/-- Interpolating retained committed rows evaluates the full protocol pack factor. -/
theorem retainedFactor_mle {F : Type} [CommRing F] [CharP F 2] {h : Nat}
    (q : Witness (h+4)) (d : Fin 12) (s : F) (low : Fin 4 → F)
    (high : Fin (h+1) → F) (j : Fin 1600) :
    mle (retainedFactor q d s low j) high = linearAtPack q d s (joinPoint (a := 4) (b := h+1) low high) j := by
  rw [linearAtPack_eq_mle]
  have hh := mle_blocks (n := h+4+1) (a := 4) (b := h+1) (by omega)
    (fun u : Fin 16 => fun row : Fin (2^(h+1)) => packTable q d s j
      ⟨u.val+16*row.val,by
        have hu := u.isLt
        have hr := row.isLt
        calc
          _ < 16*2^(h+1) := by omega
          _ = 2^(h+4+1) := by rw [show h+4+1=(h+1)+4 by omega,pow_add]; ring⟩)
    (joinPoint (a := 4) (b := h+1) low high)
  have ht : (fun w : Fin (2^(h+4+1)) => packTable q d s j
      ⟨w.val%16+16*(w.val/16),by omega⟩) = packTable q d s j := by
    funext w
    congr 1
    apply Fin.ext
    exact Nat.mod_add_div _ _
  change mle (fun w : Fin (2^(h+4+1)) => packTable q d s j
    ⟨w.val%16+16*(w.val/16),_⟩) (joinPoint (a := 4) (b := h+1) low high) = _ at hh
  rw [ht] at hh
  rw [hh]
  have hlo : (fun i : Fin 4 => joinPoint (a := 4) (b := h+1) low high ⟨i.val,by omega⟩) = low := by
    funext i
    simp only [joinPoint,i.isLt,dite_true]
  have hhi : (fun i : Fin (h+1) => joinPoint (a := 4) (b := h+1) low high ⟨4+i.val,by omega⟩) = high := by
    funext i
    simp only [joinPoint,show ¬4+i.val<4 by omega,dite_false,Nat.add_sub_cancel_left]
  rw [hlo,hhi]
  rfl

/-- Interpolating any retained native factor column gives the full committed pack evaluation. -/
theorem packedTable_column_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W)
    (point : Array W) (hp : point.size=4) (high : Fin (h+1) → W) (j : Fin 1600) :
    mle (fun row : Fin (2^(h+1)) =>
      (packedTable w d.val (instanceWeights s) point).toArray[row.val*1600+j.val]!) high =
      linearAtPack q d s (joinPoint (a := 4) (b := h+1) (fun i : Fin 4 => point[i.val]!) high) j := by
  rw [← retainedFactor_mle]
  apply congrArg (fun table : Fin (2^(h+1)) → W => mle table high)
  funext row
  rw [PackedE.get_toArray _ _ (by
    rw [packedTable_size,retainedRows_eq w hn]
    have hh := row_index_lt j.isLt row
    simpa only [pow_succ,Nat.mul_comm,Nat.mul_left_comm] using hh)]
  exact packedTable_retainedFactor w q hn hw d s point hp row j

/-- The protocol pack cofactor evaluates the weighted chi expression on its three committed factors. -/
theorem packCofactorPolynomial_value {F : Type} [CommRing F] [CharP F 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (claim : Gkr.Claim F p) (s : F) (point : Fin (p+1) → F) :
    MvPolynomial.eval point (packCofactorPolynomial q d claim s) =
      ∑ j : Fin 1600,claim.weights j *
        ((∑ i : Fin 16,muAt s i)*linearAtPack q d s point j+
          ((∑ i : Fin 16,muAt s i)+linearAtPack q d s point (along j 1))*
            linearAtPack q d s point (along j 2)) := by
  simp only [packCofactorPolynomial,chiPolynomial,map_sum,map_mul,map_add,MvPolynomial.eval_C,
    mle_eq_eval,← linearAtPack_eq_mle,Fin.val_zero,Fin.val_one,along_zero]
  rfl

/-- The retained native cofactor is the committed protocol cofactor with the four low pack coordinates bound. -/
theorem packTableCofactor_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s scale : W) (claim : Claim)
    (point : Array W) (hp : point.size=4) (high : Fin (h+1) → W) :
    packTableCofactor (packedTable w d.val (instanceWeights s) point) claim.weights (h+1)
      scale (sum (instanceWeights s)) high =
      scale*MvPolynomial.eval (joinPoint (a := 4) (b := h+1) (fun i => point[i.val]!) high)
        (packCofactorPolynomial q d (claim.toWordProtocol (h+4)) s) := by
  rw [packCofactorPolynomial_value]
  unfold packTableCofactor
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro j _
  rw [shift_eq j 1,shift_eq j 2]
  rw [packedTable_column_protocol w q hn hw d s point hp high j,
    packedTable_column_protocol w q hn hw d s point hp high (along j 1),
    packedTable_column_protocol w q hn hw d s point hp high (along j 2),instanceWeights_sum]
  rfl

/-- The complete native early tensor is the protocol cofactor projected over its high equality-weighted pack block. -/
theorem nativeTensorValue_protocol (w : SlicedWitness) {h : Nat} (q : Witness (h+4))
    (hn : w.nLog=h+8) (hw : PreChiRefines w q) (d : Fin 12) (s : W) (claim : Claim)
    (hc : claim.point.size=h+5) (hbound : 1600*(2^w.nLog/64) ≤ USize.size)
    (point : Array W) (hp : point.size=4) :
    nativeTensorValue w d.val claim s point =
      booleanSum (fun high : Fin (h+1) → W =>
        eqEval (fun i : Fin (h+1) => (claim.point.extract 4 claim.point.size)[i.val]!) high *
          MvPolynomial.eval (joinPoint (a := 4) (b := h+1) (fun i => point[i.val]!) high)
            (packCofactorPolynomial q d (claim.toWordProtocol (h+4)) s)) := by
  have hn8 : 8 ≤ w.nLog := by omega
  have hc' : claim.point.size=w.nLog-3 := by omega
  have hs : (claim.point.extract 4 claim.point.size).size=h+1 := by
    rw [Array.size_extract,Nat.min_self,hc]; omega
  have hh := nativeTensorValue_packTable w d.val claim s point hp
    (packBoundary_rows w hn8 claim hc') (packBoundary_address w hn8 hbound)
  rw [hh]
  generalize hz : (claim.point.extract 4 claim.point.size).size = n
  have hn1 : n=h+1 := hz.symm.trans hs
  clear hz
  subst n
  apply congrArg booleanSum
  funext high
  rw [packTableCofactor_protocol w q hn hw d s 1 claim point hp high,one_mul]

end CompStark.Keccak.GkrProver
