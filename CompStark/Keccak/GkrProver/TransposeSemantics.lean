/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.Refinement

/-! Sparse native position-weight transposition and the protocol linear adjoint. -/

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- The forward pi permutation sends a source lane to its destination lane. -/
def forwardPi (l : Fin 25) : Fin 25 :=
  ⟨l.val/5+5*((2*(l.val%5)+3*(l.val/5))%5),by omega⟩

/-- The inverse pi map recovers every source lane. -/
theorem inverse_forwardPi : ∀ l : Fin 25, inversePi (forwardPi l).val = l := by decide

/-- The forward pi map recovers every destination lane. -/
theorem forward_inversePi : ∀ l : Fin 25, forwardPi (inversePi l.val) = l := by decide

/-- Every rho rotation fits within one lane. -/
theorem rho_lt : ∀ l : Fin 25, rho l < 64 := by decide

/-- Forward rho/pi maps a pre-rotation bit to its transmitted position. -/
def forwardRhoPi (i : Fin 1600) : Fin 1600 :=
  let l : Fin 25 := ⟨i.val/64,by omega⟩
  ⟨64*(forwardPi l).val+(i.val%64+rho l)%64,by omega⟩

/-- Inverse rho/pi recovers the source bit of a transmitted position. -/
def backwardRhoPi (j : Fin 1600) : Fin 1600 :=
  let l := inversePi (j.val/64)
  ⟨64*l.val+(j.val%64+64-rho l)%64,by omega⟩

/-- Forward rho/pi followed by its inverse preserves every bit coordinate. -/
theorem backward_forwardRhoPi (i : Fin 1600) : backwardRhoPi (forwardRhoPi i) = i := by
  let l : Fin 25 := ⟨i.val/64,by omega⟩
  have hd : (forwardRhoPi i).val/64 = (forwardPi l).val := by
    dsimp only [forwardRhoPi,l]
    omega
  have hm : (forwardRhoPi i).val%64 = (i.val%64+rho l)%64 := by
    dsimp only [forwardRhoPi,l]
    omega
  apply Fin.ext
  change 64*(inversePi ((forwardRhoPi i).val/64)).val+_ = i.val
  rw [hd,inverse_forwardPi,hm]
  have hr := rho_lt l
  change 64*(i.val/64)+((i.val%64+rho l)%64+64-rho l)%64 = i.val
  omega

/-- Inverse rho/pi followed by the forward map preserves every bit coordinate. -/
theorem forward_backwardRhoPi (j : Fin 1600) : forwardRhoPi (backwardRhoPi j) = j := by
  let l := inversePi (j.val/64)
  have hd : (backwardRhoPi j).val/64 = l.val := by
    dsimp only [backwardRhoPi,l]
    omega
  have hm : (backwardRhoPi j).val%64 = (j.val%64+64-rho l)%64 := by
    dsimp only [backwardRhoPi,l]
    omega
  have he : (⟨(backwardRhoPi j).val/64,by omega⟩ : Fin 25) = l := Fin.ext hd
  apply Fin.ext
  change 64*(forwardPi ⟨(backwardRhoPi j).val/64,by omega⟩).val+_ = j.val
  rw [he,hm]
  have hp := forward_inversePi (⟨j.val/64,by omega⟩ : Fin 25)
  change forwardPi l = _ at hp
  rw [hp]
  have hr := rho_lt l
  change 64*(j.val/64)+((j.val%64+64-rho l)%64+rho l)%64 = j.val
  omega

/-- Rho/pi is a permutation of the complete 1600-bit state. -/
def rhoPiEquiv : Fin 1600 ≃ Fin 1600 where
  toFun := forwardRhoPi
  invFun := backwardRhoPi
  left_inv := backward_forwardRhoPi
  right_inv := forward_backwardRhoPi

/-- A source column coordinate together with its row selects a complete state position. -/
def columnPosition (c : Fin 320) (y : Fin 5) : Fin 1600 := ⟨c.val+320*y.val,by omega⟩

/-- A position's column coordinate and row are its quotient and remainder by 320. -/
theorem columnPosition_eq_iff (c : Fin 320) (y : Fin 5) (i : Fin 1600) :
    columnPosition c y = i ↔ c.val = i.val%320 ∧ y.val = i.val/320 := by
  simp only [columnPosition,Fin.ext_iff]
  omega

/-- The left theta source permutes the five columns of each bit plane. -/
def thetaLeft (c : Fin 320) : Fin 320 :=
  ⟨64*((c.val/64+4)%5)+c.val%64,by omega⟩

/-- The right theta source permutes columns and rotates the bit plane. -/
def thetaRight (c : Fin 320) : Fin 320 :=
  ⟨64*((c.val/64+1)%5)+(c.val%64+63)%64,by omega⟩

/-- Inverting the left theta source advances its column by one. -/
def thetaLeftInv (c : Fin 320) : Fin 320 :=
  ⟨64*((c.val/64+1)%5)+c.val%64,by omega⟩

/-- Inverting the right theta source retreats its column and advances its bit plane. -/
def thetaRightInv (c : Fin 320) : Fin 320 :=
  ⟨64*((c.val/64+4)%5)+(c.val%64+1)%64,by omega⟩

/-- The left theta source is a column permutation. -/
def thetaLeftEquiv : Fin 320 ≃ Fin 320 where
  toFun := thetaLeft
  invFun := thetaLeftInv
  left_inv c := by apply Fin.ext; simp only [thetaLeft,thetaLeftInv]; omega
  right_inv c := by apply Fin.ext; simp only [thetaLeft,thetaLeftInv]; omega

/-- The right theta source is a column-and-bit permutation. -/
def thetaRightEquiv : Fin 320 ≃ Fin 320 where
  toFun := thetaRight
  invFun := thetaRightInv
  left_inv c := by apply Fin.ext; simp only [thetaRight,thetaRightInv]; omega
  right_inv c := by apply Fin.ext; simp only [thetaRight,thetaRightInv]; omega

/-- Reindexing the linear layer by forward rho/pi exposes its three theta contributions. -/
theorem linear_forwardRhoPi {F : Type} [CommRing F] (a : Fin 1600 → F) (i : Fin 1600) :
    linear a (forwardRhoPi i) = a i +
      (∑ y, a (columnPosition (thetaLeft ⟨i.val%320,by omega⟩) y)) +
      (∑ y, a (columnPosition (thetaRight ⟨i.val%320,by omega⟩) y)) := by
  have hb := congrArg Fin.val (backward_forwardRhoPi i)
  change 64*(inversePi ((forwardRhoPi i).val/64)).val+
    ((forwardRhoPi i).val%64+64-rho (inversePi ((forwardRhoPi i).val/64)))%64 = i.val at hb
  unfold linear
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · exact congrArg a (Fin.ext hb)
    · apply Finset.sum_congr rfl
      intro y _
      apply congrArg a
      apply Fin.ext
      dsimp only [columnPosition,thetaLeft]
      omega
  · apply Finset.sum_congr rfl
    intro y _
    apply congrArg a
    apply Fin.ext
    dsimp only [columnPosition,thetaRight]
    omega

/-- Summing a column selector over rows retains exactly its matching column. -/
theorem columnDelta_sum {F : Type} [CommRing F] (c : Fin 320) (i : Fin 1600) :
    (∑ y : Fin 5, if columnPosition c y = i then (1 : F) else 0) =
      if c = ⟨i.val%320,by omega⟩ then 1 else 0 := by
  have h (y : Fin 5) : columnPosition c y = i ↔
      c = ⟨i.val%320,by omega⟩ ∧ y = ⟨i.val/320,by omega⟩ := by
    rw [columnPosition_eq_iff]
    simp only [Fin.ext_iff]
  simp only [h,ite_and,Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const_zero]

/-- The transpose of a theta column selector sums the inverse-permuted source column. -/
theorem thetaColumn_transpose {F : Type} [CommRing F] (w : Fin 1600 → F)
    (e : Fin 320 ≃ Fin 320) (i : Fin 1600) :
    (∑ j : Fin 1600, w j * ∑ y : Fin 5,
      if columnPosition (e ⟨j.val%320,by omega⟩) y = i then 1 else 0) =
      ∑ y : Fin 5, w (columnPosition (e.symm ⟨i.val%320,by omega⟩) y) := by
  simp only [columnDelta_sum]
  rw [← (finProdFinEquiv (m := 5) (n := 320)).sum_comp (fun j : Fin 1600 =>
    w j * if e ⟨j.val%320,by omega⟩ = ⟨i.val%320,by omega⟩ then 1 else 0),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have hlow (c : Fin 320) :
      (⟨((finProdFinEquiv (m := 5) (n := 320)) (y,c)).val%320,by omega⟩ : Fin 320) = c := by
    apply Fin.ext
    change (c.val+320*y.val)%320 = c.val
    omega
  simp only [hlow,← Equiv.eq_symm_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

/-- The protocol's linear transpose is the sparse inverse-rho/pi and two column sums. -/
theorem linearTranspose_sparse {F : Type} [CommRing F] (w : Fin 1600 → F) (i : Fin 1600) :
    linearTranspose w i = w (forwardRhoPi i) +
      (∑ y, w (forwardRhoPi (columnPosition (thetaLeftInv ⟨i.val%320,by omega⟩) y))) +
      (∑ y, w (forwardRhoPi (columnPosition (thetaRightInv ⟨i.val%320,by omega⟩) y))) := by
  unfold linearTranspose
  rw [← rhoPiEquiv.sum_comp]
  change (∑ j, w (forwardRhoPi j)*linear (fun k => if k=i then 1 else 0) (forwardRhoPi j)) = _
  simp only [linear_forwardRhoPi,mul_add,Finset.sum_add_distrib]
  have hleft := thetaColumn_transpose (fun j => w (forwardRhoPi j)) thetaLeftEquiv i
  have hright := thetaColumn_transpose (fun j => w (forwardRhoPi j)) thetaRightEquiv i
  change (∑ j, w (forwardRhoPi j)*∑ y, if columnPosition (thetaLeft ⟨j.val%320,by omega⟩) y=i then 1 else 0) =
    ∑ y, w (forwardRhoPi (columnPosition (thetaLeftInv ⟨i.val%320,by omega⟩) y)) at hleft
  change (∑ j, w (forwardRhoPi j)*∑ y, if columnPosition (thetaRight ⟨j.val%320,by omega⟩) y=i then 1 else 0) =
    ∑ y, w (forwardRhoPi (columnPosition (thetaRightInv ⟨i.val%320,by omega⟩) y)) at hright
  rw [hleft,hright]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Structural prefix of the native column accumulation loop. -/
def transposeColumns (g : Array W) (n : Nat) : Array W :=
  (List.range n).foldl (fun columns j =>
    columns.set! (64*(j/64%5)+j%64) (columns[64*(j/64%5)+j%64]!+g[j]!))
    (Array.replicate 320 0)

/-- After a column-loop prefix each bucket holds exactly the sum of matching positions. -/
theorem transposeColumns_invariant (g : Array W) (n : Nat) :
    (transposeColumns g n).size = 320 ∧ ∀ c : Fin 320,
      (transposeColumns g n)[c.val]! =
        ∑ j ∈ Finset.range n, if j%320=c.val then g[j]! else 0 := by
  induction n with
  | zero =>
    constructor
    · exact Array.size_replicate ..
    · intro c
      simp only [transposeColumns,List.range_zero,List.foldl_nil,Finset.range_zero,Finset.sum_empty]
      rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact c.isLt),Array.getElem_replicate]
  | succ n ih =>
    have hkey : 64*(n/64%5)+n%64 = n%320 := by omega
    have hstep : transposeColumns g (n+1) =
        (transposeColumns g n).set! (n%320) ((transposeColumns g n)[n%320]!+g[n]!) := by
      rw [transposeColumns,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,hkey]
      rfl
    rw [hstep]
    refine ⟨by rw [Array.size_set!,ih.1],?_⟩
    intro c
    rw [Finset.sum_range_succ]
    by_cases he : n%320=c.val
    · rw [he,Array.getElem!_set!_self _ _ _ (by rw [ih.1]; exact c.isLt),ih.2 c,ite_eq_left rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ he,ih.2 c,ite_eq_right he,add_zero]

/-- The complete native column loop is the sum of all five rows in each column. -/
theorem transposeColumns_get (g : Array W) (c : Fin 320) :
    (transposeColumns g 1600)[c.val]! = ∑ y : Fin 5, g[(columnPosition c y).val]! := by
  rw [(transposeColumns_invariant g 1600).2 c,← Fin.sum_univ_eq_sum_range]
  rw [← (finProdFinEquiv (m := 5) (n := 320)).sum_comp
    (fun j : Fin 1600 => if j.val%320=c.val then g[j.val]! else 0),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have hlow (k : Fin 320) : ((finProdFinEquiv (m := 5) (n := 320)) (y,k)).val%320=k.val := by
    change (k.val+320*y.val)%320=k.val
    omega
  simp only [hlow,← Fin.ext_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

/-- The native mutable column loop is its exact structural prefix fold. -/
theorem transposeColumnLoop_eq (g : Array W) (n : Nat) :
    transposeColumnLoop g n = transposeColumns g n := by
  simp only [transposeColumnLoop,transposeColumns,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']

attribute [local irreducible] transposeColumns rotations

/-- The sparse column expression expands to its two complete five-row sums. -/
theorem transposeColumns_sparse (g : Array W) (i : Fin 1600) :
    g[i.val]!+(transposeColumns g 1600)[64*((i.val/64%5+1)%5)+i.val%64]!+
      (transposeColumns g 1600)[64*((i.val/64%5+4)%5)+(i.val%64+1)%64]! =
    g[i.val]!+(∑ y, g[(columnPosition (thetaLeftInv ⟨i.val%320,by omega⟩) y).val]!)+
      (∑ y, g[(columnPosition (thetaRightInv ⟨i.val%320,by omega⟩) y).val]!) := by
  have hleft : 64*((i.val/64%5+1)%5)+i.val%64 = (thetaLeftInv ⟨i.val%320,by omega⟩).val := by
    dsimp only [thetaLeftInv]
    omega
  have hright : 64*((i.val/64%5+4)%5)+(i.val%64+1)%64 =
      (thetaRightInv ⟨i.val%320,by omega⟩).val := by
    dsimp only [thetaRightInv]
    omega
  rw [hleft,hright,transposeColumns_get,transposeColumns_get]

/-- Defaulting lookup of a dimension-indexed array returns its defining coordinate. -/
theorem ofFn_get! {A : Type} [Inhabited A] {n : Nat} (f : Fin n → A) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact i.isLt),Array.getElem_ofFn]

/-- The native sparse transpose reads the protocol's exact adjoint position weight. -/
theorem transposeWeights_eq (weights : Array W) (i : Fin 1600) :
    (transposeWeights weights)[i.val]! = linearTranspose (fun j => weights[j.val]!) i := by
  let g := Array.ofFn fun j : Fin 1600 => weights[(forwardRhoPi j).val]!
  have hg (j : Fin 1600) : g[j.val]! = weights[(forwardRhoPi j).val]! :=
    ofFn_get! (fun j : Fin 1600 => weights[(forwardRhoPi j).val]!) j
  have hnative : transposeWeights weights = Array.ofFn fun j : Fin 1600 =>
      g[j.val]!+(transposeColumns g 1600)[64*((j.val/64%5+1)%5)+j.val%64]!+
        (transposeColumns g 1600)[64*((j.val/64%5+4)%5)+(j.val%64+1)%64]! := by
    have hforward : (Array.ofFn fun k : Fin 1600 =>
        weights[64*(k.val/64/5+5*((2*(k.val/64%5)+3*(k.val/64/5))%5))+
          (k.val%64+rotations[k.val/64]!)%64]!) = g := by
      apply congrArg Array.ofFn
      funext k
      rw [rotations_eq ⟨k.val/64,by omega⟩]
      rfl
    let finish (source : Array W) := Array.ofFn fun j : Fin 1600 =>
      source[j.val]!+(transposeColumns source 1600)[64*((j.val/64%5+1)%5)+j.val%64]!+
        (transposeColumns source 1600)[64*((j.val/64%5+4)%5)+(j.val%64+1)%64]!
    have hloop : transposeWeights weights = finish (Array.ofFn fun k : Fin 1600 =>
        weights[64*(k.val/64/5+5*((2*(k.val/64%5)+3*(k.val/64/5))%5))+
          (k.val%64+rotations[k.val/64]!)%64]!) := by
      simp only [transposeWeights,transposeColumnLoop_eq]
      rfl
    exact hloop.trans (congrArg finish hforward)
  have hread := congrArg (fun a : Array W => a[i.val]!) hnative
  have hh := hread.trans (ofFn_get! (fun j : Fin 1600 =>
    g[j.val]!+(transposeColumns g 1600)[64*((j.val/64%5+1)%5)+j.val%64]!+
      (transposeColumns g 1600)[64*((j.val/64%5+4)%5)+(j.val%64+1)%64]!) i)
  calc
    (transposeWeights weights)[i.val]! = _ := hh.trans (transposeColumns_sparse g i)
    _ = weights[(forwardRhoPi i).val]!+
        (∑ y, weights[(forwardRhoPi (columnPosition (thetaLeftInv ⟨i.val%320,by omega⟩) y)).val]!)+
        (∑ y, weights[(forwardRhoPi (columnPosition (thetaRightInv ⟨i.val%320,by omega⟩) y)).val]!) := by
      simp only [hg]
    _ = _ := (linearTranspose_sparse (fun j => weights[j.val]!) i).symm

/-- Native sparse transposition commutes with the verifier-field interpretation. -/
theorem transposeWeights_toField (weights : Array W) (i : Fin 1600) :
    (transposeWeights weights)[i.val]!.toField = linearTranspose (fun j => weights[j.val]!.toField) i := by
  rw [transposeWeights_eq]
  change WordExt3.ringEquiv (linearTranspose (fun j => weights[j.val]!) i) = _
  rw [linearTranspose_sparse,linearTranspose_sparse]
  simp only [map_add,map_sum]
  rfl

end CompStark.Keccak.GkrProver
