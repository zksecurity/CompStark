/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.BinaryValues

/-! Structural coefficient semantics of the quadratic commitment-opening rounds. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open BF64
open scoped BigOperators

/-- The two transmitted coefficients computed by one native opening round. -/
def quadraticCoefficients (a b : Array W) (width : Nat) (scale : W) : W × W := Id.run do
  let mut zero : W := 0
  let mut infinity : W := 0
  for i in [:a.size/(2*width)] do
    for j in [:width] do
      let offset := 2*i*width+j
      zero := zero+a[offset]!*b[offset]!
      infinity := infinity+(a[offset]!+a[offset+width]!)*(b[offset]!+b[offset+width]!)
  return (scale*zero,scale*infinity)

/-- The exact constant and leading coefficients of the complete quadratic factor sum. -/
def quadraticCoefficientSum (a b : Array W) (width : Nat) (scale : W) : W × W :=
  (scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,
    a[2*i*width+j]!*b[2*i*width+j]!,
    scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,
      (a[2*i*width+j]!+a[2*i*width+j+width]!)*(b[2*i*width+j]!+b[2*i*width+j+width]!))

/-- Both native scalar accumulators equal the full mathematical quadratic coefficients. -/
theorem quadraticCoefficients_eq (a b : Array W) (width : Nat) (scale : W) :
    quadraticCoefficients a b width scale = quadraticCoefficientSum a b width scale := by
  let z (i j : Nat) := a[2*i*width+j]!*b[2*i*width+j]!
  let h (i j : Nat) := (a[2*i*width+j]!+a[2*i*width+j+width]!)*
    (b[2*i*width+j]!+b[2*i*width+j+width]!)
  let step (i : Nat) (state : W × W) (j : Nat) := (state.1+z i j,state.2+h i j)
  let outer (state : W × W) (i : Nat) := (List.range width).foldl (step i) state
  have hinner (state : W × W) (i : Nat) :
      (outer state i).1 = state.1+∑ j ∈ Finset.range width,z i j ∧
      (outer state i).2 = state.2+∑ j ∈ Finset.range width,h i j := by
    constructor
    · have hf := foldl_value_sum Prod.fst (step i) (z i) (fun _ _ => rfl) (List.range width) state
      rw [list_range_sum] at hf
      exact hf
    · have hf := foldl_value_sum Prod.snd (step i) (h i) (fun _ _ => rfl) (List.range width) state
      rw [list_range_sum] at hf
      exact hf
  have hz := foldl_value_sum Prod.fst outer (fun i => ∑ j ∈ Finset.range width,z i j)
    (fun state i => (hinner state i).1) (List.range (a.size/(2*width))) (0,0)
  have hh := foldl_value_sum Prod.snd outer (fun i => ∑ j ∈ Finset.range width,h i j)
    (fun state i => (hinner state i).2) (List.range (a.size/(2*width))) (0,0)
  simp only [list_range_sum,zero_add] at hz hh
  simp only [quadraticCoefficients,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  change (scale*((List.range (a.size/(2*width))).foldl outer (0,0)).1,
    scale*((List.range (a.size/(2*width))).foldl outer (0,0)).2) = _
  rw [hz,hh]
  rfl

/-- The Boolean endpoint sum of all paired quadratic factor rows. -/
def quadraticBooleanSum (a b : Array W) (width : Nat) (scale : W) : W :=
  scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,
    (a[2*i*width+j]!*b[2*i*width+j]! +
      a[2*i*width+j+width]!*b[2*i*width+j+width]!)

/-- The remaining factor sum after binding the current row coordinate. -/
def quadraticRoundSum (a b : Array W) (width : Nat) (scale r : W) : W :=
  scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,
    line a[2*i*width+j]! a[2*i*width+j+width]! r *
      line b[2*i*width+j]! b[2*i*width+j+width]! r

/-- In characteristic two, the omitted quadratic coefficient is determined by the endpoint sum. -/
theorem quadraticCell_decode (a b c d r : W) :
    a*b+r*((a*b+c*d)+(a+c)*(b+d)+r*((a+c)*(b+d))) =
      line a c r*line b d r := by
  unfold line
  linear_combination r * CharTwo.add_self_eq_zero (c*d)

/-- The actual two transmitted opening coefficients decode to the exact bound factor sum. -/
theorem quadraticCoefficients_decode (a b : Array W) (width : Nat) (scale r : W) :
    let coefficients := quadraticCoefficients a b width scale
    coefficients.1+r*(quadraticBooleanSum a b width scale+coefficients.2+r*coefficients.2) =
      quadraticRoundSum a b width scale r := by
  rw [quadraticCoefficients_eq]
  let z (i j : Nat) := a[2*i*width+j]!*b[2*i*width+j]!
  let v (i j : Nat) := z i j+a[2*i*width+j+width]!*b[2*i*width+j+width]!
  let h (i j : Nat) := (a[2*i*width+j]!+a[2*i*width+j+width]!)*
    (b[2*i*width+j]!+b[2*i*width+j+width]!)
  change (scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,z i j)+
    r*(scale*(∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,v i j)+
      scale*(∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,h i j)+
      r*(scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,h i j)) = _
  calc
    _ = scale*∑ i ∈ Finset.range (a.size/(2*width)), ∑ j ∈ Finset.range width,
        (z i j+r*(v i j+h i j+r*h i j)) := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    _ = quadraticRoundSum a b width scale r := by
      apply congrArg (fun value : W => scale*value)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact quadraticCell_decode _ _ _ _ _

/-- One opening message and challenge bind the same coordinate of both factor tables. -/
def quadraticStep (width : Nat) (scale : W) (state : QuadraticResult) : QuadraticResult :=
  let coefficients := quadraticCoefficients state.a state.b width scale
  let message := #[coefficients.1,coefficients.2]
  let (r,writer) := (state.writer.writeAll message).sample
  ⟨fold state.a width r,fold state.b width r,state.point.push r,state.messages.push message,
    coefficients.1+r*(state.value+coefficients.2+r*coefficients.2),writer⟩

/-- The complete production opening loop is a structural fold of its single-round transition. -/
theorem proveQuadratics_eq_fold (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (rounds : Nat) :
    proveQuadratics writer a b width scale value rounds =
      (List.range rounds).foldl (fun state _ => quadraticStep width scale state)
        ⟨a,b,#[],#[],value,writer⟩ := by
  simp only [proveQuadratics,foldArrayShared_eq,ite_self,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  let view (state : Array W × Array W × W × Writer × Array W × Array (Array W)) : QuadraticResult :=
    ⟨state.1,state.2.1,state.2.2.2.2.1,state.2.2.2.2.2,state.2.2.1,state.2.2.2.1⟩
  change view _ = _
  symm
  apply List.foldl_hom view (init := (a,b,value,writer,#[],#[]))
  intro state i
  dsimp only [view,quadraticStep]
  simp only [quadraticCoefficients,Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,pure_bind,Id.run_pure,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']

/-- Structural iteration of the complete production opening transition. -/
def quadraticRun (width : Nat) (scale : W) (initial : QuadraticResult) : Nat → QuadraticResult
  | 0 => initial
  | n+1 => quadraticStep width scale (quadraticRun width scale initial n)

/-- A range fold of opening transitions is the structurally recursive opening run. -/
theorem quadraticRun_eq_fold (width : Nat) (scale : W) (initial : QuadraticResult) (n : Nat) :
    quadraticRun width scale initial n =
      (List.range n).foldl (fun state _ => quadraticStep width scale state) initial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [quadraticRun,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]

/-- The actual native opening loop is the structurally recursive opening run. -/
theorem proveQuadratics_eq_run (writer : Writer) (a b : Array W) (width : Nat)
    (scale value : W) (rounds : Nat) :
    proveQuadratics writer a b width scale value rounds =
      quadraticRun width scale ⟨a,b,#[],#[],value,writer⟩ rounds := by
  rw [proveQuadratics_eq_fold,quadraticRun_eq_fold]

/-- Every opening transition appends exactly one message and one sampled coordinate. -/
theorem quadraticRun_lengths (width : Nat) (scale : W) (initial : QuadraticResult) (n : Nat) :
    (quadraticRun width scale initial n).point.size = initial.point.size+n ∧
      (quadraticRun width scale initial n).messages.size = initial.messages.size+n := by
  induction n with
  | zero => exact ⟨(Nat.add_zero _).symm,(Nat.add_zero _).symm⟩
  | succ n ih =>
    simp only [quadraticRun,quadraticStep,Array.size_push,ih.1,ih.2,Nat.add_assoc]
    trivial

/-- Opening iteration can expose its first transition before the remaining structural run. -/
theorem quadraticRun_succ_first (width : Nat) (scale : W) (initial : QuadraticResult) (n : Nat) :
    quadraticRun width scale initial (n+1) =
      quadraticRun width scale (quadraticStep width scale initial) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [quadraticRun,ih,quadraticRun]

/-- Appending to an array preserves every existing total-indexed read. -/
theorem array_push_get_old {A : Type} [Inhabited A] (a : Array A) (value : A)
    (i : Nat) (hi : i < a.size) : (a.push value)[i]! = a[i]! := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega),Array.getElem_push_lt hi,getElem!_pos a i hi]

/-- Appending to an array writes the new value at the former end. -/
theorem array_push_get_last {A : Type} [Inhabited A] (a : Array A) (value : A) :
    (a.push value)[a.size]! = value := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega),Array.getElem_push_eq]

/-- Opening iteration preserves every coordinate and message already present in the initial prefix. -/
theorem quadraticRun_prefix (width : Nat) (scale : W) (initial : QuadraticResult) (n : Nat) :
    (∀ i, i < initial.point.size → (quadraticRun width scale initial n).point[i]! = initial.point[i]!) ∧
      (∀ i, i < initial.messages.size →
        (quadraticRun width scale initial n).messages[i]! = initial.messages[i]!) := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n ih =>
    constructor
    · intro i hi
      rw [quadraticRun]
      dsimp only [quadraticStep]
      rw [array_push_get_old _ _ _ (by rw [(quadraticRun_lengths width scale initial n).1]; omega),ih.1 i hi]
    · intro i hi
      rw [quadraticRun]
      dsimp only [quadraticStep]
      rw [array_push_get_old _ _ _ (by rw [(quadraticRun_lengths width scale initial n).2]; omega),ih.2 i hi]

end CompStark.Keccak.GkrProver
