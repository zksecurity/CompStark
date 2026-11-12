/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.NativeCompleteness

/-! Structural bit-gather and retained-round semantics of native witness construction. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr BF64

/-- Gather one bit from each source word into consecutive machine-word positions. -/
def sliceGather (source : Nat → UInt64) (z : Nat) : Nat → UInt64
  | 0 => 0
  | n+1 => sliceGather source z n ||| (((source n >>> z.toUInt64) &&& 1) <<< n.toUInt64)

/-- Structural gathering agrees with the native ascending range fold. -/
theorem sliceGather_eq_fold (source : Nat → UInt64) (z n : Nat) :
    sliceGather source z n=(List.range n).foldl (fun word b => word ||| (((source b >>> z.toUInt64) &&& 1) <<< b.toUInt64)) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sliceGather,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]

/-- A shifted singleton source bit occupies exactly its designated output bit. -/
theorem sliceGather_single_bit (word : UInt64) (z n : Fin 64) (b : Fin 64) :
    ((((word >>> z.val.toUInt64) &&& 1) <<< n.val.toUInt64).toBitVec.getLsbD b.val)=
      (decide (b=n) && word.toBitVec.getLsbD z.val) := by
  have hz : ((z.val.toUInt64.toBitVec % 64).toNat)=z.val := by
    change z.val.toUInt64.toNat % (64 % 2^64)=z.val
    simp only [Nat.toUInt64,UInt64.toNat_ofNat',show (64 : Nat)%2^64=64 from rfl,
      Nat.mod_eq_of_lt (lt_trans z.isLt (by decide : 64<2^64)),Nat.mod_eq_of_lt z.isLt]
  have hn : ((n.val.toUInt64.toBitVec % 64).toNat)=n.val := by
    change n.val.toUInt64.toNat % (64 % 2^64)=n.val
    simp only [Nat.toUInt64,UInt64.toNat_ofNat',show (64 : Nat)%2^64=64 from rfl,
      Nat.mod_eq_of_lt (lt_trans n.isLt (by decide : 64<2^64)),Nat.mod_eq_of_lt n.isLt]
  simp only [UInt64.toBitVec_shiftLeft,UInt64.toBitVec_shiftRight,UInt64.toBitVec_and,
    UInt64.toBitVec_ofNat,BitVec.shiftLeft_eq',BitVec.ushiftRight_eq',hz,hn,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_and,BitVec.getLsbD_ushiftRight,
    decide_eq_true b.isLt,Bool.true_and]
  by_cases h : b=n
  · subst b
    simp only [Nat.lt_irrefl,decide_false,Bool.not_false,Bool.true_and,Nat.sub_self,Nat.add_zero,
      BitVec.getLsbD_ofNat,decide_true,show (0 : Nat)<64 from by decide,
      show Nat.testBit 1 0=true from rfl,Bool.and_true]
  · have hval : b.val≠n.val := fun hh => h (Fin.ext hh)
    by_cases hlt : b.val<n.val
    · simp only [hlt,decide_true,Bool.not_true,Bool.false_and,h,decide_false]
    · have hbit : (BitVec.ofNat 64 1).getLsbD (b.val-n.val)=false := by
        rw [BitVec.getLsbD_ofNat]
        exact Bool.and_eq_false_iff.mpr (Or.inr (Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))))
      simp only [hbit,Bool.and_false,h,decide_false,Bool.false_and]

/-- After gathering a prefix, every output bit is its source bit or zero beyond the prefix. -/
theorem sliceGather_bit (source : Nat → UInt64) (z : Fin 64) (n : Nat) (hn : n≤64) (b : Fin 64) :
    (sliceGather source z.val n).toBitVec.getLsbD b.val =
      if b.val<n then (source b.val).toBitVec.getLsbD z.val else false := by
  induction n with
  | zero => simp only [sliceGather,UInt64.toBitVec_ofNat,BitVec.getLsbD_zero,Nat.not_lt_zero,↓reduceIte]
  | succ n ih =>
    rw [sliceGather,UInt64.toBitVec_or,BitVec.getLsbD_or,ih (by omega),sliceGather_single_bit (source n) z ⟨n,by omega⟩ b]
    by_cases hb : b.val=n
    · have hfin : b=(⟨n,by omega⟩ : Fin 64) := Fin.ext hb
      simp only [hb,Nat.lt_irrefl,↓reduceIte,decide_eq_true hfin,Bool.true_and,Bool.false_or,
        Nat.lt_add_one]
    · have hfin : b≠(⟨n,by omega⟩ : Fin 64) := fun h => hb (congrArg Fin.val h)
      rw [decide_eq_false hfin,Bool.false_and,Bool.or_false]
      have heq : (b.val<n)=(b.val<n+1) := propext (by omega)
      simp only [heq]

/-- Fill a consecutive array interval with prescribed cells. -/
def fillArray {F : Type} (a : Array F) (start n : Nat) (value : Nat → F) : Array F :=
  (List.range n).foldl (fun a i => a.set! (start+i) (value i)) a

/-- Filling an interval preserves the complete array size. -/
theorem fillArray_size {F : Type} (a : Array F) (start n : Nat) (value : Nat → F) :
    (fillArray a start n value).size=a.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fillArray,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,Array.size_set!]
    exact ih

/-- An interval fill changes exactly its designated coordinates. -/
theorem fillArray_get {F : Type} [Inhabited F] (a : Array F) (start n : Nat) (value : Nat → F)
    (hn : start+n≤a.size) (i : Nat) :
    (fillArray a start n value)[i]! = if (start ≤ i ∧ i < start+n) then value (i-start) else a[i]! := by
  induction n with
  | zero => simp only [fillArray,List.range_zero,List.foldl_nil,Nat.add_zero,show ¬(start ≤ i ∧ i < start) by omega,↓reduceIte]
  | succ n ih =>
    simp only [fillArray,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    by_cases hi : start+n=i
    · subst i
      rw [Array.getElem!_set!_self _ _ _ (by rw [← fillArray,fillArray_size]; omega)]
      rw [ite_eq_left (by omega),Nat.add_sub_cancel_left]
    · rw [Array.getElem!_set!_ne _ _ _ _ hi]
      rw [← fillArray,ih (by omega)]
      have hh : (start ≤ i ∧ i < start+n)=(start ≤ i ∧ i < start+(n+1)) := propext (by omega)
      simp only [hh]

/-- Fill consecutive complete rows of a flat array. -/
def fillRows {F : Type} (a : Array F) (start rows width : Nat) (value : Nat → Nat → F) : Array F :=
  (List.range rows).foldl (fun a row => fillArray a ((start+row)*width) width (value row)) a

/-- Complete-row filling preserves the allocation size. -/
theorem fillRows_size {F : Type} (a : Array F) (start rows width : Nat) (value : Nat → Nat → F) :
    (fillRows a start rows width value).size=a.size := by
  induction rows with
  | zero => rfl
  | succ rows ih =>
    simp only [fillRows,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,fillArray_size]
    exact ih

/-- A flat row coordinate lies in exactly its own complete row interval. -/
theorem row_interval {width g : Nat} (hg : g<width) (j r : Nat) :
    (r*width ≤ j*width+g ∧ j*width+g < r*width+width) ↔ j=r := by
  have hh := Nat.div_eq_iff (x := j*width+g) (y := r) (by omega : 0<width)
  rw [row_div hg] at hh
  omega

/-- Complete-row filling changes exactly its designated row indices. -/
theorem fillRows_get {F : Type} [Inhabited F] (a : Array F) (start rows width : Nat) (value : Nat → Nat → F)
    (hsize : (start+rows)*width≤a.size) (j g : Nat) (hg : g<width) :
    (fillRows a start rows width value)[j*width+g]! =
      if (start ≤ j ∧ j < start+rows) then value (j-start) g else a[j*width+g]! := by
  induction rows with
  | zero => simp only [fillRows,List.range_zero,List.foldl_nil,Nat.add_zero,show ¬(start ≤ j ∧ j < start) by omega,↓reduceIte]
  | succ rows ih =>
    rw [fillRows,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [fillArray_get _ _ _ _ (by rw [← fillRows,fillRows_size]; simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hsize)]
    simp only [show ((start+rows)*width ≤ j*width+g ∧ j*width+g < (start+rows)*width+width)=(j=start+rows) from propext (row_interval hg j (start+rows))]
    by_cases hj : j=start+rows
    · simp only [hj,↓reduceIte,Nat.add_sub_cancel_left]
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_right hj,← fillRows,ih (by nlinarith)]
      have hh : (start ≤ j ∧ j < start+rows)=(start ≤ j ∧ j < start+(rows+1)) := propext (by omega)
      simp only [hh]

/-- The native initial slicing loops as nested structural interval fills. -/
def slicedInitial (nLog : Nat) (committed : Array UInt64) : Array UInt64 :=
  let n := 2^nLog
  let groups := n/64
  (List.range 25).foldl (fun state l =>
    fillRows state (64*l) 64 groups (fun z group =>
      sliceGather (fun b => committed[l*n+64*group+b]!) z 64))
    (Array.replicate (1600*groups) 0)

/-- Native round transitions retain their exact pre-chi input for the product prover. -/
def slicedRoundStep (groups : Nat) (state : Array UInt64 × Array (Array UInt64)) (r : Nat) :
    Array UInt64 × Array (Array UInt64) :=
  let preChi := linearSlices state.1 groups
  (chiSlices preChi groups r,state.2.push preChi)

/-- A structural prefix of the native witness round loop. -/
def slicedRoundTrace (groups rounds : Nat) (initial : Array UInt64) : Array UInt64 × Array (Array UInt64) :=
  (List.range rounds).foldl (slicedRoundStep groups) (initial,#[initial])

attribute [local irreducible] linearSlices chiSlices

/-- The production witness stores precisely the pre-chi trace from its initial bit-gather loops. -/
theorem buildWitness_layers (nLog : Nat) (committed : Array UInt64) :
    (buildWitness nLog committed).layers=(slicedRoundTrace (2^nLog/64) 24 (slicedInitial nLog committed)).2 := by
  have hbind {A B : Type} (a : Id A) (f : A → Id B) : a >>= f = f a := rfl
  have hpure {A : Type} (a : A) : (pure a : Id A)=a := rfl
  simp only [buildWitness,Std.Legacy.Range.forIn_eq_forIn_range',hbind,List.forIn_pure_yield_eq_foldl,
    Id.run_pure,Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  simp only [hpure]
  simp only [slicedRoundTrace,slicedInitial,fillRows,fillArray,sliceGather_eq_fold]
  rfl


/-- A prefix of the native lane-slicing loop. -/
def slicedInitialPrefix (nLog : Nat) (committed : Array UInt64) (lanes : Nat) : Array UInt64 :=
  let n := 2^nLog
  let groups := n/64
  (List.range lanes).foldl (fun state l =>
    fillRows state (64*l) 64 groups (fun z group =>
      sliceGather (fun b => committed[l*n+64*group+b]!) z 64))
    (Array.replicate (1600*groups) 0)

/-- Lane-slicing prefixes retain their complete allocation. -/
theorem slicedInitialPrefix_size (nLog : Nat) (committed : Array UInt64) (lanes : Nat) :
    (slicedInitialPrefix nLog committed lanes).size=1600*(2^nLog/64) := by
  induction lanes with
  | zero => exact Array.size_replicate ..
  | succ lanes ih =>
    simp only [slicedInitialPrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,fillRows_size]
    exact ih

/-- After slicing a lane prefix, each processed lane contains its complete gathered word. -/
theorem slicedInitialPrefix_get (nLog : Nat) (committed : Array UInt64) (lanes : Nat) (hlanes : lanes≤25)
    (l : Fin 25) (z : Fin 64) (group : Nat) (hg : group<2^nLog/64) :
    (slicedInitialPrefix nLog committed lanes)[(64*l.val+z.val)*(2^nLog/64)+group]! =
      if l.val<lanes then sliceGather (fun b => committed[l.val*2^nLog+64*group+b]!) z.val 64 else 0 := by
  induction lanes with
  | zero =>
    simp only [slicedInitialPrefix,List.range_zero,List.foldl_nil,Nat.not_lt_zero,↓reduceIte]
    rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact row_index_lt hg ⟨64*l.val+z.val,by omega⟩),Array.getElem_replicate]
  | succ lanes ih =>
    rw [slicedInitialPrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [fillRows_get _ _ _ _ _ (by rw [← slicedInitialPrefix,slicedInitialPrefix_size]; nlinarith [l.isLt,z.isLt]) _ _ hg]
    have hregion : (64*lanes ≤ 64*l.val+z.val ∧ 64*l.val+z.val < 64*lanes+64)=(l.val=lanes) :=
      propext (by simpa only [Nat.mul_comm] using row_interval z.isLt l.val lanes)
    simp only [hregion]
    by_cases hl : l.val=lanes
    · simp only [← hl,↓reduceIte,Nat.add_sub_cancel_left,Nat.lt_add_one]
    · rw [ite_eq_right hl,← slicedInitialPrefix,ih (by omega)]
      have hh : (l.val<lanes)=(l.val<lanes+1) := propext (by omega)
      simp only [hh]

/-- Every bit gathered by the initial native slicing loops is its original committed input bit. -/
theorem slicedInitial_bit (nLog : Nat) (committed : Array UInt64) (l : Fin 25) (z b : Fin 64)
    (group : Nat) (hg : group<2^nLog/64) :
    sliceBit (slicedInitial nLog committed)[(64*l.val+z.val)*(2^nLog/64)+group]! b =
      sliceBit committed[l.val*2^nLog+64*group+b.val]! z := by
  rw [show slicedInitial nLog committed=slicedInitialPrefix nLog committed 25 from rfl,
    slicedInitialPrefix_get nLog committed 25 (by decide) l z group hg,ite_eq_left l.isLt]
  unfold sliceBit
  rw [sliceGather_bit _ z 64 (by decide) b,ite_eq_left b.isLt]


/-- A structural successor appends exactly the next production pre-chi state. -/
theorem slicedRoundTrace_succ (groups rounds : Nat) (initial : Array UInt64) :
    slicedRoundTrace groups (rounds+1) initial=slicedRoundStep groups (slicedRoundTrace groups rounds initial) rounds := by
  rw [slicedRoundTrace,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

/-- A round trace contains its input followed by one retained pre-chi state per round. -/
theorem slicedRoundTrace_size (groups rounds : Nat) (initial : Array UInt64) :
    (slicedRoundTrace groups rounds initial).2.size=rounds+1 := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    rw [slicedRoundTrace_succ]
    change ((slicedRoundTrace groups rounds initial).2.push _).size=_
    rw [Array.size_push,ih]

/-- Every retained production pre-chi entry is the linear layer of its exact chronological predecessor. -/
theorem slicedRoundTrace_get (groups rounds : Nat) (initial : Array UInt64) (k : Nat) (hk : k<rounds) :
    (slicedRoundTrace groups rounds initial).2[k+1]! =linearSlices (slicedRoundTrace groups k initial).1 groups := by
  induction rounds with
  | zero => omega
  | succ rounds ih =>
    rw [slicedRoundTrace_succ]
    change ((slicedRoundTrace groups rounds initial).2.push (linearSlices (slicedRoundTrace groups rounds initial).1 groups))[k+1]! = _
    by_cases heq : k=rounds
    · subst k
      rw [← slicedRoundTrace_size groups rounds initial,array_push_get_last]
    · rw [array_push_get_old _ _ _ (by rw [slicedRoundTrace_size]; omega),ih (by omega)]

/-- Chronological bit-level execution with the native round-number convention. -/
def chronologicalState (initial : Fin 1600 → ZMod 2) : Nat → Fin 1600 → ZMod 2
  | 0 => initial
  | n+1 => Gkr.round ⟨n%24,Nat.mod_lt _ (by decide)⟩ (chronologicalState initial n)

/-- All native sliced state bits agree with chronological bit-level execution. -/
theorem slicedRoundTrace_bit (groups rounds : Nat) (initial : Array UInt64) (hr : rounds≤24)
    (group : Nat) (hg : group<groups) (b : Fin 64) (j : Fin 1600) :
    sliceBit (slicedRoundTrace groups rounds initial).1[j.val*groups+group]! b =
      chronologicalState (fun k => sliceBit initial[k.val*groups+group]! b) rounds j := by
  induction rounds generalizing j with
  | zero => rfl
  | succ rounds ih =>
    rw [slicedRoundTrace_succ]
    change sliceBit (chiSlices (linearSlices (slicedRoundTrace groups rounds initial).1 groups) groups rounds)[j.val*groups+group]! b = _
    rw [roundSlices_eq _ hg (⟨rounds,by omega⟩ : Fin 24) j b]
    change Gkr.round ⟨rounds,by omega⟩ _ j=Gkr.round ⟨rounds%24,by omega⟩ _ j
    have heq : (⟨rounds,by omega⟩ : Fin 24)=⟨rounds%24,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega)).symm
    rw [heq]
    apply congrArg (fun state => Gkr.round ⟨rounds%24,by omega⟩ state j)
    funext k
    exact ih (by omega) k

/-- The first twelve chronological rounds are the first protocol segment. -/
theorem chronologicalState_first {p : Nat} (q : Witness p) (b : Fin (2^(p+4))) (n : Nat) (hn : n≤12) :
    chronologicalState (startState q b 0) n=segmentState q b 0 n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chronologicalState,segmentState,ih (by omega)]
    apply congrArg (fun r : Fin 24 => Gkr.round r (segmentState q b 0 n (by omega)))
    apply Fin.ext
    simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_add,Nat.mod_eq_of_lt (by omega : n<24)]

/-- The second twelve chronological rounds are the second protocol segment when their committed boundary matches. -/
theorem chronologicalState_second {p : Nat} (q : Witness p) (b : Fin (2^(p+4)))
    (hchain : ∀ j,segmentState q b 0 12 (by omega) j=startState q b 1 j)
    (n : Nat) (hn : n≤12) :
    chronologicalState (startState q b 0) (12+n)=segmentState q b 1 n hn := by
  induction n with
  | zero => exact (chronologicalState_first q b 12 (by decide)).trans (funext hchain)
  | succ n ih =>
    rw [show 12+(n+1)=(12+n)+1 by omega,chronologicalState,segmentState,ih (by omega)]
    apply congrArg (fun r : Fin 24 => Gkr.round r (segmentState q b 1 n (by omega)))
    apply Fin.ext
    simp only [Fin.val_one,Nat.mul_one,Nat.mod_eq_of_lt (by omega : 12+n<24)]

/-- Native witness construction preserves its declared logarithmic instance count. -/
theorem buildWitness_nLog (nLog : Nat) (committed : Array UInt64) : (buildWitness nLog committed).nLog=nLog := rfl


/-- Padded permutation indices select a valid group of sixty-four sliced instances. -/
theorem slicedInstance_group {h : Nat} (b : Fin (2^(h+8))) : b.val/64<2^(h+8)/64 := by
  have hp : 2^(h+8)=2^(h+2)*64 := by rw [show h+8=(h+2)+6 by omega,pow_add]; rfl
  have hg : 2^(h+8)/64=2^(h+2) := by rw [hp,Nat.mul_div_cancel _ (by decide)]
  rw [hg,Nat.div_lt_iff_lt_mul (by decide)]
  exact b.isLt.trans_eq hp

/-- Initial native slices are exactly the first committed segment's starting state. -/
theorem slicedInitial_start {h : Nat} (committed : Array UInt64) (b : Fin (2^(h+8))) (j : Fin 1600) :
    sliceBit (slicedInitial (h+8) committed)[j.val*(2^(h+8)/64)+b.val/64]! ⟨b.val%64,by omega⟩ =
      startState (committedWitness (h+4) committed) b 0 j := by
  have hh := slicedInitial_bit (h+8) committed (⟨j.val/64,by omega⟩ : Fin 25)
    ⟨j.val%64,by omega⟩ ⟨b.val%64,by omega⟩ (b.val/64) (slicedInstance_group b)
  have hj : 64*(j.val/64)+j.val%64=j.val := by omega
  have hb : j.val/64*2^(h+8)+64*(b.val/64)+b.val%64=j.val/64*2^(h+8)+b.val := by omega
  simpa only [hj,hb,startState,committedWitness,Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hh

/-- Every pre-chi slice produced by the native witness builder refines its committed segment state. -/
theorem buildWitness_preChiRefines {h : Nat} (committed : Array UInt64)
    (hchain : ∀ b j,segmentState (committedWitness (h+4) committed) b 0 12 (by omega) j=
      startState (committedWitness (h+4) committed) b 1 j) :
    PreChiRefines (buildWitness (h+8) committed) (committedWitness (h+4) committed) := by
  intro d m b i j
  rw [buildWitness_nLog,buildWitness_layers]
  let permutation := packInstance i b
  let bit : Fin 64 := ⟨16*(b.val%4)+i.val,by omega⟩
  let k := 12*m.val+(11-d.val)
  have hk : k<24 := by dsimp only [k]; have := m.isLt; have := d.isLt; omega
  have hindex : 12*(m.val+1)-d.val=k+1 := by dsimp only [k]; have := d.isLt; omega
  have hgroup : permutation.val/64=b.val/4 := by dsimp only [permutation,packInstance]; have := i.isLt; omega
  have hbit : permutation.val%64=bit.val := by dsimp only [permutation,packInstance,bit]; have := i.isLt; omega
  have hg : b.val/4<2^(h+8)/64 := by rw [← hgroup]; exact slicedInstance_group permutation
  have hstart : (fun pos : Fin 1600 => sliceBit (slicedInitial (h+8) committed)[pos.val*(2^(h+8)/64)+b.val/4]! bit)=
      startState (committedWitness (h+4) committed) permutation 0 := by
    funext pos
    rw [← hgroup]
    have heq : bit=(⟨permutation.val%64,by omega⟩ : Fin 64) := Fin.ext hbit.symm
    rw [heq]
    exact slicedInitial_start committed permutation pos
  rw [hindex,slicedRoundTrace_get _ 24 _ k hk,linearSlices_eq _ hg j bit]
  apply congrArg (fun state => linear state j)
  funext pos
  rw [slicedRoundTrace_bit _ k _ (by omega) _ hg bit pos,hstart]
  have hm : m=0 ∨ m=1 := by have := m.isLt; omega
  rcases hm with hm | hm
  · subst m
    simpa only [k,Fin.val_zero,Nat.mul_zero,Nat.zero_add] using
      congrFun (chronologicalState_first (committedWitness (h+4) committed) permutation (11-d.val) (by omega)) pos
  · subst m
    exact congrFun (chronologicalState_second _ permutation (hchain permutation) (11-d.val) (by omega)) pos


end CompStark.Keccak.GkrProver
