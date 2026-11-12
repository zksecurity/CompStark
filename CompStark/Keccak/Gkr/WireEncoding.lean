/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.LayerSequence

/-! # Injective transcript encodings and their adaptive execution -/

set_option maxHeartbeats 800000
@[expose] public section
open OracleComp
namespace CompStark.Keccak.Gkr

/-- Fixed-length injective blocks remain injective when concatenated in coordinate order. -/
theorem flatten_ofFn_injective {α β : Type} (encode : α → List β) (len : Nat)
    (length : ∀ a, (encode a).length = len) (inj : Function.Injective encode) (n : Nat) :
    Function.Injective (fun a : Fin n → α => (List.ofFn fun i => encode (a i)).flatten) := by
  induction n with
  | zero => intro a b _; exact funext fun i => i.elim0
  | succ n ih =>
    intro a b h
    simp only [List.ofFn_succ,List.flatten_cons] at h
    have hh := List.append_inj h (by rw [length,length])
    have h0 := inj hh.1
    have ht := ih hh.2
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

/-- A sumcheck block uses exactly two wire moves per round. -/
theorem roundMessages_length {E : Type} {n d : Nat}
    (polys : Fin n → Sumcheck.CompressedMessage E d) (point : Fin n → E) :
    (roundMessages polys point).length = 2*n := by
  simp [roundMessages,List.length_flatten,List.sum_ofFn,Nat.mul_comm]

/-- A sumcheck encoding determines every coefficient and challenge. -/
theorem roundMessages_injective {E : Type} {n d : Nat}
    {a b : Fin n → Sumcheck.CompressedMessage E d} {r s : Fin n → E}
    (h : roundMessages a r = roundMessages b s) : a = b ∧ r = s := by
  let encode := fun pair : Sumcheck.CompressedMessage E d × E => [List.ofFn (messageVector pair.1),[pair.2]]
  have hinj : Function.Injective encode := by
    intro x y h
    have hh := List.cons.inj h
    have he := messageVector_injective (List.ofFn_injective hh.1)
    have hr : x.2 = y.2 := by simpa only [List.cons.injEq,List.nil_eq, and_true] using hh.2
    exact Prod.ext he hr
  have he := flatten_ofFn_injective encode 2 (fun _ => rfl) hinj n
    (a₁ := fun i => (a i,r i)) (a₂ := fun i => (b i,s i)) h
  constructor
  · exact funext fun i => congrArg Prod.fst (congrFun he i)
  · exact funext fun i => congrArg Prod.snd (congrFun he i)

/-- Every layer has the same fixed wire length. -/
theorem layerMessages_length {E : Type} {p : Nat} (t : LayerTranscript E p) :
    (layerMessages t).length = 2*p+28 := by
  simp only [layerMessages,List.length_append,List.length_cons,List.length_nil,roundMessages_length]
  omega

/-- The layer encoding determines all of its messages and challenges. -/
theorem layerMessages_injective {E : Type} {p : Nat} :
    Function.Injective (@layerMessages E p) := by
  intro a b h
  simp only [layerMessages,List.append_assoc,List.cons_append,List.nil_append] at h
  have h0 := List.cons.inj h
  have hp := List.ofFn_injective h0.1
  have h1 := List.cons.inj h0.2
  have hs : a.point = b.point := by simpa only [List.cons.injEq,and_true] using h1.1
  have h2 := List.append_inj h1.2 (by rw [roundMessages_length,roundMessages_length])
  have hpack := roundMessages_injective h2.1
  have h3 := List.append_inj h2.2 (by rw [roundMessages_length,roundMessages_length])
  have hpos := roundMessages_injective h3.1
  have h4 := List.cons.inj h3.2
  have he := List.ofFn_injective h4.1
  have hb : a.beta = b.beta := by simpa only [List.cons.injEq,and_true] using h4.2
  cases a; cases b
  cases hp; cases hs; cases hpack.1; cases hpack.2; cases hpos.1; cases hpos.2; cases he; cases hb
  rfl

/-- A complete sequence of layer encodings determines every layer transcript. -/
theorem sequenceMessages_injective {E : Type} {p n : Nat} :
    Function.Injective (@sequenceMessages E p n) :=
  flatten_ofFn_injective layerMessages (2*p+28) layerMessages_length layerMessages_injective n

/-- The full wire encoding determines the typed GKR transcript. -/
theorem transcriptMessages_injective {E : Type} {p : Nat} :
    Function.Injective (@transcriptMessages E p) := by
  intro a b h
  simp only [transcriptMessages,List.append_assoc,List.cons_append,List.nil_append] at h
  have h0 := List.append_inj h (by simp only [List.length_ofFn])
  have hi : a.instancePoint = b.instancePoint := by
    have he := List.ofFn_injective h0.1
    funext i
    simpa only [List.cons.injEq,and_true] using congrFun he i
  have h1 := List.cons.inj h0.2
  have hs : a.segment = b.segment := by simpa only [List.cons.injEq,and_true] using h1.1
  have h2 := List.append_inj h1.2 (by simp only [List.length_ofFn])
  have hl : a.lanePoint = b.lanePoint := by
    have he := List.ofFn_injective h2.1
    funext i
    simpa only [List.cons.injEq,and_true] using congrFun he i
  have h3 := List.cons.inj h2.2
  have hm : a.middleValue = b.middleValue := by simpa only [List.cons.injEq,and_true] using h3.1
  have hlen (t : Transcript E p) : ((List.ofFn fun d => layerMessages (t.layers d)).flatten).length =
      12*(2*p+28) := by
      simp only [List.length_flatten,List.map_ofFn,Function.comp_def,layerMessages_length,List.ofFn_const,List.sum_replicate]
      simp only [smul_eq_mul]
  have h4 := List.append_inj h3.2 (by rw [hlen,hlen])
  have hls := sequenceMessages_injective h4.1
  have h5 := List.append_inj h4.2 (by rw [roundMessages_length,roundMessages_length])
  have ho := roundMessages_injective h5.1
  have h6 := List.cons.inj h5.2
  have hov : a.openings.outputValue = b.openings.outputValue := by
    simpa only [List.cons.injEq,and_true] using h6.1
  have h7 := List.append_inj h6.2 (by rw [roundMessages_length,roundMessages_length])
  have hip := roundMessages_injective h7.1
  have hsl : a.openings.slices = b.openings.slices := by
    apply List.ofFn_injective
    simpa only [List.cons.injEq,and_true] using h7.2
  have hop : a.openings = b.openings := by
    have ext (o1 o2 : OpeningTranscript E)
        (h1 : o1.outputPolys = o2.outputPolys) (h2 : o1.outputPoint = o2.outputPoint)
        (h3 : o1.outputValue = o2.outputValue) (h4 : o1.inputPolys = o2.inputPolys)
        (h5 : o1.inputPoint = o2.inputPoint) (h6 : o1.slices = o2.slices) : o1 = o2 := by
      cases o1; cases o2
      cases h1; cases h2; cases h3; cases h4; cases h5; cases h6
      rfl
    exact ext _ _ ho.1 ho.2 hov hip.1 hip.2 hsl
  cases a; cases b
  cases hi; cases hs; cases hl; cases hm; cases hls; cases hop
  rfl

/-- The typed layer sampler encodes exactly the concrete public wire block. -/
theorem runLayer_encoding {E : Type} [Fintype E] [Nonempty E] [Zero E] (p d : Nat)
    (prover : Prover E) (history : List (List E)) :
    layerMessages <$> runLayer E p prover history = runWire E prover (layerSteps p d) history := by
  simp only [layerSteps,runWire_append,runWire,pure_bind]
  simp_rw [← runSumcheck_encoding]
  simp only [runLayer,runPack,runPosition,runBeta,layerMessages,map_eq_bind_pure_comp,
    Function.comp_def,bind_assoc,pure_bind,List.append_assoc]

/-- A sequence sampler encodes the corresponding consecutive public layer blocks. -/
theorem runLayerSequence_encoding {E : Type} [Fintype E] [Nonempty E] [Zero E]
    (p n start : Nat) (prover : Prover E) (history : List (List E)) :
    sequenceMessages <$> runLayerSequence E p prover n history =
      runWire E prover ((List.range n).flatMap fun i => layerSteps p (start+i)) history := by
  induction n generalizing start history with
  | zero => simp only [runLayerSequence,map_pure,sequenceMessages,List.ofFn_zero,List.flatten_nil,
      List.range_zero,List.flatMap_nil,runWire]
  | succ n ih =>
    simp only [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
    rw [runWire_append,← runLayer_encoding]
    simp only [runLayerSequence,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,
      sequenceMessages_cons]
    congr 1
    funext t
    have he := ih (start+1) (history ++ layerMessages t)
    have hi : (fun i => layerSteps p (start+(i+1))) = (fun i => layerSteps p (start+1+i)) := by
      funext i; congr 1; omega
    simp only [hi]
    simp only [map_eq_bind_pure_comp,Function.comp_def] at he
    rw [← he]
    simp only [bind_assoc,pure_bind]

end CompStark.Keccak.Gkr
