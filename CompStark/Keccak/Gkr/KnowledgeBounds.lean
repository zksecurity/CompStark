/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgePhases

/-! # Composition of fixed-prefix bounds along the concrete GKR schedule -/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
@[expose] public section
open OracleComp
open scoped ENNReal
namespace CompStark.Keccak.Gkr

/-- A challenge's local bound applies at every authored prefix at its wire offset. -/
def PrefixBound {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (offset : Nat) (kind : Challenge) (before after : Cut) : Prop :=
  ∀ history : List (List E), history.length = offset →
    (cuts p)[history.length]? = some before → (cuts p)[history.length+1]? = some after →
    Pr{let r ← uniformField E}[¬ prefixClaim x output history q ∧
      prefixClaim x output (history ++ [[r]]) q] ≤ (kind.numerator : ENNReal) / Fintype.card E

/-- Each challenge has its concrete successor cut and its local bound at the current offset. -/
def PrefixBoundChain {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) :
    Nat → List (WireStep × Cut) → Prop
  | _, [] => True
  | offset, (.message _, _) :: rest => PrefixBoundChain x output q (offset+1) rest
  | offset, (.challenge kind, c) :: rest =>
      (∃ after, rest.head?.map Prod.snd = some after ∧ PrefixBound x output q offset kind c after) ∧
      PrefixBoundChain x output q (offset+1) rest

/-- The head of a nonempty sumcheck block is its first message and entering cut. -/
theorem roundNodes_head (count degree : Nat) (kind : Nat → Challenge) (cut : Nat → Cut)
    (tail : List (WireStep × Cut)) :
    (roundNodes count degree kind cut ++ tail).head?.map Prod.snd =
      if count = 0 then tail.head?.map Prod.snd else some (cut 0) := by
  cases count with
  | zero => rfl
  | succ n =>
    simp only [roundNodes, List.range_succ_eq_map, List.flatMap_cons, List.cons_append,
      List.head?_cons, Option.map_some, Nat.add_one_ne_zero, ite_false]

/-- Round blocks compose their per-coordinate bounds with the continuation's bound chain. -/
theorem prefixBoundChain_rounds {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (count degree offset : Nat) (kind : Nat → Challenge) (cut : Nat → Cut)
    (tail : List (WireStep × Cut)) (last : Cut)
    (head : tail.head?.map Prod.snd = some last)
    (valid : PrefixBoundChain x output q (offset+2*count) tail)
    (bounds : ∀ i, i < count → PrefixBound x output q (offset+2*i+1) (kind i) (cut i)
      (if i+1 < count then cut (i+1) else last)) :
    PrefixBoundChain x output q offset (roundNodes count degree kind cut ++ tail) := by
  induction count generalizing offset kind cut with
  | zero => exact valid
  | succ n ih =>
    have he : roundNodes (n+1) degree kind cut =
        [(.message (degree+1), cut 0), (.challenge (kind 0), cut 0)] ++
          roundNodes n degree (fun i => kind (i+1)) (fun i => cut (i+1)) := by
      simp only [roundNodes, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [he, List.append_assoc]
    refine ⟨⟨if 1 < n+1 then cut 1 else last, ?_, ?_⟩, ?_⟩
    · change (roundNodes n degree (fun i => kind (i+1)) (fun i => cut (i+1)) ++ tail).head?.map
        Prod.snd = _
      rw [roundNodes_head, head]
      by_cases hn : n = 0
      · simp only [hn, ite_true, Nat.lt_irrefl, ite_false]
      · simp only [hn, ite_false, show 1 < n+1 by omega, ite_true, Nat.zero_add]
    · exact bounds 0 (by omega)
    · apply ih (offset+1+1) (fun i => kind (i+1)) (fun i => cut (i+1))
      · rw [show offset+1+1+2*n = offset+2*(n+1) by omega]
        exact valid
      · intro i hi
        have hb := bounds (i+1) (by omega)
        simp only [Nat.add_lt_add_iff_right] at hb
        have hoff : offset+1+1+2*i+1 = offset+2*(i+1)+1 := by omega
        rw [hoff]
        exact hb

/-- Consecutive initial coordinates compose their affine collision bounds. -/
theorem prefixBoundChain_initial {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (count offset : Nat) (kind : Nat → Challenge) (tail : List (WireStep × Cut))
    (head : tail.head?.map Prod.snd = some (.start (offset+count)))
    (valid : PrefixBoundChain x output q (offset+count) tail)
    (limit : offset+count ≤ p+10) (numerator : ∀ i, (kind i).numerator = 1) :
    PrefixBoundChain x output q offset
      ((List.range count).map (fun i => (.challenge (kind i), .start (offset+i))) ++ tail) := by
  induction count generalizing offset kind with
  | zero => simpa only [Nat.add_zero, List.range_zero, List.map_nil, List.nil_append] using valid
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons_append, Function.comp_def, Nat.add_zero]
    refine ⟨⟨.start (offset+1), ?_, ?_⟩, ?_⟩
    · cases n with
      | zero => simpa only [List.range_zero, List.map_nil, List.nil_append] using head
      | succ n => simp only [List.range_succ_eq_map, List.map_cons, List.cons_append,
          List.head?_cons, Option.map_some]
    · intro history hlen source target
      simpa only [numerator, Nat.cast_one] using
        prefix_initial_local_bound x output q ⟨offset, by omega⟩ history hlen source target
    · have he : (fun i => (WireStep.challenge (kind i.succ), Cut.start (offset+i.succ))) =
          (fun i => (WireStep.challenge (kind (i+1)), Cut.start (offset+1+i))) := by
        funext i
        congr 2
        omega
      rw [he]
      apply ih (offset+1) (fun i => kind (i+1))
      · rw [show offset+1+n = offset+(n+1) by omega]
        exact head
      · rw [show offset+1+n = offset+(n+1) by omega]
        exact valid
      · omega
      · intro i
        exact numerator (i+1)

/-- One layer composes its product, two cubic sumchecks, and beta bounds. -/
theorem prefixBoundChain_layer {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (d : Fin 12) (tail : List (WireStep × Cut))
    (head : tail.head?.map Prod.snd = some (betaNextCut d))
    (valid : PrefixBoundChain x output q (layerOffset p d+(2*p+28)) tail) :
    PrefixBoundChain x output q (layerOffset p d) (layerNodes p d ++ tail) := by
  simp only [layerNodes, List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨⟨.pack d 0, ?_, ?_⟩, ?_⟩
  · rw [roundNodes_head]
    simp only [Nat.add_one_ne_zero, ite_false]
  · intro history hlen source target
    exact prefix_product_local_bound x output q d history hlen source target
  · apply prefixBoundChain_rounds x output q (p+1) 1 (layerOffset p d+1+1)
      (.packSegment d.val) (.pack d) _ (.position d 0)
    · rw [roundNodes_head]
      rfl
    · have hoff : layerOffset p d+1+1+2*(p+1) = layerOffset p d+(2*p+4) := by omega
      rw [hoff]
      apply prefixBoundChain_rounds x output q 11 2 (layerOffset p d+(2*p+4))
        (.position d.val) (.position d) _ (.position d 11)
      · rfl
      · refine ⟨⟨betaNextCut d, head, ?_⟩, ?_⟩
        · intro history hlen source target
          apply prefix_beta_next_local_bound x output q d history (by omega) source target
        · convert valid using 1
      · intro i hi history hlen source target
        apply prefix_position_local_bound x output q d ⟨i, hi⟩ history hlen source
        by_cases h : i+1 < 11
        · simpa only [h, ite_true] using target
        · have he : i+1 = 11 := by omega
          simpa only [he, Nat.lt_irrefl, ite_false] using target
    · intro i hi history hlen source target
      apply prefix_pack_local_bound x output q d ⟨i, hi⟩ history _ (by omega) source target
      intro t good
      by_cases h : i+1 < p+1
      · simpa only [h, ite_true] using good
      · have he : i+1 = p+1 := by omega
        rw [he]
        exact pack_end_preserving x output q d t (by simpa only [h, ite_false] using good)

/-- The two opening sumchecks compose their quadratic bounds and deterministic message suffixes. -/
theorem prefixBoundChain_openings {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) :
    PrefixBoundChain x output q (wordOffset p)
      (roundNodes 6 1 .outputSlot .word ++ [(.message 1, .wordEnd)] ++
        roundNodes 4 1 .inputLow .input ++ roundNodes 6 1 .inputSlot (fun i => .input (4+i)) ++
        [(.message 64, .inputEnd)]) := by
  simp only [List.append_assoc]
  apply prefixBoundChain_rounds x output q 6 1 (wordOffset p) .outputSlot .word _ .wordEnd
  · rfl
  · change PrefixBoundChain x output q (wordOffset p+2*6+1) _
    have hoff : wordOffset p+2*6+1 = inputOffset p := rfl
    rw [hoff]
    apply prefixBoundChain_rounds x output q 4 1 (inputOffset p) .inputLow .input _ (.input 4)
    · rw [roundNodes_head]
      rfl
    · apply prefixBoundChain_rounds x output q 6 1 (inputOffset p+2*4) .inputSlot
        (fun i => .input (4+i)) _ .inputEnd
      · rfl
      · trivial
      · intro i hi history hlen source target
        apply prefix_input_local_bound x output q ⟨4+i, by omega⟩ history _ (by dsimp only [Fin.val_mk]; omega) source target
        intro t good
        by_cases h : i+1 < 6
        · simpa only [h, ite_true, Nat.add_assoc] using good
        · have he : 4+i+1 = 10 := by omega
          simpa only [h, ite_false, cutHolds, he] using good
    · intro i hi history hlen source target
      apply prefix_input_local_bound x output q ⟨i, by omega⟩ history _ hlen source target
      intro t good
      by_cases h : i+1 < 4
      · simpa only [h, ite_true] using good
      · have he : i+1 = 4 := by omega
        simpa only [cutHolds, he, Nat.lt_irrefl, ite_false] using good
  · intro i hi history hlen source target
    apply prefix_word_local_bound x output q ⟨i, hi⟩ history _ hlen source target
    intro t good
    by_cases h : i+1 < 6
    · simpa only [h, ite_true] using good
    · have he : i+1 = 6 := by omega
      simpa only [cutHolds, he, Nat.lt_irrefl, ite_false] using good

/-- A consecutive suffix of layers composes with the fixed opening continuation. -/
theorem prefixBoundChain_layers {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (count start : Nat) (finish : start+count = 12) (tail : List (WireStep × Cut))
    (head : tail.head?.map Prod.snd = some (.word 0))
    (valid : PrefixBoundChain x output q (wordOffset p) tail) :
    PrefixBoundChain x output q (p+11+(2*p+28)*start)
      ((List.ofFn fun i : Fin count => layerNodes p ⟨start+i.val, by omega⟩).flatten ++ tail) := by
  induction count generalizing start with
  | zero =>
    have hs : start = 12 := by omega
    subst start
    simpa only [List.ofFn_zero, List.flatten_nil, List.nil_append, wordOffset, Nat.mul_comm] using valid
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    apply prefixBoundChain_layer x output q ⟨start, by omega⟩
    · cases n with
      | zero =>
        have hs : start = 11 := by omega
        simpa only [List.ofFn_zero, List.flatten_nil, List.nil_append, betaNextCut,
          show ¬ start+1 < 12 by omega, dite_false] using head
      | succ n =>
        simp only [List.ofFn_succ, List.flatten_cons, layerNodes, List.cons_append,
          List.head?_cons, Option.map_some, betaNextCut, show start+1 < 12 by omega, dite_true,
          Fin.val_zero, Fin.val_succ]
    · have he : (fun i : Fin n => layerNodes p ⟨start+i.succ.val, by omega⟩) =
          (fun i : Fin n => layerNodes p ⟨(start+1)+i.val, by omega⟩) := by
        funext i
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [he]
      have h := ih (start+1) (by omega)
      convert h using 1
      dsimp only [layerOffset]
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- Every authored challenge in the complete annotated schedule has its local bound. -/
theorem scheduleNodes_prefixBoundChain {E : Type} [Field E] [Fintype E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p) :
    PrefixBoundChain x output q 0 (scheduleNodes p) := by
  unfold scheduleNodes
  simp only [List.append_assoc]
  have start : (fun i => (WireStep.challenge (.initialInstance i), Cut.start i)) =
      (fun i => (WireStep.challenge (.initialInstance i), Cut.start (0+i))) := by
    simp only [Nat.zero_add]
  rw [start]
  apply prefixBoundChain_initial x output q (p+4) 0 .initialInstance
  · simp only [List.cons_append, List.nil_append, List.head?_cons, Option.map_some, Nat.zero_add]
  · simp only [Nat.zero_add, List.cons_append, List.nil_append]
    change (∃ after, _ = some after ∧ _) ∧ _
    refine ⟨⟨.start (p+5), ?_, ?_⟩, ?_⟩
    · simp only [List.range_succ_eq_map, List.map_cons, List.cons_append,
        List.head?_cons, Option.map_some, Nat.add_zero]
    · intro history hlen source target
      simpa only [Challenge.numerator, Nat.cast_one] using
        prefix_initial_local_bound x output q ⟨p+4, by omega⟩ history hlen source target
    · change PrefixBoundChain x output q (p+5) _
      apply prefixBoundChain_initial x output q 5 (p+5) .lane
      · rfl
      · change PrefixBoundChain x output q (p+5+5+1) _
        have hoff : p+5+5+1 = p+11+(2*p+28)*0 := by omega
        rw [hoff]
        apply prefixBoundChain_layers x output q 12 0 rfl
        · rw [roundNodes_head]
          rfl
        · exact prefixBoundChain_openings x output q
      · omega
      · intro i
        rfl
  · omega
  · intro i
    rfl

end CompStark.Keccak.Gkr
