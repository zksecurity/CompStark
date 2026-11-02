/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Answers
public import CompStark.Ni.QueryBound
public import CompStark.Ni.BcsRun

/-! # The verifier's transcript schedule

* `inputs P A vk pis proof`: the transcript schedule, the elements the verifier observes before
  each squeeze: the STARK's domain separator, the trace commitment and the public values; the
  quotient commitment and the out-of-domain grinding witness; the PCS's domain separator, the
  opened values and the batching grinding witness; each commit-phase commitment with its
  grinding witness, the first after FRI's domain separator; the final polynomial and the query
  grinding witness. A grinding witness is not observed without grinding (`witnessInput`).
* `parse`: a duplex call read back from the queries made before it, by following capacities to
  the initial one (`answering`, `stepsTo`): each capacity was answered by the call of the round
  before. This gives the call's history (each earlier round's input and answered samples) and its
  own input.
* `out`: the result and the query log of a run of the verifier's monad on logged answers.
* `roundValues`, `pcsCounts`: the values and counts the PCS observes, round by round.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type}

/-! ### Domain separators in the schedule -/

/-- A grinding witness as the verifier observes it: not at all without grinding. -/
def witnessInput (bits : Nat) (w : F) : List F := if bits = 0 then [] else [w]

/-- `seed` observed before the first of `blocks`. -/
def prependSeed (seed : List F) : List (List F) → List (List F)
  | [] => [seed]
  | b :: bs => (seed ++ b) :: bs

/-! ### The preprocessed shape -/

/-- The preprocessed round of an opening in the verifier's shape: present with the key, opened at
the next row exactly when the AIR reads it. -/
theorem preprocessedRound_cases {EF : Type} (A : Air F) (vk : Option (PreprocessedKey F))
    (o : OpenedValues EF) (db : Nat) (hshape : preprocessedShapeOk A vk o db = true) (d : Fri.Domain F)
    (zeta zetaNext : EF) :
    (vk = none ∧ o.preprocessedLocal = none ∧ o.preprocessedNext = none ∧
      preprocessedRound A vk o d zeta zetaNext = []) ∨
    ∃ k l, vk = some k ∧ o.preprocessedLocal = some l ∧
      preprocessedRound A vk o d zeta zetaNext =
        [(k.commit, [(d, (zeta, l.toList) ::
          ((o.preprocessedNext.map fun r ↦ (zetaNext, r.toList)).toList))])] := by
  rcases o with ⟨tl, tn, pl, pn, qc⟩
  match vk, pl, pn, hshape with
  | none, none, none, _ => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | some k, some l, none, h =>
    simp only [preprocessedShapeOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      at h
    refine Or.inr ⟨k, l, rfl, rfl, ?_⟩
    simp only [preprocessedRound, h.2, Bool.false_eq_true, ↓reduceIte, Option.getD_some,
      Option.map_none, Option.toList_none]
  | some k, some l, some r, h =>
    simp only [preprocessedShapeOk, Bool.and_eq_true] at h
    refine Or.inr ⟨k, l, rfl, rfl, ?_⟩
    simp only [preprocessedRound, h.2.1, ↓reduceIte, Option.getD_some, Option.map_some,
      Option.toList_some]
  | none, some _, _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  | none, none, some _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  | some _, none, _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h

/-- An opening in the verifier's preprocessed shape holds rows of the AIR's widths, and its claim
counts are the AIR's. -/
theorem prep_of_shapeOk {EF : Type} {A : Air F} {vk : Option (PreprocessedKey F)}
    {o : OpenedValues EF} {db : Nat} (h : preprocessedShapeOk A vk o db = true) :
    (o.preprocessedLocal.getD #[]).size = A.preprocessedWidth ∧
      (o.preprocessedNext.getD #[]).size = A.preprocessedNextWidth ∧
      (o.preprocessedLocal.map fun l ↦
          [l.size :: (o.preprocessedNext.map (·.size)).toList]).toList =
        if A.preprocessedWidth = 0 then [] else
          [[A.preprocessedWidth ::
            if A.opensPreprocessedNext then [A.preprocessedWidth] else []]] := by
  rcases o with ⟨tl, tn, pl, pn, qc⟩
  match vk, pl, pn, h with
  | none, none, none, h =>
    simp only [preprocessedShapeOk, beq_iff_eq] at h
    have hn : A.preprocessedNextWidth = 0 := by
      have := A.preprocessedNextWidth_le; omega
    simp only [Option.getD_none, Array.size_empty, h, hn, Option.map_none, Option.toList_none,
      ↓reduceIte, and_self]
  | some k, some l, none, h =>
    simp only [preprocessedShapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨⟨⟨h0, -⟩, -⟩, hl⟩, hn⟩ := h
    have hnw : A.preprocessedNextWidth = 0 := by
      simp only [Air.preprocessedNextWidth, hn, Bool.false_eq_true, ↓reduceIte]
    simp only [Option.getD_some, hl, Option.getD_none, Array.size_empty, hnw, Option.map_some,
      Option.map_none, Option.toList_none, Option.toList_some, Nat.pos_iff_ne_zero.mp h0,
      ↓reduceIte, hn, Bool.false_eq_true, and_self]
  | some k, some l, some r, h =>
    simp only [preprocessedShapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h0, -⟩, -⟩, hl⟩, hn, hr⟩ := h
    have hnw : A.preprocessedNextWidth = A.preprocessedWidth := by
      simp only [Air.preprocessedNextWidth, hn, ↓reduceIte]
    simp only [Option.getD_some, hl, hr, hnw, Option.map_some, Option.toList_some,
      Nat.pos_iff_ne_zero.mp h0, ↓reduceIte, hn, and_self]
  | none, some _, _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  | none, none, some _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  | some _, none, _, h => simp only [preprocessedShapeOk, Bool.false_eq_true] at h

variable [BaseField F] {EF : Type} [Challenge F EF]

/-! ### The transcript schedule -/

/-- Extension elements as base elements, lowest coefficient first. -/
def coeffs (xs : List EF) : List F := xs.flatMap Ext.coeffs

/-- The opened values in the order the verifier observes them: the trace at `ζ` and `ζ ω` if
opened, every quotient chunk, and the preprocessed trace at `ζ` and `ζ ω` if opened. -/
def openedValues (o : OpenedValues EF) : List EF :=
  o.traceLocal.toList ++ (o.traceNext.getD #[]).toList ++
    o.quotientChunks.toList.flatMap (·.toList) ++
    (o.preprocessedLocal.getD #[]).toList ++ (o.preprocessedNext.getD #[]).toList

/-- The claimed evaluation counts of a proof's openings: the trace at one or two points, every
quotient chunk at one, and the preprocessed trace, if opened, at one or two. -/
def pcsCounts (o : OpenedValues EF) : List (List (List Nat)) :=
  [[o.traceLocal.size :: (o.traceNext.map (·.size)).toList],
    o.quotientChunks.toList.map fun ch ↦ [ch.size]] ++
    (o.preprocessedLocal.map fun l ↦ [l.size :: (o.preprocessedNext.map (·.size)).toList]).toList

theorem claimCounts_openingRounds (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (zeta : EF) (htn : traceNextOk A proof.opened = true)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    Fri.claimCounts (openingRounds A vk proof zeta) = pcsCounts proof.opened := by
  unfold openingRounds
  dsimp only
  rw [traceOpenings_eq htn]
  have htc : ((proof.opened.traceNext.map fun r ↦
      (zeta * Ext.ofBase (twoAdicGen proof.degreeBits), r.toList)).toList.map
        fun x ↦ x.2.length) = (proof.opened.traceNext.map (·.size)).toList := by
    cases proof.opened.traceNext <;> rfl
  rcases preprocessedRound_cases A vk proof.opened _ hshape ⟨1, proof.degreeBits⟩ zeta
    (zeta * Ext.ofBase (twoAdicGen proof.degreeBits)) with ⟨-, hl, hn, hr⟩ | ⟨k, l, -, hl, hr⟩
  · simp only [Fri.claimCounts, pcsCounts, hr, hl, List.map_cons, List.map_nil, List.map_map,
      Array.length_toList, Option.map_none, Option.toList_none, List.append_nil, htc]
    rfl
  · simp only [Fri.claimCounts, pcsCounts, hr, hl, List.map_cons, List.map_nil, List.map_map,
      Array.length_toList, Option.map_some, Option.toList_some, List.cons_append,
      List.nil_append, htc]
    refine congrArg (List.cons _) (congrArg₂ (fun a b ↦ a :: b) rfl ?_)
    cases proof.opened.preprocessedNext <;> rfl

/-- The elements the verifier observes on `proof` before each squeeze, round by round: the
STARK's domain separator, the trace commitment, the preprocessed commitment of the verifying key
`vk` and the public values; the quotient commitment
and the out-of-domain grinding witness; the PCS's domain separator, the opened values and the
batching grinding witness; each commit-phase commitment with its grinding witness, the first
after FRI's domain separator; the final polynomial and the query grinding witness. A grinding
witness is not observed without grinding. -/
def inputs (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F)) (pis : List F)
    (proof : Proof F EF) : List (List F) :=
  (starkSeedOf EF P A proof.degreeBits ++ capElems proof.traceCommit ++ preprocessedDigest vk ++
    pis) ::
  (capElems proof.quotientCommit ++ witnessInput P.oodPowBits proof.oodWitness) ::
  (DomainSeparator.pcsSeed F EF (pcsCounts proof.opened) P.batchPowBits ++
    coeffs (openedValues proof.opened) ++ witnessInput P.batchPowBits proof.fri.batchWitness) ::
  prependSeed (friSeedOf P proof)
    (((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      capElems cw.1 ++ witnessInput P.commitPowBits cw.2) ++
    [coeffs proof.fri.finalPoly.toList ++ witnessInput P.queryPowBits proof.fri.queryWitness])

/-! ### The duplex chain of a schedule -/

variable {K : Nat} (answer : (q : Query F) → Answer K q)

/-- A round of a duplex chain: its input and the samples answered. -/
abbrev Step (F : Type) (K : Nat) := List F × Vector F K

/-! ### Parsing -/

/-- The first duplex call in `log` answering capacity `cap`: its capacity, input and samples. -/
def answering (log : QueryLog (spec F K)) (cap : Digest F) : Option (Digest F × Step F K) :=
  log.findSome? fun e ↦ match e with
    | ⟨.duplex c input, answer⟩ => if answer.1 = cap then some (c, input, answer.2) else none
    | _ => none

/-- The rounds that led to capacity `cap` in `log`, oldest first, following capacities back to
the initial one in at most `fuel` steps. -/
def stepsTo (log : QueryLog (spec F K)) : Nat → Digest F → Option (List (Step F K))
  | fuel, cap =>
    if cap = initCap then some [] else
      match fuel with
      | 0 => none
      | fuel + 1 => match answering log cap with
        | some (c, step) => (stepsTo log fuel c).map (· ++ [step])
        | none => none

/-- A duplex call parsed against the queries `log` before it: the rounds before it and its
input. -/
def parse (log : QueryLog (spec F K)) : Query F → Option (List (Step F K) × List F)
  | .duplex cap input => (stepsTo log log.length cap).map (·, input)
  | _ => none

variable {answer}

variable {log : QueryLog (spec F K)} {blocks : List (List F)} {i : Nat}

/-! ### The verifier's run on logged answers -/

section Run
open CompStark.Fri

variable (answer : (q : Query F) → Answer K q) {P : Fri.Params}

local notation "Hl" => idealLogged answer

/-- The result and the query log of `x` from state `s`, on the logged answers. -/
def out {α : Type} (x : M Hl α) (s : Sponge F) :
    Except String (α × Sponge F) × QueryLog (spec F K) :=
  ((x.run s).run).run

variable {answer}

theorem coeffs_ne_nil {xs : List EF} (h : xs ≠ []) : coeffs xs ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [coeffs, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and_or]
  refine Or.inl (List.ne_nil_of_length_pos ?_)
  rw [Ext.coeffs, Challenge.length_coeffs]
  exact (Challenge.params EF).d_pos

theorem toElems_ne_nil (bs : List UInt8) : DomainSeparator.toElems F bs ≠ [] := by
  simp only [DomainSeparator.toElems, ne_eq, reduceCtorEq, not_false_eq_true]

theorem pcsSeed_ne_nil (counts : List (List (List Nat))) (bits : Nat) :
    DomainSeparator.pcsSeed F EF counts bits ≠ [] := toElems_ne_nil _

/-- The values of the rounds of a commitment scheme opening, in order. -/
def roundValues (rounds : List (Fri.Round F EF)) : List EF :=
  rounds.flatMap fun r ↦ r.2.flatMap fun m ↦ m.2.flatMap (·.2)

theorem heights_openingRounds (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (zeta : EF) :
    ((((openingRounds A vk proof zeta).flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [proof.degreeBits + P.logBlowup] := by
  refine Fri.dedup_mergeSort_const _ _ _ (fun x hx ↦ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simp only [openingRounds, List.cons_append, List.nil_append, List.flatMap_cons,
      List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap] at hy
    rcases hy with rfl | ⟨ch, -, rfl⟩ | ⟨r, hr, hy⟩
    · rfl
    · rfl
    · unfold preprocessedRound at hr
      split at hr
      · rw [List.mem_singleton] at hr
        subst hr
        rw [List.mem_singleton] at hy
        rw [hy]
      · exact absurd hr List.not_mem_nil
  · simp only [openingRounds, List.flatMap_cons, List.map_append, List.map_cons, ne_eq,
      List.cons_append, reduceCtorEq, not_false_eq_true]

theorem roundValues_openingRounds (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (zeta : EF) (htn : traceNextOk A proof.opened = true)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    roundValues (openingRounds A vk proof zeta) = openedValues proof.opened := by
  unfold openingRounds
  dsimp only
  rw [traceOpenings_eq htn]
  have htv : ((proof.opened.traceNext.map fun r ↦
      (zeta * Ext.ofBase (twoAdicGen proof.degreeBits), r.toList)).toList.flatMap (·.2)) =
        (proof.opened.traceNext.getD #[]).toList := by
    cases proof.opened.traceNext <;>
      simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        List.flatMap_nil, List.flatMap_cons, List.append_nil, Option.getD_none, Option.getD_some,
        Array.toList_empty]
  rcases preprocessedRound_cases A vk proof.opened _ hshape ⟨1, proof.degreeBits⟩ zeta
    (zeta * Ext.ofBase (twoAdicGen proof.degreeBits)) with ⟨-, hl, hn, hr⟩ | ⟨k, l, -, hl, hr⟩
  · simp only [roundValues, openedValues, hr, hl, hn, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_map, List.append_nil, List.append_assoc, Option.getD_none, Array.toList_empty,
      htv]
  · simp only [roundValues, openedValues, hr, hl, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_map, List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
      Option.getD_some, htv]
    cases proof.opened.preprocessedNext <;>
      simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        List.flatMap_nil, List.flatMap_cons, List.append_nil, Option.getD_none, Option.getD_some,
        Array.toList_empty]

end Run

end CompStark.Ni
