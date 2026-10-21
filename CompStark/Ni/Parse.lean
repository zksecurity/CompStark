/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Answers
public import CompStark.Ni.QueryBound
public import CompStark.Ni.BcsRun

/-! # Parsing duplex calls into transcript prefixes

In the random-oracle model every challenge round of the verifier is one duplex call: the
capacity left by the previous round and the elements observed since. A duplex call can be read
back from the queries made before it by following capacities to the initial one (`parse`): each
capacity was answered by the call of the round before. This gives the call's history (each
earlier round's input and answered samples) and its own input.

* `inputs P A vk pis proof`: the transcript schedule, the elements the verifier observes before
  each squeeze: the STARK's domain separator, the trace commitment and the public values; the
  quotient commitment and the out-of-domain grinding witness; the PCS's domain separator, the
  opened values and the batching grinding witness; each commit-phase commitment with its
  grinding witness, the first after FRI's domain separator; the final polynomial and the query
  grinding witness. A grinding witness is not observed without grinding.
* `keyAt answer blocks i`: the duplex call of round `i` when every round is answered by
  `answer`, and `history answer blocks i` the rounds before it, the prefix of round `i`.
* `parse_keyAt`: in a log answered by `answer` whose duplex calls answer distinct capacities,
  none the initial one (`CapsInjective`), and that holds the calls of the rounds before `i`, the
  call of round `i` parses to its history and input.
* `hasRounds_verifyWith`: if the verifier accepts a proof on fixed answers, its log holds the call of every round of the proof's schedule. The proof runs the verifier
  symbolically on the logged answers (`out` and its lemmas), up to the query round.
* `parse_verifyWith`: so, in the verifier's log, round `i`'s call parses to the proof's prefix up
  to round `i`.
* `extAt`, `challengeOffset`: reading the challenges off a round's samples.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type}

/-! ### Consistent logs -/

/-- Every query of `log` is answered by `answer`. -/
def Consistent {K : Nat} (answer : (q : Query F) → Answer K q) (log : QueryLog (spec F K)) : Prop :=
  ∀ e ∈ log, e.2 = answer e.1

/-- A log of answers by `answer` is answered by `answer`. -/
theorem consistent_tableQueryLog {K : Nat} {answer : (q : Query F) → Answer K q} {α : Type}
    (oa : OracleComp (spec F K) α) :
    Consistent answer (tableQueryLog oa answer) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [Consistent, tableQueryLog_pure, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | query_bind t k ih =>
    rw [Consistent, tableQueryLog_query_bind]
    rintro e (_ | ⟨_, he⟩)
    · rfl
    · exact ih _ e he

/-! ### Domain separators in the schedule -/

/-- A grinding witness as the verifier observes it: not at all without grinding. -/
def witnessInput (bits : Nat) (w : F) : List F := if bits = 0 then [] else [w]

/-- The challenges of the rounds, in the order of `inputs`: `α`, `ζ` and the batching challenge
take the first `d` samples of rounds `0`, `1` and `2`; fold `i`'s grinding sample is the first
sample of round `3 + i` and its `β_i` the next `d` (the first `d` without commit grinding); the
query round's grinding sample is its first sample, and the query indices the next ones (from the
first without query grinding). -/
def challengeOffset (bits : Nat) : Nat := if bits = 0 then 0 else 1

theorem length_witnessInput (bits : Nat) (w : F) :
    (witnessInput bits w).length = challengeOffset bits := by
  unfold witnessInput challengeOffset; split <;> rfl

/-- `seed` observed before the first of `blocks`. -/
def prependSeed (seed : List F) : List (List F) → List (List F)
  | [] => [seed]
  | b :: bs => (seed ++ b) :: bs

/-- `seed` before the first fold round, nothing before the others. -/
def seedAt (seed : List F) (k : Nat) : List F := if k = 0 then seed else []

theorem getD_prependSeed (seed : List F) (b : List F) (bs : List (List F)) (k : Nat) :
    (prependSeed seed (b :: bs)).getD k [] = seedAt seed k ++ (b :: bs).getD k [] := by
  cases k with
  | zero => rfl
  | succ k => simp only [prependSeed, List.getD_cons_succ, seedAt, Nat.add_one_ne_zero,
      ↓reduceIte, List.nil_append]

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

/-- The opened values in the order the verifier observes them: the trace at `ζ`, the trace at
`ζ ω`, every quotient chunk, and the preprocessed trace at `ζ` and `ζ ω` if opened. -/
def openedValues (o : OpenedValues EF) : List EF :=
  o.traceLocal.toList ++ o.traceNext.toList ++ o.quotientChunks.toList.flatMap (·.toList) ++
    (o.preprocessedLocal.getD #[]).toList ++ (o.preprocessedNext.getD #[]).toList

/-- The claimed evaluation counts of a proof's openings: the trace at two points, every quotient
chunk at one, and the preprocessed trace, if opened, at one or two. -/
def pcsCounts (o : OpenedValues EF) : List (List (List Nat)) :=
  [[[o.traceLocal.size, o.traceNext.size]], o.quotientChunks.toList.map fun ch ↦ [ch.size]] ++
    (o.preprocessedLocal.map fun l ↦ [l.size :: (o.preprocessedNext.map (·.size)).toList]).toList

theorem claimCounts_openingRounds (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (zeta : EF)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    Fri.claimCounts (openingRounds A vk proof zeta) = pcsCounts proof.opened := by
  unfold openingRounds
  rcases preprocessedRound_cases A vk proof.opened _ hshape ⟨1, proof.degreeBits⟩ zeta
    (zeta * Ext.ofBase (twoAdicGen proof.degreeBits)) with ⟨-, hl, hn, hr⟩ | ⟨k, l, -, hl, hr⟩
  · simp only [Fri.claimCounts, pcsCounts, hr, hl, List.map_cons, List.map_nil, List.map_map,
      Array.length_toList, Option.map_none, Option.toList_none, List.append_nil]
    rfl
  · simp only [Fri.claimCounts, pcsCounts, hr, hl, List.map_cons, List.map_nil, List.map_map,
      Array.length_toList, Option.map_some, Option.toList_some, List.cons_append,
      List.nil_append]
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
  (starkSeedOf EF P A proof.degreeBits ++ proof.traceCommit.toList ++ preprocessedDigest vk ++
    pis) ::
  (proof.quotientCommit.toList ++ witnessInput P.oodPowBits proof.oodWitness) ::
  (DomainSeparator.pcsSeed F EF (pcsCounts proof.opened) P.batchPowBits ++
    coeffs (openedValues proof.opened) ++ witnessInput P.batchPowBits proof.fri.batchWitness) ::
  prependSeed (friSeedOf P proof)
    (((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput P.commitPowBits cw.2) ++
    [coeffs proof.fri.finalPoly.toList ++ witnessInput P.queryPowBits proof.fri.queryWitness])

/-! ### The duplex chain of a schedule -/

variable {K : Nat} (answer : (q : Query F) → Answer K q)

/-- The capacity before round `j` of `blocks` when every round is answered by `answer`. -/
def capAt (blocks : List (List F)) : Nat → Digest F
  | 0 => initCap
  | j + 1 => (answer (.duplex (capAt blocks j) (blocks.getD j []))).1

/-- The duplex call of round `j`. -/
def keyAt (blocks : List (List F)) (j : Nat) : Query F :=
  .duplex (capAt answer blocks j) (blocks.getD j [])

/-- A round of a duplex chain: its input and the samples answered. -/
abbrev Step (F : Type) (K : Nat) := List F × Vector F K

/-- The rounds before round `i`. -/
def history (blocks : List (List F)) (i : Nat) : List (Step F K) :=
  (List.range i).map fun j ↦ (blocks.getD j [], (answer (keyAt answer blocks j)).2)

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

/-- On the duplex calls of `log`, `answer` never gives the initial capacity, and gives distinct
calls distinct capacities. -/
def CapsInjective (log : QueryLog (spec F K)) : Prop :=
  ∀ c input, Query.duplex c input ∈ log.map Sigma.fst →
    (answer (.duplex c input)).1 ≠ initCap ∧
    ∀ c' input', Query.duplex c' input' ∈ log.map Sigma.fst →
      (answer (.duplex c input)).1 = (answer (.duplex c' input')).1 → c = c' ∧ input = input'

variable {answer}

theorem answering_eq (log : QueryLog (spec F K)) (hcons : Consistent answer log)
    (hinj : CapsInjective answer log) (c : Digest F) (input : List F)
    (hmem : Query.duplex c input ∈ log.map Sigma.fst) :
    answering log (answer (.duplex c input)).1 = some (c, input, (answer (.duplex c input)).2) := by
  obtain ⟨e, he, hek⟩ := List.mem_map.mp hmem
  have hsome : answering log (answer (.duplex c input)).1 ≠ none := by
    unfold answering
    rw [ne_eq, List.findSome?_eq_none_iff]
    intro h
    have := h e he
    obtain ⟨q, a⟩ := e
    simp only at hek
    subst hek
    have ha : a = answer (.duplex c input) := hcons _ he
    subst ha
    simp only [↓reduceIte, reduceCtorEq] at this
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hsome
  rw [hr]
  obtain ⟨⟨q, a⟩, hq, hqr⟩ := List.exists_of_findSome?_eq_some hr
  rcases q with ⟨c', input'⟩ | _ | _
  · have ha := hcons _ hq
    simp only at ha
    subst ha
    dsimp only at hqr
    split at hqr
    · rename_i hcap
      obtain ⟨rfl, rfl⟩ := ((hinj c' input' (List.mem_map_of_mem hq)).2 c input hmem hcap)
      rw [← Option.some.inj hqr]
    · exact absurd hqr (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hqr (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd hqr (by simp only [reduceCtorEq, not_false_eq_true])

variable {log : QueryLog (spec F K)} {blocks : List (List F)} {i : Nat}

/-- The calls of the rounds before `i` are in `log`. -/
def HasRounds (answer : (q : Query F) → Answer K q) (log : QueryLog (spec F K))
    (blocks : List (List F)) (i : Nat) : Prop :=
  ∀ j < i, keyAt answer blocks j ∈ log.map Sigma.fst

theorem capAt_ne_initCap (hinj : CapsInjective answer log) (hrounds : HasRounds answer log blocks i)
    (j : Nat) (hj : j < i) : capAt answer blocks (j + 1) ≠ initCap :=
  (hinj _ _ (hrounds j hj)).1

/-- The capacities of the rounds up to `i` are distinct. -/
theorem capAt_injective (hinj : CapsInjective answer log)
    (hrounds : HasRounds answer log blocks i) :
    ∀ j j', j ≤ i → j' ≤ i → capAt answer blocks j = capAt answer blocks j' → j = j'
  | 0, 0, _, _, _ => rfl
  | 0, j' + 1, _, hj', h => absurd h.symm (capAt_ne_initCap hinj hrounds j' (by omega))
  | j + 1, 0, hj, _, h => absurd h (capAt_ne_initCap hinj hrounds j (by omega))
  | j + 1, j' + 1, hj, hj', h => by
    have := ((hinj _ _ (hrounds j (by omega))).2 _ _ (hrounds j' (by omega)) h).1
    rw [capAt_injective hinj hrounds j j' (by omega) (by omega) this]

/-- A log holding the rounds before `i` has at least `i` queries. -/
theorem le_length (hinj : CapsInjective answer log) (hrounds : HasRounds answer log blocks i) :
    i ≤ log.length := by
  have hnodup : ((List.range i).map (keyAt answer blocks)).Nodup := by
    refine List.Nodup.map_on (fun j hj j' hj' h ↦ ?_) List.nodup_range
    rw [List.mem_range] at hj hj'
    simp only [keyAt, Query.duplex.injEq] at h
    exact capAt_injective hinj hrounds j j' hj.le hj'.le h.1
  have hsub : (List.range i).map (keyAt answer blocks) ⊆ log.map Sigma.fst := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact hrounds j (List.mem_range.mp hj)
  have := (hnodup.subperm hsub).length_le
  simpa only [List.length_map, List.length_range] using this

theorem stepsTo_capAt (hcons : Consistent answer log) (hinj : CapsInjective answer log) :
    ∀ i, HasRounds answer log blocks i → ∀ fuel, i ≤ fuel →
      stepsTo log fuel (capAt answer blocks i) = some (history answer blocks i)
  | 0, _, fuel, _ => by
    rw [stepsTo.eq_def]
    simp only [capAt, ↓reduceIte, history, List.range_zero, List.map_nil]
  | i + 1, hrounds, fuel + 1, hfuel => by
    have hne := capAt_ne_initCap hinj hrounds i (by omega)
    rw [stepsTo.eq_def]
    simp only [hne, ↓reduceIte]
    rw [capAt, answering_eq log hcons hinj _ _ (hrounds i (by omega))]
    dsimp only
    rw [stepsTo_capAt hcons hinj i (fun j hj ↦ hrounds j (by omega)) fuel (by omega),
      Option.map_some, history, history, List.range_succ, List.map_append]
    rfl

/-- **Parsing a round's duplex call.** If `log` is answered by `answer`, its duplex calls answer
distinct capacities and none the initial one, and it holds the calls of the rounds before `i`,
then it parses the call of round `i` to the rounds before it and its input. -/
theorem parse_keyAt (hcons : Consistent answer log) (hinj : CapsInjective answer log)
    (hrounds : HasRounds answer log blocks i) :
    parse log (keyAt answer blocks i) = some (history answer blocks i, blocks.getD i []) := by
  rw [keyAt, parse, stepsTo_capAt hcons hinj i hrounds _ (le_length hinj hrounds),
    Option.map_some]

/-! ### The verifier's run on logged answers -/

section Run
open CompStark.Fri

variable (answer : (q : Query F) → Answer K q) {P : Fri.Params}

local notation "Hl" => idealLogged answer

/-- The result and the query log of `x` from state `s`, on the logged answers. -/
def out {α : Type} (x : M Hl α) (s : Sponge F) :
    Except String (α × Sponge F) × QueryLog (spec F K) :=
  ((x.run s).run).run

theorem out_pure {α : Type} (a : α) (s : Sponge F) :
    out answer (pure a : M Hl α) s = (.ok (a, s), []) := rfl

theorem out_bind {α β : Type} (x : M Hl α) (f : α → M Hl β) (s : Sponge F) :
    out answer (x >>= f) s = match out answer x s with
      | (.ok (v, s'), w) => ((out answer (f v) s').1, w ++ (out answer (f v) s').2)
      | (.error e, w) => (.error e, w) := by
  unfold out
  simp only [StateT.run_bind, ExceptT.run_bind, WriterT.run_bind']
  rcases h : (StateT.run x s).run.run with ⟨_ | ⟨v, s'⟩, w⟩
  · change (Except.error _, w ++ []) = _
    rw [List.append_nil]
  · rfl

/-- A computation that succeeds within a bind succeeded first, and logged a prefix. -/
theorem out_bind_ok {α β : Type} {x : M Hl α} {f : α → M Hl β} {s : Sponge F} {r : β × Sponge F}
    (h : (out answer (x >>= f) s).1 = .ok r) :
    ∃ v s', (out answer x s).1 = .ok (v, s') ∧ (out answer (f v) s').1 = .ok r ∧
      (out answer (x >>= f) s).2 = (out answer x s).2 ++ (out answer (f v) s').2 := by
  rw [out_bind] at h ⊢
  rcases hx : out answer x s with ⟨_ | ⟨v, s'⟩, w⟩
  · rw [hx] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · rw [hx] at h
    exact ⟨v, s', rfl, h, rfl⟩

theorem out_modify (f : Sponge F → Sponge F) (s : Sponge F) :
    out answer (modify f : M Hl Unit) s = (.ok ((), f s), []) := rfl

theorem out_throw {α : Type} (e : String) (s : Sponge F) :
    out answer (throw e : M Hl α) s = (.error e, []) := rfl

theorem out_ensure_ok {b : Bool} {msg : String} {s : Sponge F} {r : Unit × Sponge F}
    (h : (out answer (ensure (H := Hl) b msg) s).1 = .ok r) : b = true ∧ r = ((), s) := by
  unfold ensure at h
  split at h
  · exact ⟨by assumption, (Except.ok.inj h).symm⟩
  · exact absurd h (by simp only [out_throw, reduceCtorEq, not_false_eq_true])

/-- A passed check: its condition holds, and the rest runs from the same state. -/
theorem out_ensure_bind_ok {β : Type} {b : Bool} {msg : String} {f : Unit → M Hl β} {s : Sponge F}
    {r : β × Sponge F} (h : (out answer (ensure (H := Hl) b msg >>= f) s).1 = .ok r) :
    b = true ∧ (out answer (f ()) s).1 = .ok r ∧
      (out answer (ensure (H := Hl) b msg >>= f) s).2 = (out answer (f ()) s).2 := by
  obtain ⟨v, s', h₁, h₂, hlog⟩ := out_bind_ok answer h
  obtain ⟨hb, hs⟩ := out_ensure_ok answer h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj hs
  refine ⟨hb, h₂, ?_⟩
  rw [hlog]
  unfold ensure
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  rfl

theorem out_sample_cons (cap : Digest F) (input : List F) (x : F) (rest : List F) :
    out answer (sample Hl) ⟨cap, input, x :: rest⟩ = (.ok (x, ⟨cap, input, rest⟩), []) := rfl

theorem out_sample_nil (cap : Digest F) (input : List F) :
    out answer (sample Hl) ⟨cap, input, []⟩ =
      (.ok (((answer (.duplex cap input)).2.toList.headD 0),
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) := by
  unfold out
  change (Except.ok <$> (Hl).sample ⟨cap, input, []⟩ : WriterT _ Id _).run = _
  simp only [QueryImpl.withLogging_apply, QueryImpl.ofFn_apply]
  rfl

theorem foldl_observe : ∀ (xs : List F) (s : Sponge F),
    xs.foldl (Hl).observe s = if xs = [] then s else ⟨s.cap, s.input ++ xs, []⟩
  | [], _ => rfl
  | x :: xs, s => by
    rw [List.foldl_cons, foldl_observe xs,
      ite_eq_right_of_eq_false _ _ (eq_false (List.cons_ne_nil x xs))]
    split
    · rename_i h
      subst h
      rfl
    · simp only [List.append_assoc, List.singleton_append]

theorem out_observeList (xs : List F) (s : Sponge F) :
    out answer (observeList Hl xs) s =
      (.ok ((), if xs = [] then s else ⟨s.cap, s.input ++ xs, []⟩), []) := by
  rw [observeList, out_modify, foldl_observe]

theorem out_observeList_nil (xs : List F) (cap : Digest F) (input : List F) :
    out answer (observeList Hl xs) ⟨cap, input, []⟩ = (.ok ((), ⟨cap, input ++ xs, []⟩), []) := by
  rw [out_observeList]
  split
  · rename_i h
    rw [h, List.append_nil]
  · rfl

theorem out_observe (x : F) (s : Sponge F) :
    out answer (observe Hl x) s = (.ok ((), ⟨s.cap, s.input ++ [x], []⟩), []) := rfl

theorem foldl_observeExts (xs : List EF) (s : Sponge F) :
    xs.foldl (fun s x ↦ (Ext.coeffs x).foldl (Hl).observe s) s =
      (coeffs xs).foldl (Hl).observe s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [coeffs, List.flatMap_cons, List.foldl_append]

theorem out_observeExts (xs : List EF) (s : Sponge F) :
    out answer (observeExts Hl xs) s =
      (.ok ((), if coeffs xs = [] then s else ⟨s.cap, s.input ++ coeffs xs, []⟩), []) := by
  rw [observeExts, out_modify, foldl_observeExts, foldl_observe]

/-- `n` samples left or more: sampling `n` takes them. -/
theorem out_sampleList_pop (cap : Digest F) (input : List F) :
    ∀ (n : Nat) (samples : List F), n ≤ samples.length →
      out answer (sampleList Hl n) ⟨cap, input, samples⟩ =
        (.ok (samples.take n, ⟨cap, input, samples.drop n⟩), [])
  | 0, _, _ => rfl
  | n + 1, x :: rest, h => by
    simp only [sampleList, out_bind, out_sample_cons,
      out_sampleList_pop cap input n rest (by simp only [List.length_cons] at h; omega), out_pure,
      List.append_nil, List.take_succ_cons, List.drop_succ_cons]

/-- `d` samples left or more: an extension sample takes them. -/
theorem out_sampleExt_pop (cap : Digest F) (input : List F) (samples : List F)
    (h : Challenge.d EF ≤ samples.length) :
    out answer (sampleExt Hl : M Hl EF) ⟨cap, input, samples⟩ =
      (.ok (Challenge.ofCoeffs (samples.take (Challenge.d EF)),
        ⟨cap, input, samples.drop (Challenge.d EF)⟩), []) := by
  simp only [sampleExt, out_bind, out_sampleList_pop answer cap input _ samples h, out_pure,
    List.append_nil]

/-- No samples left: an extension sample duplexes and takes `d` samples of the answer. -/
theorem out_sampleExt_nil (hK : Challenge.d EF ≤ K) (cap : Digest F) (input : List F) :
    out answer (sampleExt Hl : M Hl EF) ⟨cap, input, []⟩ =
      (.ok (Challenge.ofCoeffs ((answer (.duplex cap input)).2.toList.take (Challenge.d EF)),
        ⟨(answer (.duplex cap input)).1, [],
        (answer (.duplex cap input)).2.toList.drop (Challenge.d EF)⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) := by
  obtain ⟨d, hd⟩ : ∃ d, Challenge.d EF = d + 1 :=
    ⟨Challenge.d EF - 1, Nat.succ_pred_eq_of_pos (Challenge.params EF).d_pos |>.symm⟩
  have hlen : d ≤ (answer (.duplex cap input)).2.toList.tail.length := by
    rw [List.length_tail, Vector.length_toList, ← Nat.add_sub_cancel d 1, ← hd]
    exact Nat.sub_le_sub_right hK 1
  simp only [sampleExt, hd, sampleList, out_bind, out_sample_nil,
    out_sampleList_pop answer _ _ d _ hlen, out_pure, List.append_nil]
  rcases hL : (answer (.duplex cap input)).2.toList with _ | ⟨a, rest⟩
  · have := congrArg List.length hL
    rw [Vector.length_toList, List.length_nil] at this
    omega
  · rfl

/-- A loop whose every step from a state satisfying `Inv` yields, keeps `Inv` at the next step
and queries `q` of its step logs `q` of every step. -/
theorem out_forIn_keys {γ β : Type} (f : γ → β → M Hl (ForInStep β)) (q : Nat → Query F)
    (Inv : Nat → Sponge F → Prop) :
    ∀ (l : List γ) (k0 : Nat) (b : β) (s : Sponge F) (r : β × Sponge F),
      (∀ k (hk : k < l.length) b s (r : ForInStep β × Sponge F), Inv (k0 + k) s →
        (out answer (f l[k] b) s).1 = .ok r →
        (∃ b', r.1 = .yield b') ∧ Inv (k0 + k + 1) r.2 ∧
          q (k0 + k) ∈ (out answer (f l[k] b) s).2.map Sigma.fst) →
      Inv k0 s → (out answer (forIn l b f) s).1 = .ok r →
      Inv (k0 + l.length) r.2 ∧
        ∀ k < l.length, q (k0 + k) ∈ (out answer (forIn l b f) s).2.map Sigma.fst
  | [], k0, b, s, r, _, hinv, hok => by
    rw [List.forIn_nil, out_pure] at hok
    rw [← (Except.ok.inj hok)]
    exact ⟨hinv, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
  | a :: l, k0, b, s, r, hstep, hinv, hok => by
    rw [List.forIn_cons] at hok ⊢
    obtain ⟨v, s', h1, h2, hlog⟩ := out_bind_ok answer hok
    obtain ⟨⟨b', hb'⟩, hinv', hq⟩ := hstep 0 (Nat.succ_pos _) b s (v, s') hinv h1
    simp only at hb'
    subst hb'
    have ih := out_forIn_keys f q Inv l (k0 + 1) b' s' r
      (fun k hk b s r hinv hok ↦ by
        have e : k0 + 1 + k = k0 + (k + 1) := by omega
        rw [e] at hinv ⊢
        exact hstep (k + 1) (by simp only [List.length_cons]; omega) b s r hinv hok)
      hinv' h2
    rw [hlog]
    have e : k0 + 1 + l.length = k0 + (a :: l).length := by
      simp only [List.length_cons]; omega
    refine ⟨e ▸ ih.1, fun k hk ↦ ?_⟩
    rw [List.map_append, List.mem_append]
    rcases k with _ | k
    · exact Or.inl hq
    · have e' : k0 + 1 + k = k0 + (k + 1) := by omega
      exact Or.inr (e' ▸ ih.2 k (by simp only [List.length_cons] at hk; omega))

/-- No samples left: a sample of bits duplexes and takes the first sample of the answer. -/
theorem out_sampleBits_nil (bits : Nat) (cap : Digest F) (input : List F) :
    ∃ v, out answer (sampleBits Hl bits) ⟨cap, input, []⟩ =
      (.ok (v, ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) :=
  ⟨_, by simp only [sampleBits, out_bind, out_sample_nil, out_pure, List.append_nil]; rfl⟩

theorem out_checkWitness_zero (w : F) (s : Sponge F) :
    out answer (checkWitness Hl 0 w) s = (.ok (true, s), []) := rfl

/-- With grinding, a witness check observes the witness, duplexes and takes the first sample. -/
theorem out_checkWitness_pos (bits : Nat) (hbits : bits ≠ 0) (w : F) (cap : Digest F)
    (input samples : List F) :
    ∃ v, out answer (checkWitness Hl bits w) ⟨cap, input, samples⟩ =
      (.ok (v, ⟨(answer (.duplex cap (input ++ [w]))).1, [],
        (answer (.duplex cap (input ++ [w]))).2.toList.tail⟩),
        [⟨.duplex cap (input ++ [w]), answer (.duplex cap (input ++ [w]))⟩]) := by
  obtain ⟨v, hv⟩ := out_sampleBits_nil answer bits cap (input ++ [w])
  refine ⟨v == 0, ?_⟩
  simp only [checkWitness, hbits, ↓reduceIte, out_bind, out_observe, hv, out_pure,
    List.append_nil, List.nil_append]

theorem out_forIn_observe {γ : Type} (l : List γ) (f : γ → F) (s : Sponge F) :
    out answer (forIn l PUnit.unit fun a _ ↦ do
      observe Hl (f a)
      pure (ForInStep.yield PUnit.unit)) s =
      (.ok (PUnit.unit, (l.map f).foldl (Hl).observe s), []) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, out_bind]
    simp only [out_bind, out_observe, out_pure, List.nil_append]
    rw [ih]
    rfl

variable {answer}

/-- The keys of the rounds `j` with `lo ≤ j < hi` are in the log `w`. -/
def LogsRounds (answer : (q : Query F) → Answer K q) (blocks : List (List F)) (lo hi : Nat)
    (w : QueryLog (spec F K)) : Prop :=
  ∀ j, lo ≤ j → j < hi → keyAt answer blocks j ∈ w.map Sigma.fst

theorem logsRounds_cons {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec F K)}
    (h₁ : keyAt answer blocks lo ∈ w₁.map Sigma.fst)
    (h₂ : LogsRounds answer blocks (lo + 1) hi w₂) :
    LogsRounds answer blocks lo hi (w₁ ++ w₂) := fun j hlo hhi ↦ by
  rw [List.map_append, List.mem_append]
  rcases Nat.eq_or_lt_of_le hlo with rfl | hlt
  · exact Or.inl h₁
  · exact Or.inr (h₂ j hlt hhi)

theorem logsRounds_append {blocks : List (List F)} {lo mid hi : Nat} {w₁ w₂ : QueryLog (spec F K)}
    (h₁ : LogsRounds answer blocks lo mid w₁) (h₂ : LogsRounds answer blocks mid hi w₂) :
    LogsRounds answer blocks lo hi (w₁ ++ w₂) := fun j hlo hhi ↦ by
  rw [List.map_append, List.mem_append]
  rcases Nat.lt_or_ge j mid with h | h
  · exact Or.inl (h₁ j hlo h)
  · exact Or.inr (h₂ j h hhi)

theorem logsRounds_empty {blocks : List (List F)} {lo hi : Nat} {w : QueryLog (spec F K)}
    (h : hi ≤ lo) : LogsRounds answer blocks lo hi w := fun _ hlo hhi ↦ by omega

theorem logsRounds_right {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec F K)}
    (h₂ : LogsRounds answer blocks lo hi w₂) : LogsRounds answer blocks lo hi (w₁ ++ w₂) :=
  fun j hlo hhi ↦ by
    rw [List.map_append, List.mem_append]
    exact Or.inr (h₂ j hlo hhi)

theorem logsRounds_left {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec F K)}
    (h₁ : LogsRounds answer blocks lo hi w₁) : LogsRounds answer blocks lo hi (w₁ ++ w₂) :=
  fun j hlo hhi ↦ by
    rw [List.map_append, List.mem_append]
    exact Or.inl (h₁ j hlo hhi)

theorem coeffs_ne_nil {xs : List EF} (h : xs ≠ []) : coeffs xs ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [coeffs, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and_or]
  refine Or.inl (List.ne_nil_of_length_pos ?_)
  rw [Ext.coeffs, Challenge.length_coeffs]
  exact (Challenge.params EF).d_pos

theorem toElems_ne_nil (bs : List UInt8) : DomainSeparator.toElems F bs ≠ [] := by
  simp only [DomainSeparator.toElems, ne_eq, reduceCtorEq, not_false_eq_true]

theorem two_le_length_toElems (bs : List UInt8) (h : bs ≠ []) :
    2 ≤ (DomainSeparator.toElems F bs).length := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [DomainSeparator.toElems, List.length_cons, List.length_map, DomainSeparator.chunks,
    DomainSeparator.chunks.go]
  omega

theorem seedBytes_ne_nil (version : Nat) (name : String) (steps : List DomainSeparator.Step)
    (inst : List Nat) : DomainSeparator.seedBytes version name steps inst ≠ [] := by
  simp only [DomainSeparator.seedBytes, List.cons_append, ne_eq, reduceCtorEq, not_false_eq_true]

theorem two_le_length_friSeed (arities : List Nat) (finalLen commitBits queryBits numQueries
    indexBits logBlowup maxLogArity : Nat) : 2 ≤ (DomainSeparator.friSeed F EF arities finalLen
      commitBits queryBits numQueries indexBits logBlowup maxLogArity).length :=
  two_le_length_toElems _ (seedBytes_ne_nil _ _ _ _)

theorem pcsSeed_ne_nil (counts : List (List (List Nat))) (bits : Nat) :
    DomainSeparator.pcsSeed F EF counts bits ≠ [] := toElems_ne_nil _

theorem friSeed_ne_nil (arities : List Nat) (finalLen commitBits queryBits numQueries indexBits
    logBlowup maxLogArity : Nat) : DomainSeparator.friSeed F EF arities finalLen commitBits
      queryBits numQueries indexBits logBlowup maxLogArity ≠ [] := toElems_ne_nil _

/-- FRI's rounds: from the state after the batching challenge, with the capacity of round `r`,
the verifier queries every fold round and the query round. -/
theorem verifyFri_logs (hK : P.numQueries + Challenge.d EF + 1 ≤ K) (blocks : List (List F))
    (r : Nat) (proof : FriProof F EF) (rounds : List (Round F EF)) (alpha : EF) (logMax : Nat)
    (hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [logMax])
    (hfold : ∀ j (hj : j < (proof.commits.toList.zip proof.commitWitnesses.toList).length),
      blocks.getD (r + j) [] = seedAt (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
        P.maxLogArity) j ++
        (proof.commits.toList.zip proof.commitWitnesses.toList)[j].1.toList ++
          witnessInput P.commitPowBits (proof.commits.toList.zip proof.commitWitnesses.toList)[j].2)
    (hlast : blocks.getD (r + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      [] = seedAt (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
        P.maxLogArity) (proof.commits.toList.zip proof.commitWitnesses.toList).length ++
        coeffs proof.finalPoly.toList ++ witnessInput P.queryPowBits proof.queryWitness)
    (samples : List F) {res : Unit × Sponge F}
    (hok : (out answer (verifyFri (idealLogged answer) P proof rounds alpha)
      ⟨capAt answer blocks r, [], samples⟩).1 = .ok res) :
    LogsRounds answer blocks r
      (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      (out answer (verifyFri (idealLogged answer) P proof rounds alpha)
        ⟨capAt answer blocks r, [], samples⟩).2 := by
  set seed := DomainSeparator.friSeed F EF
    (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
    (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
    P.maxLogArity with hseed
  have hseedne : seed ≠ [] := toElems_ne_nil _
  set cws := proof.commits.toList.zip proof.commitWitnesses.toList with hcws
  unfold verifyFri at hok ⊢
  dsimp only at hok ⊢
  simp only [hheights, List.headD_cons] at hok ⊢
  -- the shape checks
  obtain ⟨hpar, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨hfp, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  -- FRI's domain separator
  obtain ⟨_, s₁, h₁, hok, hlog⟩ := out_bind_ok answer hok
  rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hseedne)] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hseedne), List.nil_append]
  dsimp only at hok ⊢
  rw [List.nil_append] at hok ⊢
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  -- the fold rounds
  obtain ⟨betas, s₄, h₄, hok, hlog⟩ := out_bind_ok answer hok
  rw [hlog]
  have hloop := out_forIn_keys answer _ (fun k ↦ keyAt answer blocks (r + k))
    (fun k s ↦ s.cap = capAt answer blocks (r + k) ∧ s.input = seedAt seed k) _ 0 _ _ _ ?_
    ⟨rfl, rfl⟩ h₄
  rotate_left
  · intro k hk b st rr hinv hstep
    simp only [Nat.zero_add] at hinv ⊢
    obtain ⟨hcap, hinp⟩ := hinv
    rcases st with ⟨cap, input, smp⟩
    simp only at hcap hinp
    subst hcap hinp
    have hblk := hfold k hk
    generalize cws[k] = cw at hstep hblk ⊢
    obtain ⟨c, w⟩ := cw
    dsimp only at hstep hblk ⊢
    have hc : c.toList ≠ [] :=
      List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
    obtain ⟨_, s₁, h₁, hstep, hlog₁⟩ := out_bind_ok answer hstep
    rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hc)] at h₁
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
    rw [hlog₁, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hnext : seedAt seed (k + 1) = [] := rfl
    by_cases hbits : P.commitPowBits = 0
    · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hblk
      obtain ⟨v₂, s₂, h₂, hstep, hlog₂⟩ := out_bind_ok answer hstep
      rw [hbits, out_checkWitness_zero] at h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
      obtain ⟨-, hstep, hlog₃⟩ := out_ensure_bind_ok answer hstep
      have hv₄ := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks (r + k))
        (seedAt seed k ++ c.toList)
      obtain ⟨β, s₄, h₄, hstep, hlog₄⟩ := out_bind_ok answer hstep
      rw [hv₄] at h₄
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₄)
      rw [out_pure] at hstep
      obtain rfl := Except.ok.inj hstep
      refine ⟨⟨_, rfl⟩, ⟨(congrArg
        (fun b ↦ (answer (.duplex (capAt answer blocks (r + k)) b)).1) hblk).symm, hnext⟩, ?_⟩
      rw [hlog₂, hbits, out_checkWitness_zero, hlog₃, hlog₄, hv₄]
      simp only [keyAt, hblk, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, true_or, or_true]
    · simp only [witnessInput, hbits, ↓reduceIte] at hblk
      obtain ⟨v₂, hv₂⟩ := out_checkWitness_pos answer _ hbits w (capAt answer blocks (r + k))
        (seedAt seed k ++ c.toList) []
      obtain ⟨_, s₂, h₂, hstep, hlog₂⟩ := out_bind_ok answer hstep
      rw [hv₂] at h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
      obtain ⟨-, hstep, hlog₃⟩ := out_ensure_bind_ok answer hstep
      have hv₄ := out_sampleExt_pop (EF := EF) answer
        (answer (.duplex (capAt answer blocks (r + k)) (seedAt seed k ++ c.toList ++ [w]))).1 []
        (answer (.duplex (capAt answer blocks (r + k))
          (seedAt seed k ++ c.toList ++ [w]))).2.toList.tail
        (by rw [List.length_tail, Vector.length_toList]; omega)
      obtain ⟨β, s₄, h₄, hstep, hlog₄⟩ := out_bind_ok answer hstep
      rw [hv₄] at h₄
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₄)
      rw [out_pure] at hstep
      obtain rfl := Except.ok.inj hstep
      refine ⟨⟨_, rfl⟩, ⟨(congrArg
        (fun b ↦ (answer (.duplex (capAt answer blocks (r + k)) b)).1) hblk).symm, hnext⟩, ?_⟩
      rw [hlog₂, hv₂]
      simp only [keyAt, hblk, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, true_or, or_true]
  obtain ⟨⟨hcap₄, hinp₄⟩, hkeys⟩ := hloop
  refine logsRounds_append (mid := r + cws.length) (fun j hlo hhi ↦ ?_) ?_
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlo
    simpa only [Nat.zero_add] using hkeys k (Nat.lt_of_add_lt_add_left hhi)
  simp only [Nat.zero_add] at hcap₄ hinp₄
  rcases s₄ with ⟨cap₄, inp₄, smp₄⟩
  simp only at hcap₄ hinp₄
  subst hcap₄ hinp₄
  -- the final polynomial
  have hfpne : coeffs proof.finalPoly.toList ≠ [] := by
    refine coeffs_ne_nil (List.ne_nil_of_length_pos ?_)
    rw [Array.length_toList, beq_iff_eq.mp hfp]
    exact Nat.two_pow_pos _
  obtain ⟨_, s₅, h₅, hok, hlog⟩ := out_bind_ok answer hok
  rw [out_observeExts, ite_eq_right_of_eq_false _ _ (eq_false hfpne)] at h₅
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₅)
  rw [hlog, out_observeExts, ite_eq_right_of_eq_false _ _ (eq_false hfpne)]
  refine logsRounds_right ?_
  have hmid : r + 1 + cws.length = r + cws.length + 1 := by omega
  rw [hmid]
  obtain ⟨q, hq⟩ : ∃ q, P.numQueries = q + 1 := ⟨P.numQueries - 1, by omega⟩
  by_cases hbits : P.queryPowBits = 0
  · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hlast
    obtain ⟨_, s₇, h₇, hok, hlog⟩ := out_bind_ok answer hok
    rw [hbits, out_checkWitness_zero] at h₇
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₇)
    rw [hlog, hbits, out_checkWitness_zero]
    refine logsRounds_right ?_
    obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
    rw [hlog]
    rw [hq, List.range_succ_eq_map, List.mapM_cons] at hok ⊢
    obtain ⟨_, _, h₈, -, hlog⟩ := out_bind_ok answer hok
    rw [hlog]
    refine logsRounds_left ?_
    obtain ⟨_, _, h₉, -, hlog⟩ := out_bind_ok answer h₈
    rw [hlog]
    refine logsRounds_left fun j hlo hhi ↦ ?_
    obtain rfl : j = r + cws.length := by omega
    obtain ⟨v, hv⟩ := out_sampleBits_nil answer logMax (capAt answer blocks (r + cws.length))
      (seedAt seed cws.length ++ coeffs proof.finalPoly.toList)
    rw [hv]
    simp only [keyAt, hlast, List.map_cons, List.map_nil, List.mem_singleton]
  · simp only [witnessInput, hbits, ↓reduceIte] at hlast
    obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits proof.queryWitness
      (capAt answer blocks (r + cws.length))
      (seedAt seed cws.length ++ coeffs proof.finalPoly.toList) []
    obtain ⟨_, _, -, -, hlog⟩ := out_bind_ok answer hok
    rw [hlog, hv]
    refine logsRounds_left fun j hlo hhi ↦ ?_
    obtain rfl : j = r + cws.length := by omega
    simp only [keyAt, hlast, List.map_cons, List.map_nil, List.mem_singleton]

/-- A loop of steps that only change the state. -/
theorem out_forIn_state {γ : Type} (l : List γ) (body : γ → PUnit → M Hl (ForInStep PUnit))
    (g : γ → Sponge F → Sponge F)
    (hbody : ∀ a s, out answer (body a PUnit.unit) s = (.ok (.yield PUnit.unit, g a s), []))
    (s : Sponge F) :
    out answer (forIn l PUnit.unit body) s =
      (.ok (PUnit.unit, l.foldl (fun s a ↦ g a s) s), []) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, out_bind, hbody]
    dsimp only
    rw [ih, List.nil_append]
    rfl

/-- The values of the rounds of a commitment scheme opening, in order. -/
def roundValues (rounds : List (Fri.Round F EF)) : List EF :=
  rounds.flatMap fun r ↦ r.2.flatMap fun m ↦ m.2.flatMap (·.2)

theorem foldl_coeffs_flatMap {γ : Type} (l : List γ) (f : γ → List EF) (s : Sponge F) :
    l.foldl (fun s a ↦ (coeffs (f a)).foldl (idealLogged answer).observe s) s =
      (coeffs (l.flatMap f)).foldl (idealLogged answer).observe s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, coeffs, coeffs, coeffs, List.flatMap_append,
      List.foldl_append]

/-- The commitment scheme: from the state after `ζ`, with the capacity of the batching round
`r`, the verifier queries the batching round and every round of FRI. -/
theorem verifyPcs_logs (hK : P.numQueries + Challenge.d EF + 1 ≤ K) (blocks : List (List F))
    (r : Nat) (proof : FriProof F EF) (rounds : List (Fri.Round F EF)) (logMax : Nat)
    (hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [logMax])
    (hblock : blocks.getD r [] = DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits ++
      coeffs (roundValues rounds) ++ witnessInput P.batchPowBits proof.batchWitness)
    (hfold : ∀ j (hj : j < (proof.commits.toList.zip proof.commitWitnesses.toList).length),
      blocks.getD (r + 1 + j) [] = seedAt (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
        P.maxLogArity) j ++
        (proof.commits.toList.zip proof.commitWitnesses.toList)[j].1.toList ++
          witnessInput P.commitPowBits (proof.commits.toList.zip proof.commitWitnesses.toList)[j].2)
    (hlast : blocks.getD (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      [] = seedAt (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
        P.maxLogArity) (proof.commits.toList.zip proof.commitWitnesses.toList).length ++
        coeffs proof.finalPoly.toList ++ witnessInput P.queryPowBits proof.queryWitness)
    (samples : List F) {res : Unit × Sponge F}
    (hok : (out answer (verifyPcs (idealLogged answer) P rounds proof)
      ⟨capAt answer blocks r, [], samples⟩).1 = .ok res) :
    LogsRounds answer blocks r
      (r + 2 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      (out answer (verifyPcs (idealLogged answer) P rounds proof)
        ⟨capAt answer blocks r, [], samples⟩).2 := by
  have hobs : ∀ s, out answer (forIn rounds PUnit.unit fun x _ ↦ match x with
      | (_, mats) => do
        forIn mats PUnit.unit fun x _ ↦ match x with
          | (_, pts) => do
            forIn pts PUnit.unit fun x _ ↦ match x with
              | (_, ys) => do
                observeExts (idealLogged answer) ys
                pure (ForInStep.yield PUnit.unit)
            pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) s =
      (.ok (PUnit.unit, (coeffs (roundValues rounds)).foldl (idealLogged answer).observe s),
        []) := by
    intro s
    rw [out_forIn_state rounds _
      (fun r s ↦ (coeffs (r.2.flatMap fun m ↦ m.2.flatMap (·.2))).foldl
        (idealLogged answer).observe s)]
    · rw [roundValues, foldl_coeffs_flatMap]
    · intro r s
      obtain ⟨_, mats⟩ := r
      dsimp only
      rw [out_bind, out_forIn_state mats _
        (fun m s ↦ (coeffs (m.2.flatMap (·.2))).foldl (idealLogged answer).observe s)]
      · rw [foldl_coeffs_flatMap]
        rfl
      · intro m s
        obtain ⟨_, pts⟩ := m
        dsimp only
        rw [out_bind, out_forIn_state pts _
          (fun p s ↦ (coeffs p.2).foldl (idealLogged answer).observe s)]
        · rw [foldl_coeffs_flatMap]
          rfl
        · intro p s
          obtain ⟨_, ys⟩ := p
          dsimp only
          rw [out_bind, out_observeExts answer, foldl_observe answer]
          rfl
  set pseed := DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits
  unfold verifyPcs at hok ⊢
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  have hpne : pseed ≠ [] := toElems_ne_nil _
  obtain ⟨_, s₁, h₁, hok, hlog⟩ := out_bind_ok answer hok
  rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hpne)] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hpne)]
  refine logsRounds_right ?_
  obtain ⟨_, s₁, h₁, hok, hlog⟩ := out_bind_ok answer hok
  rw [hobs, foldl_observe] at h₁
  have hin : [] ++ pseed ≠ [] := by rw [List.nil_append]; exact toElems_ne_nil _
  have hstate : (if coeffs (roundValues rounds) = [] then
      (⟨capAt answer blocks r, [] ++ pseed, []⟩ : Sponge F) else
      ⟨capAt answer blocks r, [] ++ pseed ++ coeffs (roundValues rounds), []⟩) =
      ⟨capAt answer blocks r, pseed ++ coeffs (roundValues rounds), []⟩ := by
    split
    · rename_i h; rw [h, List.nil_append, List.append_nil]
    · rw [List.nil_append]
  rw [hstate] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hobs, foldl_observe, hstate]
  refine logsRounds_right ?_
  by_cases hbits : P.batchPowBits = 0
  · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hblock
    obtain ⟨_, s₂, h₂, hok, hlog⟩ := out_bind_ok answer hok
    rw [hbits, out_checkWitness_zero] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hbits, out_checkWitness_zero]
    refine logsRounds_right ?_
    obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
    rw [hlog]
    have hv := out_sampleExt_nil (EF := EF) answer (by omega) (capAt answer blocks r)
      (pseed ++ coeffs (roundValues rounds))
    obtain ⟨_, s₃, h₃, hok, hlog⟩ := out_bind_ok answer hok
    rw [hv] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv]
    refine logsRounds_cons (by simp only [keyAt, hblock, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    rw [show (answer (.duplex (capAt answer blocks r) (pseed ++ coeffs (roundValues rounds)))).1 =
      capAt answer blocks (r + 1) by rw [capAt, hblock]] at hok ⊢
    have := verifyFri_logs hK blocks (r + 1) proof rounds _ logMax hheights hfold hlast _ hok
    rwa [show r + 1 + 1 = r + 2 by omega] at this
  · simp only [witnessInput, hbits, ↓reduceIte] at hblock
    obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits proof.batchWitness
      (capAt answer blocks r) (pseed ++ coeffs (roundValues rounds)) []
    obtain ⟨_, s₂, h₂, hok, hlog⟩ := out_bind_ok answer hok
    rw [hv] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hv]
    refine logsRounds_cons (by simp only [keyAt, hblock, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
    rw [hlog]
    have hv₃ := out_sampleExt_pop (EF := EF) answer
      (answer (.duplex (capAt answer blocks r) (pseed ++ coeffs (roundValues rounds) ++
        [proof.batchWitness]))).1 []
      (answer (.duplex (capAt answer blocks r) (pseed ++ coeffs (roundValues rounds) ++
        [proof.batchWitness]))).2.toList.tail
      (by rw [List.length_tail, Vector.length_toList]; omega)
    obtain ⟨_, s₃, h₃, hok, hlog⟩ := out_bind_ok answer hok
    rw [hv₃] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv₃, List.nil_append]
    rw [show (answer (.duplex (capAt answer blocks r) (pseed ++ coeffs (roundValues rounds) ++
      [proof.batchWitness]))).1 = capAt answer blocks (r + 1) by rw [capAt, hblock]] at hok ⊢
    have := verifyFri_logs hK blocks (r + 1) proof rounds _ logMax hheights hfold hlast _ hok
    rwa [show r + 1 + 1 = r + 2 by omega] at this

theorem inputs_getD_fri (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (pis : List F) (proof : Proof F EF)
    (k : Nat) : (inputs P A vk pis proof).getD (3 + k) [] = seedAt (friSeedOf P proof) k ++
      ((((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
        cw.1.toList ++ witnessInput P.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++
        witnessInput P.queryPowBits proof.fri.queryWitness]).getD
        k []) := by
  rw [inputs, show 3 + k = k + 1 + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_cons_succ]
  rcases h : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput P.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++ witnessInput P.queryPowBits proof.fri.queryWitness]
    with _ | ⟨b, bs⟩
  · simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false] at h
  · exact getD_prependSeed _ _ _ _

theorem inputs_getD_fold (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (pis : List F) (proof : Proof F EF)
    (j : Nat) (hj : j < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length) :
    (inputs P A vk pis proof).getD (3 + j) [] = seedAt (friSeedOf P proof) j ++
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].1.toList ++
        witnessInput P.commitPowBits
          (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].2 := by
  rw [inputs_getD_fri, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp only [List.length_map]; exact hj)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem inputs_getD_last (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (pis : List F) (proof : Proof F EF) :
    (inputs P A vk pis proof).getD
      (3 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length) [] =
      seedAt (friSeedOf P proof)
        (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length ++
      coeffs proof.fri.finalPoly.toList ++ witnessInput P.queryPowBits proof.fri.queryWitness := by
  rw [inputs_getD_fri, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem length_inputs (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F)) (pis : List F)
    (proof : Proof F EF) :
    (inputs P A vk pis proof).length =
      2 + 2 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length := by
  rw [inputs]
  rcases h : ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
      cw.1.toList ++ witnessInput P.commitPowBits cw.2) ++
      [coeffs proof.fri.finalPoly.toList ++ witnessInput P.queryPowBits proof.fri.queryWitness]
    with _ | ⟨b, bs⟩
  · simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false] at h
  · have := congrArg List.length h
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
    simp only [prependSeed, List.length_cons]
    omega

/-- The verifier's last step: run the challenger part, then a check that queries nothing. -/
theorem run_stateT_bind {α β : Type} (x : M (idealLogged answer) α) (s : Sponge F)
    (g : α × Sponge F → ExceptT String (WriterT (QueryLog (spec F K)) Id) β)
    (hg : ∀ a, ((g a).run.run).2 = []) :
    ((StateT.run x s >>= g).run.run) = match out answer x s with
      | (.ok a, w) => (((g a).run.run).1, w)
      | (.error e, w) => (.error e, w) := by
  rw [ExceptT.run_bind, WriterT.run_bind']
  unfold out
  rcases (StateT.run x s).run.run with ⟨_ | a, w⟩
  · change (Except.error _, w ++ []) = _
    rw [List.append_nil]
  · change (((g a).run.run).1, w ++ ((g a).run.run).2) = _
    rw [hg, List.append_nil]

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
    (proof : Proof F EF) (zeta : EF)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    roundValues (openingRounds A vk proof zeta) = openedValues proof.opened := by
  unfold openingRounds
  rcases preprocessedRound_cases A vk proof.opened _ hshape ⟨1, proof.degreeBits⟩ zeta
    (zeta * Ext.ofBase (twoAdicGen proof.degreeBits)) with ⟨-, hl, hn, hr⟩ | ⟨k, l, -, hl, hr⟩
  · simp only [roundValues, openedValues, hr, hl, hn, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_map, List.append_nil, List.append_assoc, Option.getD_none, Array.toList_empty]
  · simp only [roundValues, openedValues, hr, hl, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_map, List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
      Option.getD_some]
    cases proof.opened.preprocessedNext <;>
      simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        List.flatMap_nil, List.flatMap_cons, List.append_nil, Option.getD_none, Option.getD_some,
        Array.toList_empty]

/-- **The verifier queries every round.** If the verifier on the logged answers accepts a proof,
its log holds the duplex call of every round of the proof's schedule. -/
theorem verifyWith_logs (hK : P.numQueries + Challenge.d EF + 1 ≤ K) (A : Air F)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hok : (verifyWith (idealLogged answer) P A vk proof pis).run.1 = .ok ()) :
    LogsRounds answer (inputs P A vk pis proof) 0 (inputs P A vk pis proof).length
      (verifyWith (idealLogged answer) P A vk proof pis).run.2 := by
  unfold verifyWith at hok ⊢
  dsimp only at hok ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hdeg
  simp only [hdeg, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hpis
  simp only [hpis, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hshape
  simp only [hshape, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hoodw
  simp only [hoodw, ↓reduceIte] at ⊢
  rw [run_stateT_bind _ _ _ (fun a ↦ by split <;> rfl)] at hok ⊢
  rcases hrun : out answer _ { cap := initCap, input := [], samples := [] } with ⟨_ | a, w⟩
  · rw [hrun] at hok
    cases hok
  rw [hrun] at hok
  dsimp only
  have hrun1 := congrArg Prod.fst hrun
  have hrun2 := congrArg Prod.snd hrun
  dsimp only at hrun1 hrun2
  rw [← hrun2]
  clear hrun hrun2 hok
  -- the observations of the first round
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  have hin₀ : starkSeedOf EF P A proof.degreeBits ++ proof.traceCommit.toList ++
      preprocessedDigest vk ++ pis = (inputs P A vk pis proof).getD 0 [] := by
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
  simp only [List.nil_append] at hrun1 ⊢
  rw [hin₀, show initCap = capAt answer (inputs P A vk pis proof) 0 from rfl] at hrun1 ⊢
  -- the round of `α`
  have hv₀ := out_sampleExt_nil (EF := EF) answer (by omega)
    (capAt answer (inputs P A vk pis proof) 0) ((inputs P A vk pis proof).getD 0 [])
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [hv₀] at h₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hv₀]
  refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
    List.mem_singleton]) ?_
  rw [show (answer (.duplex (capAt answer (inputs P A vk pis proof) 0)
    ((inputs P A vk pis proof).getD 0 []))).1 = capAt answer (inputs P A vk pis proof) 1 from rfl]
    at hrun1 ⊢
  -- the round of `ζ`
  have hqc : proof.quotientCommit.toList ≠ [] :=
    List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc)] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc), List.nil_append]
  dsimp only at hrun1 ⊢
  rw [List.nil_append] at hrun1 ⊢
  have hin₁ : (inputs P A vk pis proof).getD 1 [] =
      proof.quotientCommit.toList ++ witnessInput P.oodPowBits proof.oodWitness := by
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
  have hzeta : ∀ (alpha zeta : EF) (smp : List F) {res : (EF × EF) × Sponge F},
      (out answer (do
        ensure (Ext.powTwo zeta proof.degreeBits - 1 != 0)
          "out-of-domain point in the trace domain"
        verifyPcs (idealLogged answer) P (openingRounds A vk proof zeta) proof.fri
        pure (alpha, zeta)) ⟨capAt answer (inputs P A vk pis proof) 2, [], smp⟩).1 = .ok res →
      LogsRounds answer (inputs P A vk pis proof) 2 (inputs P A vk pis proof).length
        (out answer (do
          ensure (Ext.powTwo zeta proof.degreeBits - 1 != 0)
            "out-of-domain point in the trace domain"
          verifyPcs (idealLogged answer) P (openingRounds A vk proof zeta) proof.fri
          pure (alpha, zeta)) ⟨capAt answer (inputs P A vk pis proof) 2, [], smp⟩).2 := by
    intro alpha zeta smp res h
    obtain ⟨-, h, hlog⟩ := out_ensure_bind_ok answer h
    rw [hlog]
    obtain ⟨_, _, h₂, -, hlog⟩ := out_bind_ok answer h
    rw [hlog]
    refine logsRounds_left ?_
    rw [length_inputs]
    refine verifyPcs_logs hK (inputs P A vk pis proof) 2 proof.fri (openingRounds A vk proof zeta)
      (proof.degreeBits + P.logBlowup) (heights_openingRounds P A vk proof zeta) ?_
      (fun j hj ↦ inputs_getD_fold P A vk pis proof j hj) (inputs_getD_last P A vk pis proof) _ h₂
    have hshape' : preprocessedShapeOk A vk proof.opened proof.degreeBits = true := by
      simp only [Bool.and_eq_true] at hshape
      exact hshape.2
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, claimCounts_openingRounds A vk proof zeta hshape',
      roundValues_openingRounds A vk proof zeta hshape']
  by_cases hbits : P.oodPowBits = 0
  · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hin₁
    obtain ⟨_, s₂, h₂, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hbits, out_checkWitness_zero] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hbits, out_checkWitness_zero]
    refine logsRounds_right ?_
    obtain ⟨-, hrun1, hlog⟩ := out_ensure_bind_ok answer hrun1
    rw [hlog]
    rw [← hin₁] at hrun1 ⊢
    have hv₁ := out_sampleExt_nil (EF := EF) answer (by omega)
      (capAt answer (inputs P A vk pis proof) 1) ((inputs P A vk pis proof).getD 1 [])
    obtain ⟨_, s₃, h₃, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv₁] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv₁]
    refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    exact hzeta _ _ _ hrun1
  · simp only [witnessInput, hbits, ↓reduceIte] at hin₁
    obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits proof.oodWitness
      (capAt answer (inputs P A vk pis proof) 1) proof.quotientCommit.toList []
    obtain ⟨_, s₂, h₂, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv] at h₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
    rw [hlog, hv, ← hin₁]
    rw [← hin₁] at hrun1
    refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
      List.mem_singleton]) ?_
    obtain ⟨-, hrun1, hlog⟩ := out_ensure_bind_ok answer hrun1
    rw [hlog]
    have hv₁ := out_sampleExt_pop (EF := EF) answer
      (answer (.duplex (capAt answer (inputs P A vk pis proof) 1)
        ((inputs P A vk pis proof).getD 1 []))).1 []
      (answer (.duplex (capAt answer (inputs P A vk pis proof) 1)
        ((inputs P A vk pis proof).getD 1 []))).2.toList.tail
      (by rw [List.length_tail, Vector.length_toList]; omega)
    obtain ⟨_, s₃, h₃, hrun1, hlog⟩ := out_bind_ok answer hrun1
    rw [hv₁] at h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₃)
    rw [hlog, hv₁, List.nil_append]
    exact hzeta _ _ _ hrun1

end Run

/-! ### The verifier's rounds -/

section Verifier

variable {answer : (q : Query F) → Answer K q}

/-- The verifier on logged answers gives the verifier on the answers, and its log. -/
theorem run_idealLogged (P : Fri.Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) :
    (verifyWith (idealLogged answer) P A vk proof pis).run =
      (verifyWith (idealOf answer) P A vk proof pis,
        tableQueryLog (verifyWith (ideal F K) P A vk proof pis) answer) := by
  have h := QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn answer)
    (verifyWith (ideal F K) P A vk proof pis)
  rw [simulateQ_verifyWith, simulateQ_verifyWith] at h
  exact Prod.ext h (tableQueryLog_verifyWith answer P A vk proof pis).symm

end Verifier

section Setup
variable (S : Iop.Setup EF) (answer : (q : Query F) → Answer S.streamLen q)

/-- **The verifier queries every round.** If the verifier accepts a proof on the answers
`answer`, the duplex call of every round of the proof's schedule is in its log. -/
theorem hasRounds_verifyWith (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    HasRounds answer (tableQueryLog (verifyWith (ideal F S.streamLen) S.params S.air vk proof pis)
      answer) (inputs S.params S.air vk pis proof) (inputs S.params S.air vk pis proof).length := by
  have h := verifyWith_logs (answer := answer) (P := S.params) (le_refl _) S.air vk proof pis
    (by rw [run_idealLogged]; exact hok)
  rw [run_idealLogged] at h
  exact fun j hj ↦ h j (Nat.zero_le j) hj

/-- **Parsing the verifier's rounds.** If the verifier accepts a proof on the answers `answer`,
and its duplex calls answer distinct capacities, none the initial one, then its
log before round `i`'s call parses that call to the rounds before it and its input: the
proof's prefix up to round `i`. -/
theorem parse_verifyWith (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ())
    (hinj : CapsInjective answer
      (tableQueryLog (verifyWith (ideal F S.streamLen) S.params S.air vk proof pis) answer))
    (i : Nat) (hi : i ≤ (inputs S.params S.air vk pis proof).length) :
    parse (tableQueryLog (verifyWith (ideal F S.streamLen) S.params S.air vk proof pis) answer)
        (keyAt answer (inputs S.params S.air vk pis proof) i) =
      some (history answer (inputs S.params S.air vk pis proof) i,
        (inputs S.params S.air vk pis proof).getD i []) :=
  parse_keyAt (consistent_tableQueryLog _) hinj
    fun j hj ↦ hasRounds_verifyWith S answer vk proof pis hok j (by omega)

end Setup

/-! ### Reading challenges off a round -/

/-- The extension element of `d` samples from `offset` on, lowest coefficient first, in `𝕂`. -/
def extAt (samples : Vector F K) (offset : Nat) : Challenge.Spec EF :=
  CompPoly.Extension.Ext.ofFn fun i ↦ samples.toList.getD (offset + i) 0

/-- An extension sample of the `d` samples from `offset` on is `extAt`. -/
theorem toSpec_ofCoeffs_drop (samples : Vector F K) (offset : Nat) :
    Challenge.toSpec (Challenge.ofCoeffs
      ((samples.toList.drop offset).take (Challenge.d EF)) : EF) = extAt samples offset := by
  rw [Challenge.toSpec_ofCoeffs, extAt]
  congr 1
  funext i
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]


end CompStark.Ni
