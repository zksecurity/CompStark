/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Answers
public import CompStark.Ni.QueryBound

/-! # Parsing duplex calls into transcript prefixes

In the random-oracle model every challenge round of the verifier is one duplex call: the
capacity left by the previous round and the elements observed since. A duplex call can be read
back from the queries made before it by following capacities to the initial one (`parse`): each
capacity was answered by the call of the round before. This gives the call's history (each
earlier round's input and answered samples) and its own input.

* `inputs P pis proof`: the transcript schedule, the elements the verifier observes before each
  squeeze: the degree twice, `0`, the trace commitment and the public values; the quotient
  commitment; the opened values; each commit-phase commitment with its grinding witness (none
  without commit grinding); the final polynomial, the fold arities and the query grinding witness
  (none without query grinding).
* `keyAt answer blocks i`: the duplex call of round `i` when every round is answered by
  `answer`, and `history answer blocks i` the rounds before it, the prefix of round `i`.
* `parse_keyAt`: in a log answered by `answer` whose duplex calls answer distinct capacities,
  none the initial one (`CapsInjective`), and that holds the calls of the rounds before `i`, the
  call of round `i` parses to its history and input.
* `hasRounds_verifyWith`: if the verifier accepts a proof for `2 ^ logN` rows on fixed answers,
  its log holds the call of every round of the proof's schedule. The proof runs the verifier
  symbolically on the logged answers (`out` and its lemmas), up to the query round.
* `parse_verifyWith`: so, in the verifier's log, round `i`'s call parses to the proof's prefix up
  to round `i`.
* `extAt`, `challengeOffset`: reading the challenges off a round's samples.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

/-! ### The transcript schedule -/

/-- Extension elements as base elements, lowest coefficient first. -/
def coeffs (xs : List EF) : List F := xs.flatMap fun x ↦ [x.c0, x.c1, x.c2, x.c3]

/-- A grinding witness as the verifier observes it: not at all without grinding. -/
def witnessInput (bits : Nat) (w : F) : List F := if bits = 0 then [] else [w]

/-- The opened values in the order the verifier observes them: the trace at `ζ`, the trace at
`ζ ω`, and every quotient chunk. -/
def openedValues (o : OpenedValues) : List EF :=
  o.traceLocal.toList ++ o.traceNext.toList ++ o.quotientChunks.toList.flatMap (·.toList)

/-- The elements the verifier observes on `proof` before each squeeze, round by round. -/
def inputs (P : Fri.Params) (pis : List F) (proof : Proof) : List (List F) :=
  ([(proof.degreeBits : F), (proof.degreeBits : F), 0] ++ proof.traceCommit.toList ++ pis) ::
  proof.quotientCommit.toList ::
  coeffs (openedValues proof.opened) ::
  ((proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).map fun cw ↦
    cw.1.toList ++ witnessInput P.commitPowBits cw.2) ++
  [coeffs proof.fri.finalPoly.toList ++ (Fri.arities proof.fri).map (fun a : Nat ↦ (a : F)) ++
    witnessInput P.queryPowBits proof.fri.queryWitness]

/-! ### The duplex chain of a schedule -/

variable {K : Nat} (answer : (q : Query) → Answer K q)

/-- The capacity before round `j` of `blocks` when every round is answered by `answer`. -/
def capAt (blocks : List (List F)) : Nat → Digest
  | 0 => initCap
  | j + 1 => (answer (.duplex (capAt blocks j) (blocks.getD j []))).1

/-- The duplex call of round `j`. -/
def keyAt (blocks : List (List F)) (j : Nat) : Query :=
  .duplex (capAt answer blocks j) (blocks.getD j [])

/-- A round of a duplex chain: its input and the samples answered. -/
abbrev Step (K : Nat) := List F × Vector F K

/-- The rounds before round `i`. -/
def history (blocks : List (List F)) (i : Nat) : List (Step K) :=
  (List.range i).map fun j ↦ (blocks.getD j [], (answer (keyAt answer blocks j)).2)

/-! ### Parsing -/

/-- The first duplex call in `log` answering capacity `cap`: its capacity, input and samples. -/
def answering (log : QueryLog (spec K)) (cap : Digest) : Option (Digest × Step K) :=
  log.findSome? fun e ↦ match e with
    | ⟨.duplex c input, answer⟩ => if answer.1 = cap then some (c, input, answer.2) else none
    | _ => none

/-- The rounds that led to capacity `cap` in `log`, oldest first, following capacities back to
the initial one in at most `fuel` steps. -/
def stepsTo (log : QueryLog (spec K)) : Nat → Digest → Option (List (Step K))
  | fuel, cap =>
    if cap = initCap then some [] else
      match fuel with
      | 0 => none
      | fuel + 1 => match answering log cap with
        | some (c, step) => (stepsTo log fuel c).map (· ++ [step])
        | none => none

/-- A duplex call parsed against the queries `log` before it: the rounds before it and its
input. -/
def parse (log : QueryLog (spec K)) : Query → Option (List (Step K) × List F)
  | .duplex cap input => (stepsTo log log.length cap).map (·, input)
  | _ => none

/-- Every query of `log` is answered by `answer`. -/
def Consistent (log : QueryLog (spec K)) : Prop := ∀ e ∈ log, e.2 = answer e.1

/-- On the duplex calls of `log`, `answer` never gives the initial capacity, and gives distinct
calls distinct capacities. -/
def CapsInjective (log : QueryLog (spec K)) : Prop :=
  ∀ c input, Query.duplex c input ∈ log.map Sigma.fst →
    (answer (.duplex c input)).1 ≠ initCap ∧
    ∀ c' input', Query.duplex c' input' ∈ log.map Sigma.fst →
      (answer (.duplex c input)).1 = (answer (.duplex c' input')).1 → c = c' ∧ input = input'

variable {answer}

theorem answering_eq (log : QueryLog (spec K)) (hcons : Consistent answer log)
    (hinj : CapsInjective answer log) (c : Digest) (input : List F)
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

variable {log : QueryLog (spec K)} {blocks : List (List F)} {i : Nat}

/-- The calls of the rounds before `i` are in `log`. -/
def HasRounds (answer : (q : Query) → Answer K q) (log : QueryLog (spec K))
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

variable (answer : (q : Query) → Answer K q) {P : Fri.Params}

local notation "Hl" => idealLogged answer

/-- The result and the query log of `x` from state `s`, on the logged answers. -/
def out {α : Type} (x : M Hl α) (s : Sponge) :
    Except String (α × Sponge) × QueryLog (spec K) :=
  ((x.run s).run).run

theorem out_pure {α : Type} (a : α) (s : Sponge) :
    out answer (pure a : M Hl α) s = (.ok (a, s), []) := rfl

theorem out_bind {α β : Type} (x : M Hl α) (f : α → M Hl β) (s : Sponge) :
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
theorem out_bind_ok {α β : Type} {x : M Hl α} {f : α → M Hl β} {s : Sponge} {r : β × Sponge}
    (h : (out answer (x >>= f) s).1 = .ok r) :
    ∃ v s', (out answer x s).1 = .ok (v, s') ∧ (out answer (f v) s').1 = .ok r ∧
      (out answer (x >>= f) s).2 = (out answer x s).2 ++ (out answer (f v) s').2 := by
  rw [out_bind] at h ⊢
  rcases hx : out answer x s with ⟨_ | ⟨v, s'⟩, w⟩
  · rw [hx] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · rw [hx] at h
    exact ⟨v, s', rfl, h, rfl⟩

theorem out_modify (f : Sponge → Sponge) (s : Sponge) :
    out answer (modify f : M Hl Unit) s = (.ok ((), f s), []) := rfl

theorem out_throw {α : Type} (e : String) (s : Sponge) :
    out answer (throw e : M Hl α) s = (.error e, []) := rfl

theorem out_ensure_ok {b : Bool} {msg : String} {s : Sponge} {r : Unit × Sponge}
    (h : (out answer (ensure (H := Hl) b msg) s).1 = .ok r) : b = true ∧ r = ((), s) := by
  unfold ensure at h
  split at h
  · exact ⟨by assumption, (Except.ok.inj h).symm⟩
  · exact absurd h (by simp only [out_throw, reduceCtorEq, not_false_eq_true])

/-- A passed check: its condition holds, and the rest runs from the same state. -/
theorem out_ensure_bind_ok {β : Type} {b : Bool} {msg : String} {f : Unit → M Hl β} {s : Sponge}
    {r : β × Sponge} (h : (out answer (ensure (H := Hl) b msg >>= f) s).1 = .ok r) :
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

theorem out_sample_cons (cap : Digest) (input : List F) (x : F) (rest : List F) :
    out answer (sample Hl) ⟨cap, input, x :: rest⟩ = (.ok (x, ⟨cap, input, rest⟩), []) := rfl

theorem out_sample_nil (cap : Digest) (input : List F) :
    out answer (sample Hl) ⟨cap, input, []⟩ =
      (.ok (((answer (.duplex cap input)).2.toList.headD 0),
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) := by
  unfold out
  change (Except.ok <$> (Hl).sample ⟨cap, input, []⟩ : WriterT _ Id _).run = _
  simp only [QueryImpl.withLogging_apply, QueryImpl.ofFn_apply]
  rfl

theorem foldl_observe : ∀ (xs : List F) (s : Sponge),
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

theorem out_observeList (xs : List F) (s : Sponge) :
    out answer (observeList Hl xs) s =
      (.ok ((), if xs = [] then s else ⟨s.cap, s.input ++ xs, []⟩), []) := by
  rw [observeList, out_modify, foldl_observe]

theorem out_observeList_nil (xs : List F) (cap : Digest) (input : List F) :
    out answer (observeList Hl xs) ⟨cap, input, []⟩ = (.ok ((), ⟨cap, input ++ xs, []⟩), []) := by
  rw [out_observeList]
  split
  · rename_i h
    rw [h, List.append_nil]
  · rfl

theorem out_observe (x : F) (s : Sponge) :
    out answer (observe Hl x) s = (.ok ((), ⟨s.cap, s.input ++ [x], []⟩), []) := rfl

theorem foldl_observeExts (xs : List EF) (s : Sponge) :
    xs.foldl (fun s x ↦ [x.c0, x.c1, x.c2, x.c3].foldl (Hl).observe s) s =
      (coeffs xs).foldl (Hl).observe s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [coeffs, List.flatMap_cons, List.foldl_append]

theorem out_observeExts (xs : List EF) (s : Sponge) :
    out answer (observeExts Hl xs) s =
      (.ok ((), if coeffs xs = [] then s else ⟨s.cap, s.input ++ coeffs xs, []⟩), []) := by
  rw [observeExts, out_modify, foldl_observeExts, foldl_observe]

/-- Four samples left: an extension sample takes them. -/
theorem out_sampleExt_pop (cap : Digest) (input : List F) (samples : List F)
    (h : 4 ≤ samples.length) :
    ∃ v, out answer (sampleExt Hl) ⟨cap, input, samples⟩ =
      (.ok (v, ⟨cap, input, samples.drop 4⟩), []) := by
  match samples, h with
  | a :: b :: c :: d :: rest, _ =>
    exact ⟨⟨a, b, c, d⟩, by simp only [sampleExt, out_bind, out_sample_cons, out_pure,
      List.append_nil, List.drop_succ_cons, List.drop_zero]⟩

/-- No samples left: an extension sample duplexes and takes four samples of the answer. -/
theorem out_sampleExt_nil (hK : 4 ≤ K) (cap : Digest) (input : List F) :
    ∃ v, out answer (sampleExt Hl) ⟨cap, input, []⟩ =
      (.ok (v, ⟨(answer (.duplex cap input)).1, [],
        (answer (.duplex cap input)).2.toList.drop 4⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) := by
  have hlen : 3 ≤ (answer (.duplex cap input)).2.toList.tail.length := by
    rw [List.length_tail, Vector.length_toList]
    omega
  match hL : (answer (.duplex cap input)).2.toList, hlen with
  | a :: b :: c :: d :: rest, _ =>
    refine ⟨⟨a, b, c, d⟩, ?_⟩
    simp only [sampleExt, out_bind, out_sample_nil, hL, List.headD_cons, List.tail_cons,
      out_sample_cons, out_pure, List.append_nil, List.drop_succ_cons, List.drop_zero]

/-- A loop whose every step from a state satisfying `Inv` yields, keeps `Inv` at the next step
and queries `q` of its step logs `q` of every step. -/
theorem out_forIn_keys {γ β : Type} (f : γ → β → M Hl (ForInStep β)) (q : Nat → Query)
    (Inv : Nat → Sponge → Prop) :
    ∀ (l : List γ) (k0 : Nat) (b : β) (s : Sponge) (r : β × Sponge),
      (∀ k (hk : k < l.length) b s (r : ForInStep β × Sponge), Inv (k0 + k) s →
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
theorem out_sampleBits_nil (bits : Nat) (cap : Digest) (input : List F) :
    ∃ v, out answer (sampleBits Hl bits) ⟨cap, input, []⟩ =
      (.ok (v, ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩),
        [⟨.duplex cap input, answer (.duplex cap input)⟩]) :=
  ⟨_, by simp only [sampleBits, out_bind, out_sample_nil, out_pure, List.append_nil]; rfl⟩

theorem out_checkWitness_zero (w : F) (s : Sponge) :
    out answer (checkWitness Hl 0 w) s = (.ok (true, s), []) := rfl

/-- With grinding, a witness check observes the witness, duplexes and takes the first sample. -/
theorem out_checkWitness_pos (bits : Nat) (hbits : bits ≠ 0) (w : F) (cap : Digest)
    (input samples : List F) :
    ∃ v, out answer (checkWitness Hl bits w) ⟨cap, input, samples⟩ =
      (.ok (v, ⟨(answer (.duplex cap (input ++ [w]))).1, [],
        (answer (.duplex cap (input ++ [w]))).2.toList.tail⟩),
        [⟨.duplex cap (input ++ [w]), answer (.duplex cap (input ++ [w]))⟩]) := by
  obtain ⟨v, hv⟩ := out_sampleBits_nil answer bits cap (input ++ [w])
  refine ⟨v == 0, ?_⟩
  simp only [checkWitness, hbits, ↓reduceIte, out_bind, out_observe, hv, out_pure,
    List.append_nil, List.nil_append]

theorem out_forIn_observe {γ : Type} (l : List γ) (f : γ → F) (s : Sponge) :
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
def LogsRounds (answer : (q : Query) → Answer K q) (blocks : List (List F)) (lo hi : Nat)
    (w : QueryLog (spec K)) : Prop :=
  ∀ j, lo ≤ j → j < hi → keyAt answer blocks j ∈ w.map Sigma.fst

theorem logsRounds_cons {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec K)}
    (h₁ : keyAt answer blocks lo ∈ w₁.map Sigma.fst)
    (h₂ : LogsRounds answer blocks (lo + 1) hi w₂) :
    LogsRounds answer blocks lo hi (w₁ ++ w₂) := fun j hlo hhi ↦ by
  rw [List.map_append, List.mem_append]
  rcases Nat.eq_or_lt_of_le hlo with rfl | hlt
  · exact Or.inl h₁
  · exact Or.inr (h₂ j hlt hhi)

theorem logsRounds_append {blocks : List (List F)} {lo mid hi : Nat} {w₁ w₂ : QueryLog (spec K)}
    (h₁ : LogsRounds answer blocks lo mid w₁) (h₂ : LogsRounds answer blocks mid hi w₂) :
    LogsRounds answer blocks lo hi (w₁ ++ w₂) := fun j hlo hhi ↦ by
  rw [List.map_append, List.mem_append]
  rcases Nat.lt_or_ge j mid with h | h
  · exact Or.inl (h₁ j hlo h)
  · exact Or.inr (h₂ j h hhi)

theorem logsRounds_empty {blocks : List (List F)} {lo hi : Nat} {w : QueryLog (spec K)}
    (h : hi ≤ lo) : LogsRounds answer blocks lo hi w := fun _ hlo hhi ↦ by omega

theorem logsRounds_right {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec K)}
    (h₂ : LogsRounds answer blocks lo hi w₂) : LogsRounds answer blocks lo hi (w₁ ++ w₂) :=
  fun j hlo hhi ↦ by
    rw [List.map_append, List.mem_append]
    exact Or.inr (h₂ j hlo hhi)

theorem logsRounds_left {blocks : List (List F)} {lo hi : Nat} {w₁ w₂ : QueryLog (spec K)}
    (h₁ : LogsRounds answer blocks lo hi w₁) : LogsRounds answer blocks lo hi (w₁ ++ w₂) :=
  fun j hlo hhi ↦ by
    rw [List.map_append, List.mem_append]
    exact Or.inl (h₁ j hlo hhi)

/-- FRI's rounds: from the batching round `r` on, with its input observed, the verifier queries
the batching round, every fold round and the query round. -/
theorem verifyFri_logs (hK : P.numQueries + 5 ≤ K) (blocks : List (List F)) (r : Nat)
    (proof : FriProof) (rounds : List Round) (hne : arities proof ≠ [])
    (hfold : ∀ j (hj : j < (proof.commits.toList.zip proof.commitWitnesses.toList).length),
      blocks.getD (r + 1 + j) [] =
        (proof.commits.toList.zip proof.commitWitnesses.toList)[j].1.toList ++
          witnessInput P.commitPowBits (proof.commits.toList.zip proof.commitWitnesses.toList)[j].2)
    (hlast : blocks.getD (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      [] = coeffs proof.finalPoly.toList ++ (arities proof).map (fun a : Nat ↦ (a : F)) ++
        witnessInput P.queryPowBits proof.queryWitness)
    {res : Unit × Sponge}
    (hok : (out answer (verifyFri (idealLogged answer) P proof rounds)
      ⟨capAt answer blocks r, blocks.getD r [], []⟩).1 = .ok res) :
    LogsRounds answer blocks r
      (r + 2 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      (out answer (verifyFri (idealLogged answer) P proof rounds)
        ⟨capAt answer blocks r, blocks.getD r [], []⟩).2 := by
  unfold verifyFri at hok ⊢
  dsimp only at hok ⊢
  simp only [← Array.forIn_toList] at hok ⊢
  -- the batching round
  obtain ⟨v₁, hv₁⟩ := out_sampleExt_nil answer (by omega) (capAt answer blocks r)
    (blocks.getD r [])
  obtain ⟨alpha, s₁, h₁, hok, hlog⟩ := out_bind_ok answer hok
  rw [hv₁] at h₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hv₁]
  refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil, List.mem_singleton])
    ?_
  -- the shape checks
  obtain ⟨hall, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨hwit, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  -- the fold rounds
  obtain ⟨betas, s₄, h₄, hok, hlog⟩ := out_bind_ok answer hok
  rw [hlog]
  have hloop := out_forIn_keys answer _ (fun k ↦ keyAt answer blocks (r + 1 + k))
    (fun k s ↦ s.cap = capAt answer blocks (r + 1 + k) ∧ s.input = []) _ 0 _ _ _ ?_
    ⟨rfl, rfl⟩ h₄
  rotate_left
  · intro k hk b st rr hinv hstep
    simp only [Nat.zero_add] at hinv ⊢
    obtain ⟨hcap, hinp⟩ := hinv
    rcases st with ⟨cap, input, smp⟩
    simp only at hcap hinp
    subst hcap hinp
    have hblk := hfold k hk
    generalize (proof.commits.toList.zip proof.commitWitnesses.toList)[k] = cw at hstep hblk ⊢
    obtain ⟨c, w⟩ := cw
    dsimp only at hstep hblk ⊢
    have hc : c.toList ≠ [] :=
      List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
    obtain ⟨_, s₁, h₁, hstep, hlog₁⟩ := out_bind_ok answer hstep
    rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append] at h₁
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
    rw [hlog₁, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append]
    by_cases hbits : P.commitPowBits = 0
    · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hblk
      obtain ⟨v₂, s₂, h₂, hstep, hlog₂⟩ := out_bind_ok answer hstep
      rw [hbits, out_checkWitness_zero] at h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
      obtain ⟨-, hstep, hlog₃⟩ := out_ensure_bind_ok answer hstep
      obtain ⟨v₄, hv₄⟩ := out_sampleExt_nil answer (by omega) (capAt answer blocks (r + 1 + k))
        c.toList
      obtain ⟨β, s₄, h₄, hstep, hlog₄⟩ := out_bind_ok answer hstep
      rw [hv₄] at h₄
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₄)
      rw [out_pure] at hstep
      obtain rfl := Except.ok.inj hstep
      refine ⟨⟨_, rfl⟩, ⟨(congrArg
        (fun b ↦ (answer (.duplex (capAt answer blocks (r + 1 + k)) b)).1) hblk).symm, rfl⟩, ?_⟩
      rw [hlog₂, hbits, out_checkWitness_zero, hlog₃, hlog₄, hv₄]
      simp only [keyAt, hblk, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, true_or, or_true]
    · simp only [witnessInput, hbits, ↓reduceIte] at hblk
      obtain ⟨v₂, hv₂⟩ := out_checkWitness_pos answer _ hbits w (capAt answer blocks (r + 1 + k))
        c.toList []
      obtain ⟨_, s₂, h₂, hstep, hlog₂⟩ := out_bind_ok answer hstep
      rw [hv₂] at h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₂)
      obtain ⟨-, hstep, hlog₃⟩ := out_ensure_bind_ok answer hstep
      obtain ⟨v₄, hv₄⟩ := out_sampleExt_pop answer
        (answer (.duplex (capAt answer blocks (r + 1 + k)) (c.toList ++ [w]))).1 []
        (answer (.duplex (capAt answer blocks (r + 1 + k)) (c.toList ++ [w]))).2.toList.tail
        (by rw [List.length_tail, Vector.length_toList]; omega)
      obtain ⟨β, s₄, h₄, hstep, hlog₄⟩ := out_bind_ok answer hstep
      rw [hv₄] at h₄
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₄)
      rw [out_pure] at hstep
      obtain rfl := Except.ok.inj hstep
      refine ⟨⟨_, rfl⟩, ⟨(congrArg
        (fun b ↦ (answer (.duplex (capAt answer blocks (r + 1 + k)) b)).1) hblk).symm, rfl⟩, ?_⟩
      rw [hlog₂, hv₂]
      simp only [keyAt, hblk, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, true_or]
  obtain ⟨⟨hcap₄, hinp₄⟩, hkeys⟩ := hloop
  refine logsRounds_append (mid := r + 1 + (proof.commits.toList.zip
    proof.commitWitnesses.toList).length) (fun j hlo hhi ↦ ?_) ?_
  · obtain ⟨k, rfl⟩ : ∃ k, j = r + 1 + k := ⟨j - (r + 1), by omega⟩
    simpa only [Nat.zero_add] using hkeys k (by omega)
  simp only [Nat.zero_add] at hcap₄
  rcases s₄ with ⟨cap₄, inp₄, smp₄⟩
  simp only at hcap₄ hinp₄
  subst hcap₄ hinp₄
  -- the query round
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨_, s₅, h₅, hok, hlog⟩ := out_bind_ok answer hok
  rw [out_observeExts] at h₅
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₅)
  rw [hlog, out_observeExts]
  refine logsRounds_right ?_
  obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
  rw [hlog]
  obtain ⟨_, s₆, h₆, hok, hlog⟩ := out_bind_ok answer hok
  rw [out_forIn_observe] at h₆
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₆)
  rw [hlog, out_forIn_observe]
  refine logsRounds_right ?_
  have har : (arities proof).map (fun a : Nat ↦ (a : F)) ≠ [] := by
    rw [ne_eq, List.map_eq_nil_iff]
    exact hne
  have hs₆ : ((arities proof).map (fun a : Nat ↦ (a : F))).foldl (idealLogged answer).observe
      (if coeffs proof.finalPoly.toList = [] then
        ⟨capAt answer blocks (r + 1 + (proof.commits.toList.zip
          proof.commitWitnesses.toList).length), [], smp₄⟩
      else ⟨capAt answer blocks (r + 1 + (proof.commits.toList.zip
          proof.commitWitnesses.toList).length), [] ++ coeffs proof.finalPoly.toList, []⟩) =
      ⟨capAt answer blocks (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length),
        coeffs proof.finalPoly.toList ++ (arities proof).map (fun a : Nat ↦ (a : F)), []⟩ := by
    rw [foldl_observe, ite_eq_right_of_eq_false _ _ (eq_false har)]
    split
    · rename_i h
      rw [h]
    · rw [List.nil_append]
  rw [hs₆] at hok ⊢
  have hmid : r + 2 + (proof.commits.toList.zip proof.commitWitnesses.toList).length =
      r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length + 1 := by omega
  rw [hmid]
  by_cases hbits : P.queryPowBits = 0
  · simp only [witnessInput, hbits, ↓reduceIte, List.append_nil] at hlast
    obtain ⟨_, s₇, h₇, hok, hlog⟩ := out_bind_ok answer hok
    rw [hbits, out_checkWitness_zero] at h₇
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₇)
    rw [hlog, hbits, out_checkWitness_zero]
    refine logsRounds_right ?_
    obtain ⟨-, hok, hlog⟩ := out_ensure_bind_ok answer hok
    rw [hlog]
    obtain ⟨q₀, qs, hqs⟩ : ∃ q₀ qs, proof.queries.toList = q₀ :: qs := by
      unfold arities at hne
      rcases h : proof.queries.toList with _ | ⟨q₀, qs⟩
      · rw [Array.toList_eq_nil_iff] at h
        simp only [h, Array.getElem?_empty, Option.map_none,
          Option.getD_none, ne_eq, not_true_eq_false] at hne
      · exact ⟨q₀, qs, rfl⟩
    rw [hqs] at hok ⊢
    obtain ⟨_, _, h₈, -, hlog⟩ := out_bind_ok answer hok
    rw [hlog]
    refine logsRounds_left ?_
    rw [List.forIn_cons] at h₈ ⊢
    obtain ⟨_, _, h₉, -, hlog⟩ := out_bind_ok answer h₈
    rw [hlog]
    refine logsRounds_left ?_
    obtain ⟨_, _, -, -, hlog⟩ := out_bind_ok answer h₉
    rw [hlog]
    refine logsRounds_left fun j hlo hhi ↦ ?_
    obtain rfl : j = r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length := by
      omega
    obtain ⟨v, hv⟩ := out_sampleBits_nil answer
      ((arities proof).sum + P.logBlowup + P.logFinalPolyLen)
      (capAt answer blocks (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length))
      (coeffs proof.finalPoly.toList ++ (arities proof).map (fun a : Nat ↦ (a : F)))
    rw [hv]
    simp only [keyAt, hlast, List.map_cons, List.map_nil, List.mem_singleton]
  · simp only [witnessInput, hbits, ↓reduceIte] at hlast
    obtain ⟨v, hv⟩ := out_checkWitness_pos answer _ hbits proof.queryWitness
      (capAt answer blocks (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length))
      (coeffs proof.finalPoly.toList ++ (arities proof).map (fun a : Nat ↦ (a : F))) []
    obtain ⟨_, _, -, -, hlog⟩ := out_bind_ok answer hok
    rw [hlog, hv]
    refine logsRounds_left fun j hlo hhi ↦ ?_
    obtain rfl : j = r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length := by
      omega
    simp only [keyAt, hlast, List.map_cons, List.map_nil, List.mem_singleton]

/-- A loop of steps that only change the state. -/
theorem out_forIn_state {γ : Type} (l : List γ) (body : γ → PUnit → M Hl (ForInStep PUnit))
    (g : γ → Sponge → Sponge)
    (hbody : ∀ a s, out answer (body a PUnit.unit) s = (.ok (.yield PUnit.unit, g a s), []))
    (s : Sponge) :
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
def roundValues (rounds : List Fri.Round) : List EF :=
  rounds.flatMap fun r ↦ r.2.flatMap fun m ↦ m.2.flatMap (·.2)

theorem foldl_coeffs_flatMap {γ : Type} (l : List γ) (f : γ → List EF) (s : Sponge) :
    l.foldl (fun s a ↦ (coeffs (f a)).foldl (idealLogged answer).observe s) s =
      (coeffs (l.flatMap f)).foldl (idealLogged answer).observe s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, coeffs, coeffs, coeffs, List.flatMap_append,
      List.foldl_append]

/-- The commitment scheme: from the round `r` before it, with its values the input of round `r`,
the verifier queries every round of FRI. -/
theorem verifyPcs_logs (hK : P.numQueries + 5 ≤ K) (blocks : List (List F)) (r : Nat)
    (proof : FriProof) (rounds : List Fri.Round) (hne : arities proof ≠ [])
    (hfold : ∀ j (hj : j < (proof.commits.toList.zip proof.commitWitnesses.toList).length),
      blocks.getD (r + 1 + j) [] =
        (proof.commits.toList.zip proof.commitWitnesses.toList)[j].1.toList ++
          witnessInput P.commitPowBits (proof.commits.toList.zip proof.commitWitnesses.toList)[j].2)
    (hlast : blocks.getD (r + 1 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      [] = coeffs proof.finalPoly.toList ++ (arities proof).map (fun a : Nat ↦ (a : F)) ++
        witnessInput P.queryPowBits proof.queryWitness)
    (hvals : coeffs (roundValues rounds) = blocks.getD r []) (hin : blocks.getD r [] ≠ [])
    (cap : Digest) (hcap : cap = capAt answer blocks r) (samples : List F) {res : Unit × Sponge}
    (hok : (out answer (verifyPcs (idealLogged answer) P rounds proof) ⟨cap, [], samples⟩).1 =
      .ok res) :
    LogsRounds answer blocks r
      (r + 2 + (proof.commits.toList.zip proof.commitWitnesses.toList).length)
      (out answer (verifyPcs (idealLogged answer) P rounds proof) ⟨cap, [], samples⟩).2 := by
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
  unfold verifyPcs at hok ⊢
  obtain ⟨_, s₁, h₁, hok, hlog⟩ := out_bind_ok answer hok
  rw [hobs] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hobs]
  refine logsRounds_right ?_
  rw [foldl_observe, ite_eq_right_of_eq_false _ _ (eq_false (hvals ▸ hin)), hvals, hcap,
    List.nil_append] at hok ⊢
  exact verifyFri_logs hK blocks r proof rounds hne hfold hlast hok

theorem coeffs_ne_nil {xs : List EF} (h : xs ≠ []) : coeffs xs ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [coeffs, List.flatMap_cons, List.cons_append, ne_eq, reduceCtorEq, not_false_eq_true]

theorem inputs_getD_fold (P : Fri.Params) (pis : List F) (proof : Proof) (j : Nat)
    (hj : j < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length) :
    (inputs P pis proof).getD (2 + 1 + j) [] =
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].1.toList ++
        witnessInput P.commitPowBits
          (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].2 := by
  rw [inputs, List.getD_eq_getElem?_getD, show 2 + 1 + j = j + 1 + 1 + 1 by omega,
    List.getElem?_append_left (by simp only [List.length_cons, List.length_map]; omega)]
  simp only [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

theorem inputs_getD_last (P : Fri.Params) (pis : List F) (proof : Proof) :
    (inputs P pis proof).getD
      (2 + 1 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length) [] =
      coeffs proof.fri.finalPoly.toList ++
        (Fri.arities proof.fri).map (fun a : Nat ↦ (a : F)) ++
        witnessInput P.queryPowBits proof.fri.queryWitness := by
  rw [inputs, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by simp only [List.length_cons, List.length_map]; omega)]
  simp only [List.length_cons, List.length_map, show ∀ n, 2 + 1 + n - (n + 1 + 1 + 1) = 0 from
    fun n ↦ by omega, List.getElem?_cons_zero, Option.getD_some]

theorem length_inputs (P : Fri.Params) (pis : List F) (proof : Proof) :
    (inputs P pis proof).length =
      2 + 2 + (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length := by
  simp only [inputs, List.length_cons, List.length_append, List.length_map, List.length_nil]
  omega

/-- The verifier's last step: run the challenger part, then a check that queries nothing. -/
theorem run_stateT_bind {α β : Type} (x : M (idealLogged answer) α) (s : Sponge)
    (g : α × Sponge → ExceptT String (WriterT (QueryLog (spec K)) Id) β)
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

/-- **The verifier queries every round.** If the verifier on the logged answers accepts a proof
that folds at least once, its log holds the duplex call of every round of the proof's
schedule. -/
theorem verifyWith_logs (hK : P.numQueries + 5 ≤ K) (A : Air) (proof : Proof) (pis : List F)
    (hfolds : P.logFinalPolyLen < proof.degreeBits)
    (hok : (verifyWith (idealLogged answer) P A proof pis).run.1 = .ok ()) :
    LogsRounds answer (inputs P pis proof) 0 (inputs P pis proof).length
      (verifyWith (idealLogged answer) P A proof pis).run.2 := by
  unfold verifyWith at hok ⊢
  dsimp only at hok ⊢
  split at hok
  · rename_i hshape
    simp only [hshape, ↓reduceIte] at ⊢
    split at hok
    · rename_i harities
      simp only [harities, ↓reduceIte] at ⊢
      rw [run_stateT_bind _ _ _ (fun a ↦ by split <;> rfl)] at hok ⊢
      rcases hrun : out answer _ { cap := initCap, input := [], samples := [] } with ⟨_ | a, w⟩
      · rw [hrun] at hok
        cases hok
      rw [hrun] at hok
      dsimp only
      have hne : Fri.arities proof.fri ≠ [] := by
        rw [beq_iff_eq] at harities
        rw [harities]
        exact Fri.foldArities_ne_nil _ _ (by omega)
      have hrun1 := congrArg Prod.fst hrun
      have hrun2 := congrArg Prod.snd hrun
      dsimp only at hrun1 hrun2
      rw [← hrun2]
      clear hrun hrun2 hok
      -- the observations of the first round
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observeList_nil] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observeList_nil, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observeList_nil] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observeList_nil, List.nil_append]
      have hin₀ : [] ++ [(proof.degreeBits : F)] ++ [(proof.degreeBits : F)] ++ [0] ++
          proof.traceCommit.toList ++ pis = (inputs P pis proof).getD 0 [] := by
        simp only [inputs, List.nil_append, List.cons_append, List.append_assoc,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
      dsimp only at hrun1 ⊢
      rw [hin₀, show initCap = capAt answer (inputs P pis proof) 0 from rfl] at hrun1 ⊢
      -- the round of `α`
      obtain ⟨v₀, hv₀⟩ := out_sampleExt_nil answer (by omega) (capAt answer (inputs P pis proof) 0)
        ((inputs P pis proof).getD 0 [])
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [hv₀] at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, hv₀]
      refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
        List.mem_singleton]) ?_
      rw [show (answer (.duplex (capAt answer (inputs P pis proof) 0)
        ((inputs P pis proof).getD 0 []))).1 = capAt answer (inputs P pis proof) 1 from rfl]
        at hrun1 ⊢
      -- the round of `ζ`
      have hqc : proof.quotientCommit.toList ≠ [] :=
        List.ne_nil_of_length_pos (by simp only [Vector.length_toList]; omega)
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc)] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observeList, ite_eq_right_of_eq_false _ _ (eq_false hqc), List.nil_append]
      have hin₁ : [] ++ proof.quotientCommit.toList = (inputs P pis proof).getD 1 [] := by
        simp only [inputs, List.nil_append, List.getD_eq_getElem?_getD, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      dsimp only at hrun1 ⊢
      rw [hin₁] at hrun1 ⊢
      obtain ⟨v₁, hv₁⟩ := out_sampleExt_nil answer (by omega) (capAt answer (inputs P pis proof) 1)
        ((inputs P pis proof).getD 1 [])
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [hv₁] at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, hv₁]
      refine logsRounds_cons (by simp only [keyAt, List.map_cons, List.map_nil,
        List.mem_singleton]) ?_
      -- the commitment scheme
      obtain ⟨_, s₁, h₁, -, hlog⟩ := out_bind_ok answer hrun1
      rw [hlog]
      refine logsRounds_left ?_
      rw [length_inputs]
      refine verifyPcs_logs hK (inputs P pis proof) 2 proof.fri _ hne
        (fun j hj ↦ inputs_getD_fold P pis proof j hj) (inputs_getD_last P pis proof) ?_ ?_ _ rfl _
        h₁
      · simp only [roundValues, inputs, openedValues, List.flatMap_cons, List.flatMap_nil,
          List.flatMap_map, List.getD_eq_getElem?_getD, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, List.append_nil,
          List.append_assoc]
      · have h2 : (inputs P pis proof).getD 2 [] = coeffs (openedValues proof.opened) := by
          simp only [inputs, List.getD_eq_getElem?_getD, List.cons_append,
            List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
        rw [h2]
        apply coeffs_ne_nil
        simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at hshape
        obtain ⟨⟨-, hsize⟩, hall⟩ := hshape
        have hpos : 0 < proof.opened.quotientChunks.size := by
          rw [hsize]
          exact Nat.two_pow_pos _
        have hmem : proof.opened.quotientChunks[0] ∈ proof.opened.quotientChunks :=
          Array.getElem_mem hpos
        have h4 := hall _ hmem
        intro h
        simp only [openedValues, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
          Array.mem_toList_iff, Array.toList_eq_nil_iff] at h
        have := h.2 _ hmem
        rw [this] at h4
        exact absurd h4 (by simp only [Array.size_empty, OfNat.zero_ne_ofNat, not_false_eq_true])
    · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
      cases hok
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok

end Run

/-! ### The verifier's rounds -/

section Verifier

variable {answer : (q : Query) → Answer K q}

/-- A log of answers by `answer` is answered by `answer`. -/
theorem consistent_tableQueryLog {α : Type} (oa : OracleComp (spec K) α) :
    Consistent answer (tableQueryLog oa answer) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [Consistent, tableQueryLog_pure, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | query_bind t k ih =>
    rw [Consistent, tableQueryLog_query_bind]
    rintro e (_ | ⟨_, he⟩)
    · rfl
    · exact ih _ e he

/-- The verifier on logged answers gives the verifier on the answers, and its log. -/
theorem run_idealLogged (P : Fri.Params) (A : Air) (proof : Proof) (pis : List F) :
    (verifyWith (idealLogged answer) P A proof pis).run =
      (verifyWith (idealOf answer) P A proof pis,
        tableQueryLog (verifyWith (ideal K) P A proof pis) answer) := by
  have h := QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn answer)
    (verifyWith (ideal K) P A proof pis)
  rw [simulateQ_verifyWith, simulateQ_verifyWith] at h
  exact Prod.ext h (tableQueryLog_verifyWith answer P A proof pis).symm

end Verifier

section Setup
variable (S : Iop.Setup KoalaBear.Fast.Ext4) (answer : (q : Query) → Answer S.streamLen q)

/-- **The verifier queries every round.** If the verifier accepts a proof for `2 ^ logN` rows on
the answers `answer`, the duplex call of every round of the proof's schedule is in its log. -/
theorem hasRounds_verifyWith (proof : Proof) (pis : List F) (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    HasRounds answer (tableQueryLog (verifyWith (ideal S.streamLen) S.params S.air proof pis)
      answer) (inputs S.params pis proof) (inputs S.params pis proof).length := by
  have h := verifyWith_logs (answer := answer) (P := S.params) (le_refl _) S.air proof pis
    (by have := S.folds; omega) (by rw [run_idealLogged]; exact hok)
  rw [run_idealLogged] at h
  exact fun j hj ↦ h j (Nat.zero_le j) hj

/-- **Parsing the verifier's rounds.** If the verifier accepts a proof for `2 ^ logN` rows on the
answers `answer`, and its duplex calls answer distinct capacities, none the initial one, then its
log before round `i`'s call parses that call to the rounds before it and its input: the
proof's prefix up to round `i`. -/
theorem parse_verifyWith (proof : Proof) (pis : List F) (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ())
    (hinj : CapsInjective answer
      (tableQueryLog (verifyWith (ideal S.streamLen) S.params S.air proof pis) answer))
    (i : Nat) (hi : i ≤ (inputs S.params pis proof).length) :
    parse (tableQueryLog (verifyWith (ideal S.streamLen) S.params S.air proof pis) answer)
        (keyAt answer (inputs S.params pis proof) i) =
      some (history answer (inputs S.params pis proof) i, (inputs S.params pis proof).getD i []) :=
  parse_keyAt (consistent_tableQueryLog _) hinj
    fun j hj ↦ hasRounds_verifyWith S answer proof pis hdb hok j (by omega)

end Setup

/-! ### Reading challenges off a round -/

/-- The extension element of four samples from `offset` on, lowest coefficient first, in `𝕂`. -/
def extAt (samples : Vector F K) (offset : Nat) : KoalaBear.Ext4 :=
  KoalaBear.Fast.Ext4.specEquiv ⟨samples.toList.getD offset 0, samples.toList.getD (offset + 1) 0,
    samples.toList.getD (offset + 2) 0, samples.toList.getD (offset + 3) 0⟩

/-- The challenges of the rounds, in the order of `inputs`: `α`, `ζ` and the batching challenge
take the first four samples of rounds `0`, `1` and `2`; fold `i`'s grinding sample is the first
sample of round `3 + i` and its `β_i` the next four (the first four without commit grinding); the
query round's grinding sample is its first sample, and the query indices the next ones (from the
first without query grinding). -/
def challengeOffset (bits : Nat) : Nat := if bits = 0 then 0 else 1

end CompStark.Ni
