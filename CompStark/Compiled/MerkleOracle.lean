/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.MerkleTrace
public import CompStark.Keccak.Commit.Merkle
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Merkle computations against the raw-byte hash oracle. A run of a program under the lazy
`handler` evaluates it at every table that agrees with the final log, and logs every input it
queries at that table (`run_table`). The oracle versions of the batch expansion (`expandO`) and of
an opening's climb (`climbO`) evaluate to `Commit.expand` and query the bytes of every operation the
opening computes (`climbO_covers`), within fixed query budgets. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Compiled.MerkleOracle
open CompStark.BinaryFields MixedMerkleTree.Knowledge
open OracleComp OracleSpec Interaction.Oracle.Security
open Keccak.Commit.RandomOracleTrace

variable {Key : Type} {Response : Key → Type}

/-- A complete answer table of the joint hash and challenge oracle. -/
abbrev Table (Response : Key → Type) := (query : ByteArray ⊕ Key) → (MerkleTrace.Spec Response).Range query

/-- The raw-byte hash a table answers. -/
def Table.hash (table : Table Response) : ByteArray → Keccak.Commit.Digest := fun input => table (.inl input)

/-- The inputs of a log's hash queries. -/
def inputs : QueryLog (MerkleTrace.Spec Response) → List ByteArray
  | [] => []
  | ⟨.inl input, _⟩ :: log => input :: inputs log
  | ⟨.inr _, _⟩ :: log => inputs log

/-- A logged hash query's input is among the log's inputs. -/
theorem mem_inputs {log : QueryLog (MerkleTrace.Spec Response)} {input : ByteArray}
    (member : Sum.inl input ∈ log.map Sigma.fst) : input ∈ inputs log := by
  induction log with
  | nil => cases member
  | cons entry log ih =>
    rcases entry with ⟨query, answer⟩
    rcases List.mem_cons.mp member with same | rest
    · cases same; exact List.mem_cons_self ..
    · cases query with
      | inl other => exact List.mem_cons_of_mem _ (ih rest)
      | inr _ => exact ih rest

/-- A cached key is logged. -/
theorem key_mem_of_cacheOf [DecidableEq Key] {log : QueryLog (MerkleTrace.Spec Response)}
    {t : ByteArray ⊕ Key} {value : (MerkleTrace.Spec Response).Range t}
    (known : Bcs.cacheOf log t = some value) : t ∈ log.map Sigma.fst := by
  by_contra absent
  have none : Bcs.cacheOf log t = none := by
    induction log with
    | nil => rfl
    | cons e log ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      exact Bcs.cacheOf_cons_eq_none.mpr ⟨Ne.symm absent.1, ih (by
        simpa only [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ absent.1] using known)
        absent.2⟩
  rw [known] at none
  cases none

/-- A run under the lazy handler evaluates its program at every table agreeing with the final log,
extends its starting log, and logs every query it makes at that table. -/
theorem run_table [DecidableEq Key] [∀ key, SampleableType (Response key)] {α : Type}
    (program : OracleComp (MerkleTrace.Spec Response) α) (start : QueryLog (MerkleTrace.Spec Response))
    (result : α × QueryLog (MerkleTrace.Spec Response))
    (member : result ∈ support ((simulateQ handler program).run start))
    (table : Table Response) (agrees : Agrees table result.2) :
    evalWithAnswerFn (QueryImpl.ofFn table) program = result.1 ∧ (∃ fresh, result.2 = fresh ++ start) ∧
      ∀ entry ∈ tableQueryLog program table, entry.1 ∈ result.2.map Sigma.fst := by
  induction program using OracleComp.inductionOn generalizing start result with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at member
    subst member
    exact ⟨rfl, ⟨[], rfl⟩, by simp only [tableQueryLog_pure, List.not_mem_nil, false_implies, implies_true]⟩
  | query_bind t next ih =>
    have step : result ∈ support (((simulateQ handler
        (OracleSpec.query t : OracleComp (MerkleTrace.Spec Response) _)).run start) >>=
          fun us => (simulateQ handler (next us.1)).run us.2) := by
      simpa [simulateQ_bind, OracleComp.liftM_def] using member
    obtain ⟨us, hus, rest⟩ := (mem_support_bind_iff _ _ _).1 step
    have hus' : us ∈ support ((handler t).run start) := by simpa [simulateQ_spec_query] using hus
    obtain ⟨evaluated, ⟨fresh, suffix⟩, logged⟩ := ih us.1 us.2 result rest agrees
    -- the answer and the log after the query
    have answered : table t = us.1 ∧ t ∈ us.2.map Sigma.fst ∧ ∃ added, us.2 = added ++ start := by
      simp only [handler, StateT.run_mk] at hus'
      cases known : Bcs.cacheOf start t with
      | some value =>
        rw [known, mem_support_pure_iff] at hus'
        subst hus'
        have agreesStart : Agrees table start := fun e he => agrees e (by
          rw [suffix]; exact List.mem_append_right _ he)
        exact ⟨cache_eq_table table start agreesStart t value known, key_mem_of_cacheOf known, ⟨[], rfl⟩⟩
      | none =>
        rw [known, mem_support_bind_iff] at hus'
        obtain ⟨value, _, pushed⟩ := hus'
        rw [mem_support_pure_iff] at pushed
        subst pushed
        refine ⟨agrees _ (by rw [suffix]; exact List.mem_append_right _ (List.mem_cons_self ..)),
          List.mem_cons_self .., ⟨[⟨t, value⟩], rfl⟩⟩
    obtain ⟨tableAnswer, queried, added, grown⟩ := answered
    refine ⟨?_, ⟨fresh ++ added, by rw [suffix, grown, List.append_assoc]⟩, ?_⟩
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableAnswer]
      exact evaluated
    · intro entry member
      rw [tableQueryLog_query_bind, tableAnswer] at member
      rcases List.mem_cons.mp member with same | later
      · subst same
        rw [suffix]
        exact List.mem_map.mpr (by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp queried
          exact ⟨e, List.mem_append_right _ he, rfl⟩)
      · exact logged entry later

/-- One raw-byte hash query. -/
def hashO (input : ByteArray) : OracleComp (MerkleTrace.Spec Response) Keccak.Commit.Digest :=
  liftM ((MerkleTrace.Spec Response).query (.inl input))

/-- A hash query evaluates to the table's hash. -/
@[simp] theorem eval_hashO (table : Table Response) (input : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn table) (hashO input) = table.hash input := rfl

/-- A hash query logs its input. -/
@[simp] theorem tableQueryLog_hashO (table : Table Response) (input : ByteArray) :
    tableQueryLog (hashO input) table = [⟨.inl input, table.hash input⟩] :=
  tableQueryLog_query _ _

/-- A hash query costs one query. -/
theorem hashO_bound (input : ByteArray) : IsTotalQueryBound (hashO (Response := Response) input) 1 := by
  rw [hashO, ← bind_pure (liftM _), isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

/-- The bytes of an ordered child pair. -/
def pairBytes (left right : Keccak.Commit.Digest) : ByteArray := ⟨left.toArray ++ right.toArray⟩

/-- The bytes of a child and its sibling, ordered by the child's index. -/
def pairUpBytes (index : ℕ) (x s : Keccak.Commit.Digest) : ByteArray :=
  if index % 2 = 0 then pairBytes x s else pairBytes s x

/-- Pairing up hashes the ordered pair's bytes. -/
theorem pairUp_hash (hash : ByteArray → Keccak.Commit.Digest) (index : ℕ) (x s : Keccak.Commit.Digest) :
    MixedMerkleTree.pairUp (Keccak.Commit.pairWith hash) index x s = hash (pairUpBytes index x s) := by
  unfold MixedMerkleTree.pairUp pairUpBytes
  split <;> rfl

/-- Climbing past one more sibling, without injections, pairs the running digest with it. -/
theorem climb_append (hash : List K → Keccak.Commit.Digest)
    (compress : Keccak.Commit.Digest → Keccak.Commit.Digest → Keccak.Commit.Digest)
    (path : List Keccak.Commit.Digest) (index : ℕ) (x s : Keccak.Commit.Digest) :
    MixedMerkleTree.climb hash compress (fun _ => none) index x (path ++ [s]) =
      MixedMerkleTree.pairUp compress (index >>> path.length)
        (MixedMerkleTree.climb hash compress (fun _ => none) index x path) s := by
  induction path generalizing index x with
  | nil => rfl
  | cons a path ih =>
    have step : ∀ (i : ℕ) (y : Keccak.Commit.Digest) (rest : List Keccak.Commit.Digest),
        MixedMerkleTree.climb hash compress (fun _ => none) i y (a :: rest) =
          MixedMerkleTree.climb hash compress (fun _ => none) (i / 2) (MixedMerkleTree.pairUp compress i y a)
            rest := fun _ _ _ => rfl
    have shift : (index / 2) >>> path.length = index >>> (path.length + 1) := by
      simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [List.cons_append, step, step, ih, List.length_cons, shift]

/-- Climbing one level further than a prefix of the siblings. -/
theorem climb_take_succ (hash : List K → Keccak.Commit.Digest)
    (compress : Keccak.Commit.Digest → Keccak.Commit.Digest → Keccak.Commit.Digest)
    (path : List Keccak.Commit.Digest) (index : ℕ) (x : Keccak.Commit.Digest) (l : ℕ) :
    MixedMerkleTree.climb hash compress (fun _ => none) index x (path.take (l + 1)) =
      if h : l < path.length then
        MixedMerkleTree.pairUp compress (index >>> l)
          (MixedMerkleTree.climb hash compress (fun _ => none) index x (path.take l)) path[l]
      else MixedMerkleTree.climb hash compress (fun _ => none) index x (path.take l) := by
  split
  · rename_i h
    rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, climb_append,
      List.length_take, Nat.min_eq_left (by omega)]
  · rename_i h
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- The oracle climb's levels from `l`: at each, the ordered pair of the running digest and the
sibling, the running digest moving up while siblings remain. -/
def climbStepsO (index : ℕ) (default : Keccak.Commit.Digest) (siblings : List Keccak.Commit.Digest) :
    ℕ → ℕ → Keccak.Commit.Digest → OracleComp (MerkleTrace.Spec Response) Unit
  | 0, _, _ => pure ()
  | n + 1, l, x => do
    let z ← hashO (pairUpBytes (index >>> l) x (siblings.getD l default))
    climbStepsO index default siblings n (l + 1) (if l < siblings.length then z else x)

/-- An opening's climb against the oracle: the default leaf, the leaf, then the lowest
`height + 1` levels. -/
def climbO (height : ℕ) (path : Keccak.Commit.Path) : OracleComp (MerkleTrace.Spec Response) Unit := do
  let default ← hashO (Keccak.Commit.leafBytes [])
  let leaf ← hashO (Keccak.Commit.leafBytes path.leaf)
  climbStepsO path.index default path.siblings (height + 1) 0 leaf

/-- The oracle climb's levels cost one query each. -/
theorem climbStepsO_bound (index : ℕ) (default : Keccak.Commit.Digest) (siblings : List Keccak.Commit.Digest) :
    (n l : ℕ) → (x : Keccak.Commit.Digest) →
      IsTotalQueryBound (climbStepsO (Response := Response) index default siblings n l x) n
  | 0, _, _ => trivial
  | n + 1, l, x => by
    rw [climbStepsO, hashO, isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.succ_pos _, fun _ => climbStepsO_bound index default siblings n _ _⟩

/-- An oracle climb costs `height + 3` queries. -/
theorem climbO_bound (height : ℕ) (path : Keccak.Commit.Path) :
    IsTotalQueryBound (climbO (Response := Response) height path) (height + 3) := by
  unfold climbO hashO
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => climbStepsO_bound _ _ _ _ _ _⟩

/-- The running digest of an opening's climb after its lowest `l` siblings, without injections. -/
def climbTake (hash : ByteArray → Keccak.Commit.Digest) (path : Keccak.Commit.Path) (l : ℕ) :
    Keccak.Commit.Digest :=
  MixedMerkleTree.climb (Keccak.Commit.leafWith hash) (Keccak.Commit.pairWith hash) (fun _ => none)
    path.index (Keccak.Commit.leafWith hash path.leaf) (path.siblings.take l)

/-- The oracle climb's levels from `l`, started at the running digest after `l` siblings, query
every later level's ordered pair. -/
theorem climbStepsO_covers (table : Table Response) (path : Keccak.Commit.Path) :
    (n l : ℕ) → (j : ℕ) → l ≤ j → j < l + n →
      Sum.inl (pairUpBytes (path.index >>> j) (climbTake table.hash path j)
        (path.siblings.getD j (table.hash (Keccak.Commit.leafBytes [])))) ∈
      (tableQueryLog (climbStepsO path.index (table.hash (Keccak.Commit.leafBytes [])) path.siblings n l
        (climbTake table.hash path l)) table).map Sigma.fst
  | 0, _, _, low, high => by omega
  | n + 1, l, j, low, high => by
    rw [climbStepsO, hashO, tableQueryLog_query_bind, List.map_cons, List.mem_cons]
    by_cases same : j = l
    · subst same
      exact Or.inl rfl
    · right
      have next : (if l < path.siblings.length then
          table (.inl (pairUpBytes (path.index >>> l) (climbTake table.hash path l)
            (path.siblings.getD l (table.hash (Keccak.Commit.leafBytes []))))) else
          climbTake table.hash path l) = climbTake table.hash path (l + 1) := by
        unfold climbTake
        rw [climb_take_succ]
        by_cases h : l < path.siblings.length
        · simp only [h, ↓reduceIte, ↓reduceDIte, pairUp_hash]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
          rfl
        · simp only [h, ↓reduceIte, ↓reduceDIte]
      have rest := climbStepsO_covers table path n (l + 1) j (by omega) (by omega)
      rw [← next] at rest
      exact rest

/-- An oracle climb of height `height` queries the bytes of every operation the opening computes
at a position of a tree of that height without injections. -/
theorem climbO_covers (table : Table Response) (height : ℕ) (path : Keccak.Commit.Path)
    (v : Position) (op : Op (List K) Keccak.Commit.Digest)
    (member : op ∈ Opening.ops (Keccak.Commit.leafWith table.hash) (Keccak.Commit.pairWith table.hash) []
      height 0 v path.toMixed) :
    Sum.inl (Keccak.Commit.operationBytes op) ∈ (tableQueryLog (climbO height path) table).map Sigma.fst := by
  unfold climbO hashO
  rw [tableQueryLog_query_bind, List.map_cons, List.mem_cons, tableQueryLog_query_bind, List.map_cons,
    List.mem_cons]
  right
  unfold Opening.ops at member
  split at member
  · rcases hv : v.stage with _ | _ | _ | _ <;> rw [hv] at member
    · rw [List.mem_singleton] at member
      subst member
      exact Or.inl rfl
    · rw [List.mem_singleton] at member
      subst member
      right
      have covered := climbStepsO_covers table path (height + 1) 0 (height - v.depth - 1) (Nat.zero_le _)
        (by omega)
      have bytes : Keccak.Commit.operationBytes (.inr (path.toMixed.childPair (Keccak.Commit.leafWith table.hash)
          (Keccak.Commit.pairWith table.hash) [] height 0 v.depth)) =
          pairUpBytes (path.index >>> (height - v.depth - 1)) (climbTake table.hash path (height - v.depth - 1))
            (path.siblings.getD (height - v.depth - 1) (table.hash (Keccak.Commit.leafBytes []))) := by
        unfold Opening.childPair Opening.digest pairUpBytes
        simp only [Keccak.Commit.Path.toMixed, Nat.sub_zero, climbTake]
        split <;> rfl
      rw [bytes]
      exact covered
    · simp only [Keccak.Commit.Path.toMixed, Option.toList_none, List.map_nil, List.not_mem_nil] at member
    · simp only [Keccak.Commit.Path.toMixed, Option.toList_none, List.map_nil, List.not_mem_nil] at member
  · cases member

/-- Returning a value makes no query. -/
theorem pure_bound {β : Type} (b : β) : IsTotalQueryBound (pure b : OracleComp (MerkleTrace.Spec Response) β) 0 :=
  isTotalQueryBound_zero_iff.mpr ⟨b, rfl⟩

/-- A list map with one budget per element. -/
theorem mapM_bound {α β : Type} (f : α → OracleComp (MerkleTrace.Spec Response) β) (c : ℕ)
    (each : ∀ x, IsTotalQueryBound (f x) c) : (l : List α) → IsTotalQueryBound (l.mapM f) (l.length * c)
  | [] => trivial
  | x :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isTotalQueryBound_bind (each x) fun _ =>
      by simpa only [Nat.add_zero] using isTotalQueryBound_bind (mapM_bound f c each l) fun _ => pure_bound _

/-- A list map evaluates elementwise. -/
theorem eval_mapM {α β : Type} (table : Table Response) (f : α → OracleComp (MerkleTrace.Spec Response) β) :
    (l : List α) → evalWithAnswerFn (QueryImpl.ofFn table) (l.mapM f) =
      l.map fun x => evalWithAnswerFn (QueryImpl.ofFn table) (f x)
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_mapM table f l]
    rfl

/-- One bottom-up level against the oracle: `Commit.expandLevel` with each parent hash queried. -/
def expandLevelO : ℕ → List (ℕ × Keccak.Commit.Digest) → List Keccak.Commit.Digest →
    OracleComp (MerkleTrace.Spec Response)
      (Option (List (ℕ × Keccak.Commit.Digest) × List (ℕ × Keccak.Commit.Digest) × List Keccak.Commit.Digest))
  | _, [], hints => pure (some ([], [], hints))
  | 0, _ :: _, _ => pure none
  | fuel + 1, (i, x) :: rest, hints =>
    match rest with
    | (j, y) :: tail =>
      if i % 2 = 0 ∧ j = i + 1 then do
        let z ← hashO (pairBytes x y)
        let r ← expandLevelO fuel tail hints
        pure (r.map fun r => ((i / 2, z) :: r.1, (i, y) :: (j, x) :: r.2.1, r.2.2))
      else
        match hints.head? with
        | none => pure none
        | some sibling => do
          let z ← hashO (pairUpBytes i x sibling)
          let r ← expandLevelO fuel rest hints.tail
          pure (r.map fun r => ((i / 2, z) :: r.1, (i, sibling) :: r.2.1, r.2.2))
    | [] =>
      match hints.head? with
      | none => pure none
      | some sibling => do
        let z ← hashO (pairUpBytes i x sibling)
        pure (some ([(i / 2, z)], [(i, sibling)], hints.tail))

/-- An oracle level evaluates to the level under the table's hash. -/
theorem eval_expandLevelO (table : Table Response) :
    (fuel : ℕ) → (nodes : List (ℕ × Keccak.Commit.Digest)) → (hints : List Keccak.Commit.Digest) →
      evalWithAnswerFn (QueryImpl.ofFn table) (expandLevelO fuel nodes hints) =
        Keccak.Commit.expandLevel table.hash fuel nodes hints
  | fuel, [], hints => by rw [expandLevelO.eq_1, Keccak.Commit.expandLevel.eq_1]; rfl
  | 0, _ :: _, _ => by rw [expandLevelO.eq_2, Keccak.Commit.expandLevel.eq_2]; rfl
  | fuel + 1, [(i, x)], hints => by
    rw [expandLevelO, Keccak.Commit.expandLevel.eq_4]
    cases hints with
    | nil => rfl
    | cons sibling hints =>
      simp only [List.head?_cons, List.tail_cons, evalWithAnswerFn_bind, eval_hashO, evalWithAnswerFn_pure,
        ← pairUp_hash]
      rfl
  | fuel + 1, (i, x) :: (j, y) :: tail, hints => by
    rw [expandLevelO, Keccak.Commit.expandLevel.eq_3]
    by_cases paired : i % 2 = 0 ∧ j = i + 1
    · simp only [paired, and_self, ↓reduceIte]
      simp only [evalWithAnswerFn_bind, eval_hashO, evalWithAnswerFn_pure,
        eval_expandLevelO table fuel tail hints]
      cases Keccak.Commit.expandLevel table.hash fuel tail hints <;> rfl
    · simp only [paired, ↓reduceIte]
      cases hints with
      | nil => rfl
      | cons sibling hints =>
        simp only [List.head?_cons, List.tail_cons, evalWithAnswerFn_bind, eval_hashO, evalWithAnswerFn_pure,
          eval_expandLevelO table fuel ((j, y) :: tail) hints, ← pairUp_hash]
        cases Keccak.Commit.expandLevel table.hash fuel ((j, y) :: tail) hints <;> rfl

/-- An oracle level queries at most once per node. -/
theorem expandLevelO_bound :
    (fuel : ℕ) → (nodes : List (ℕ × Keccak.Commit.Digest)) → (hints : List Keccak.Commit.Digest) →
      IsTotalQueryBound (expandLevelO (Response := Response) fuel nodes hints) nodes.length
  | fuel, [], hints => by rw [expandLevelO.eq_1]; exact (pure_bound _).mono (Nat.zero_le _)
  | 0, _ :: _, _ => by rw [expandLevelO.eq_2]; exact (pure_bound _).mono (Nat.zero_le _)
  | fuel + 1, [(i, x)], hints => by
    rw [expandLevelO]
    cases hints with
    | nil => exact (pure_bound _).mono (Nat.zero_le _)
    | cons sibling hints =>
      refine IsTotalQueryBound.mono (n₁ := 1 + 0) ?_ (by simp)
      exact isTotalQueryBound_bind (hashO_bound _) fun _ => pure_bound _
  | fuel + 1, (i, x) :: (j, y) :: tail, hints => by
    rw [expandLevelO]
    by_cases paired : i % 2 = 0 ∧ j = i + 1
    · simp only [paired, and_self, ↓reduceIte]
      refine IsTotalQueryBound.mono (n₁ := 1 + (tail.length + 0)) ?_ (by simp only [List.length_cons]; omega)
      exact isTotalQueryBound_bind (hashO_bound _) fun _ =>
        isTotalQueryBound_bind (expandLevelO_bound fuel tail hints) fun _ => pure_bound _
    · simp only [paired, ↓reduceIte]
      cases hints with
      | nil => exact (pure_bound _).mono (Nat.zero_le _)
      | cons sibling hints =>
        refine IsTotalQueryBound.mono (n₁ := 1 + (((j, y) :: tail).length + 0)) ?_
          (by simp only [List.length_cons]; omega)
        exact isTotalQueryBound_bind (hashO_bound _) fun _ =>
          isTotalQueryBound_bind (expandLevelO_bound fuel ((j, y) :: tail) hints) fun _ => pure_bound _

/-- A level has at most one parent per node. -/
theorem expandLevel_parents (hash : ByteArray → Keccak.Commit.Digest) :
    (fuel : ℕ) → (nodes : List (ℕ × Keccak.Commit.Digest)) → (hints : List Keccak.Commit.Digest) →
      ∀ result, Keccak.Commit.expandLevel hash fuel nodes hints = some result → result.1.length ≤ nodes.length
  | fuel, [], hints, result, h => by
    rw [Keccak.Commit.expandLevel.eq_1, Option.some.injEq] at h
    subst h
    exact Nat.zero_le _
  | 0, _ :: _, _, _, h => by rw [Keccak.Commit.expandLevel.eq_2] at h; cases h
  | fuel + 1, [(i, x)], hints, result, h => by
    rw [Keccak.Commit.expandLevel.eq_4] at h
    obtain ⟨sibling, -, h⟩ := Option.bind_eq_some_iff.mp h
    rw [Option.pure_def, Option.some.injEq] at h
    subst h
    exact le_rfl
  | fuel + 1, (i, x) :: (j, y) :: tail, hints, result, h => by
    rw [Keccak.Commit.expandLevel.eq_3] at h
    by_cases paired : i % 2 = 0 ∧ j = i + 1
    · simp only [paired, and_self, ↓reduceIte] at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      rw [Option.pure_def, Option.some.injEq] at h
      subst h
      have := expandLevel_parents hash fuel tail hints r hr
      simp only [List.length_cons]
      omega
    · simp only [paired, ↓reduceIte] at h
      obtain ⟨sibling, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      rw [Option.pure_def, Option.some.injEq] at h
      subst h
      have := expandLevel_parents hash fuel _ _ r hr
      simp only [List.length_cons] at this ⊢
      omega

/-- Each path reads its sibling at a level from the level's sibling table. -/
def extendPaths (siblings : List (ℕ × Keccak.Commit.Digest)) (level : ℕ) (paths : List Keccak.Commit.Path) :
    Option (List Keccak.Commit.Path) :=
  paths.mapM fun p => do
    let sibling ← List.lookup (p.index >>> level) siblings
    pure { index := p.index, leaf := p.leaf, siblings := p.siblings ++ [sibling] }

/-- All levels against the oracle: `Commit.expandLevels` with each level's parent hashes queried. -/
def expandLevelsO : ℕ → ℕ → List (ℕ × Keccak.Commit.Digest) → List Keccak.Commit.Path →
    List Keccak.Commit.Digest → OracleComp (MerkleTrace.Spec Response)
      (Option (List (ℕ × Keccak.Commit.Digest) × List Keccak.Commit.Path × List Keccak.Commit.Digest))
  | 0, _, nodes, paths, hints => pure (some (nodes, paths, hints))
  | remaining + 1, level, nodes, paths, hints => do
    let r ← expandLevelO nodes.length nodes hints
    match r with
    | none => pure none
    | some (parents, siblings, unused) =>
      match extendPaths siblings level paths with
      | none => pure none
      | some paths => expandLevelsO remaining (level + 1) (parents.take nodes.length) paths unused

/-- A level's expansion step: the level, then the paths' siblings, then the next levels. -/
theorem expandLevels_succ (hash : ByteArray → Keccak.Commit.Digest) (remaining level : ℕ)
    (nodes : List (ℕ × Keccak.Commit.Digest)) (paths : List Keccak.Commit.Path) (hints : List Keccak.Commit.Digest) :
    Keccak.Commit.expandLevels hash (remaining + 1) level nodes paths hints =
      (Keccak.Commit.expandLevel hash nodes.length nodes hints).bind fun x =>
        (extendPaths x.2.1 level paths).bind fun extended =>
          Keccak.Commit.expandLevels hash remaining (level + 1) x.1 extended x.2.2 := by
  rw [Keccak.Commit.expandLevels.eq_2]
  rfl

/-- The oracle levels evaluate to the levels under the table's hash. -/
theorem eval_expandLevelsO (table : Table Response) :
    (remaining level : ℕ) → (nodes : List (ℕ × Keccak.Commit.Digest)) → (paths : List Keccak.Commit.Path) →
      (hints : List Keccak.Commit.Digest) →
      evalWithAnswerFn (QueryImpl.ofFn table) (expandLevelsO remaining level nodes paths hints) =
        Keccak.Commit.expandLevels table.hash remaining level nodes paths hints
  | 0, _, _, _, _ => rfl
  | remaining + 1, level, nodes, paths, hints => by
    rw [expandLevelsO, expandLevels_succ, evalWithAnswerFn_bind, eval_expandLevelO]
    have parents := expandLevel_parents table.hash nodes.length nodes hints
    rcases h : Keccak.Commit.expandLevel table.hash nodes.length nodes hints with _ | ⟨ps, siblings, unused⟩
    · rfl
    · have short := parents _ h
      show evalWithAnswerFn (QueryImpl.ofFn table) (match extendPaths siblings level paths with
        | none => pure none
        | some paths => expandLevelsO remaining (level + 1) (ps.take nodes.length) paths unused) =
          (extendPaths siblings level paths).bind _
      cases extendPaths siblings level paths with
      | none => rfl
      | some extended =>
        show evalWithAnswerFn (QueryImpl.ofFn table)
          (expandLevelsO remaining (level + 1) (ps.take nodes.length) extended unused) = _
        rw [List.take_of_length_le short, eval_expandLevelsO table remaining (level + 1) ps extended unused]
        rfl

/-- The oracle levels query at most once per node and level. -/
theorem expandLevelsO_bound :
    (remaining level : ℕ) → (nodes : List (ℕ × Keccak.Commit.Digest)) → (paths : List Keccak.Commit.Path) →
      (hints : List Keccak.Commit.Digest) →
      IsTotalQueryBound (expandLevelsO (Response := Response) remaining level nodes paths hints)
        (remaining * nodes.length)
  | 0, _, _, _, _ => (pure_bound _).mono (Nat.zero_le _)
  | remaining + 1, level, nodes, paths, hints => by
    rw [expandLevelsO]
    refine IsTotalQueryBound.mono (n₁ := nodes.length + remaining * nodes.length) ?_ (by rw [Nat.succ_mul]; omega)
    refine isTotalQueryBound_bind (expandLevelO_bound _ _ _) fun r => ?_
    rcases r with _ | ⟨parents, siblings, unused⟩
    · exact (pure_bound _).mono (Nat.zero_le _)
    · dsimp only
      cases extendPaths siblings level paths with
      | none => exact (pure_bound _).mono (Nat.zero_le _)
      | some extended =>
        exact (expandLevelsO_bound remaining (level + 1) _ extended unused).mono
          (Nat.mul_le_mul_left _ (by rw [List.length_take]; exact Nat.min_le_left _ _))

/-- Deduplication keeps at most its input. -/
theorem eraseDupsBy_loop_length {α : Type} (r : α → α → Bool) :
    (as bs : List α) → (List.eraseDupsBy.loop r as bs).length ≤ as.length + bs.length
  | [], bs => by simp [List.eraseDupsBy.loop]
  | a :: as, bs => by
    unfold List.eraseDupsBy.loop
    split
    · have := eraseDupsBy_loop_length r as bs
      simp only [List.length_cons]; omega
    · have := eraseDupsBy_loop_length r as (a :: bs)
      simp only [List.length_cons] at this ⊢; omega

/-- The distinct query positions are at most the queries. -/
theorem positions_length (queries : List ℕ) : (Keccak.Commit.positions queries).length ≤ queries.length := by
  unfold Keccak.Commit.positions List.eraseDups List.eraseDupsBy
  have := eraseDupsBy_loop_length (· == ·) (queries.mergeSort (· ≤ ·)) []
  simpa only [List.length_mergeSort, List.length_nil, Nat.add_zero] using this

/-- The batch's root and the query-ordered paths after all levels. -/
def finishExpand (queries : List ℕ) :
    Option (List (ℕ × Keccak.Commit.Digest) × List Keccak.Commit.Path × List Keccak.Commit.Digest) →
      Option (Keccak.Commit.Digest × List Keccak.Commit.Path)
  | none => none
  | some (nodes, paths, unused) =>
    if (!unused.isEmpty) = true then none
    else do
      let top ← nodes.head?
      let ordered ← List.mapM (fun i => List.find? (fun p => p.index == i) paths) queries
      pure (top.2, ordered)

/-- The batch expansion against the oracle: `Commit.expand` with every leaf and parent hash queried. -/
def expandO (height rowWords leafWords : ℕ) (queries : List ℕ) (batch : Keccak.Commit.Pruned) :
    OracleComp (MerkleTrace.Spec Response) (Option (Keccak.Commit.Digest × List Keccak.Commit.Path)) :=
  let ps := Keccak.Commit.positions queries
  if ((ps.isEmpty || !ps.all fun x => decide (x < 2 ^ height)) || ps.length != batch.leafData.length ||
        decide (rowWords > leafWords) || !batch.leafData.all fun row => row.length == rowWords) = true then
    pure none
  else do
    let paths := (ps.zip batch.leafData).map fun (i, row) =>
      ({ index := i, leaf := Keccak.Commit.restoreLeaf leafWords row, siblings := [] } : Keccak.Commit.Path)
    let nodes ← paths.mapM fun p => do
      let digest ← hashO (Keccak.Commit.leafBytes p.leaf)
      pure (p.index, digest)
    let r ← expandLevelsO height 0 (nodes.take queries.length) paths batch.siblingHashes
    pure (finishExpand queries r)

/-- The oracle expansion evaluates to the expansion under the table's hash. -/
theorem eval_expandO (table : Table Response) (height rowWords leafWords : ℕ) (queries : List ℕ)
    (batch : Keccak.Commit.Pruned) :
    evalWithAnswerFn (QueryImpl.ofFn table) (expandO height rowWords leafWords queries batch) =
      Keccak.Commit.expand table.hash height rowWords leafWords queries batch := by
  unfold expandO Keccak.Commit.expand
  dsimp only
  split
  · rfl
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_mapM, eval_hashO]
    rw [List.take_of_length_le (by
      simp only [List.length_map, List.length_zip]
      exact (Nat.min_le_left _ _).trans (positions_length queries)), eval_expandLevelsO]
    rcases Keccak.Commit.expandLevels table.hash height 0 _ _ batch.siblingHashes with _ | ⟨nodes, paths, unused⟩
    · rfl
    · rfl

/-- The oracle expansion queries at most once per query and level, plus once per leaf. -/
theorem expandO_bound (height rowWords leafWords : ℕ) (queries : List ℕ) (batch : Keccak.Commit.Pruned) :
    IsTotalQueryBound (expandO (Response := Response) height rowWords leafWords queries batch)
      (queries.length * (height + 1)) := by
  unfold expandO
  dsimp only
  split
  · exact (pure_bound _).mono (Nat.zero_le _)
  · refine IsTotalQueryBound.mono (n₁ := queries.length * 1 + (height * queries.length + 0)) ?_
      (by rw [Nat.mul_succ]; nlinarith)
    refine isTotalQueryBound_bind ((mapM_bound _ 1 (fun _ =>
      isTotalQueryBound_bind (hashO_bound _) fun _ => pure_bound _) _).mono ?_) fun nodes => ?_
    · simp only [List.length_map, List.length_zip]
      exact Nat.mul_le_mul_right _ ((Nat.min_le_left _ _).trans (positions_length queries))
    · refine isTotalQueryBound_bind ((expandLevelsO_bound _ _ _ _ _).mono ?_) fun _ => pure_bound _
      exact Nat.mul_le_mul_left _ (by rw [List.length_take]; exact Nat.min_le_left _ _)

end CompStark.Compiled.MerkleOracle
