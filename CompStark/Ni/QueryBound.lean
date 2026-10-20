/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.Monad.Support
public import Mathlib.Tactic.Ring

/-! # The verifier's oracle calls

The verifier makes at most `Setup.verifierQueries` oracle calls on a proof for `2 ^ logN` rows
(`isTotalQueryBound_verifyWith`), and so does the game's verifier on every proof
(`isTotalQueryBound_verifyRo`). The shape checks come before the hashing: a Merkle opening with a
path of the wrong length hashes nothing.

The count runs through a small program logic on the verifier's monad: `Costs x n post` says that
from every challenger state `x` makes at most `n` oracle calls, and its results satisfy `post`.
Loops are bounded by their length times the bound of their body, under an invariant of the loop
state.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {H : Primitives (OracleComp spec)}

/-- From every state, `x` makes at most `n` oracle calls and its results satisfy `post`. -/
def Costs {α : Type} (x : M H α) (n : Nat) (post : α → Prop) : Prop :=
  ∀ s, IsTotalQueryBound (x.run s).run n ∧
    ∀ v s', Except.ok (v, s') ∈ support (x.run s).run → post v

theorem run_bind {α β : Type} (x : M H α) (f : α → M H β) (s : H.State) :
    ((x >>= f).run s).run = (x.run s).run >>= fun r ↦ match r with
      | .ok (v, s') => ((f v).run s').run
      | .error e => pure (.error e) := by
  simp only [StateT.run_bind, ExceptT.run_bind]
  exact bind_congr fun r ↦ by rcases r with _ | ⟨v, s'⟩ <;> rfl

theorem costs_pure {α : Type} (a : α) (post : α → Prop) (h : post a) :
    Costs (H := H) (pure a) 0 post := fun s ↦
  ⟨trivial, fun v s' hv ↦ by
    simp only [StateT.run_pure, ExceptT.run_pure, mem_support_pure_iff, Except.ok.injEq,
      Prod.mk.injEq] at hv
    rw [hv.1]
    exact h⟩

theorem costs_bind {α β : Type} {x : M H α} {f : α → M H β} {a b : Nat} {P : α → Prop}
    {Q : β → Prop} (hx : Costs x a P) (hf : ∀ v, P v → Costs (f v) b Q) :
    Costs (x >>= f) (a + b) Q := fun s ↦ by
  rw [run_bind]
  refine ⟨isTotalQueryBound_bind_of_mem_support (hx s).1 fun r hr ↦ ?_, fun w s'' hw ↦ ?_⟩
  · rcases r with e | ⟨v, s'⟩
    · trivial
    · exact (hf v ((hx s).2 v s' hr) s').1
  · rw [mem_support_bind_iff] at hw
    obtain ⟨r, hr, hw⟩ := hw
    rcases r with e | ⟨v, s'⟩
    · simp only [mem_support_pure_iff, reduceCtorEq] at hw
    · exact (hf v ((hx s).2 v s' hr) s').2 w s'' hw

theorem costs_mono {α : Type} {x : M H α} {a b : Nat} {P Q : α → Prop} (hx : Costs x a P)
    (hab : a ≤ b) (hPQ : ∀ v, P v → Q v) : Costs x b Q := fun s ↦
  ⟨(hx s).1.mono hab, fun v s' hv ↦ hPQ v ((hx s).2 v s' hv)⟩

theorem costs_throw {α : Type} (e : String) (post : α → Prop) :
    Costs (H := H) (throw e) 0 post := fun s ↦ by
  have h : ((throw e : M H α).run s).run = pure (.error e) := by
    change ((throw e : ExceptT String (OracleComp spec) α) >>= fun a ↦ pure (a, s)).run = _
    simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind]
  rw [h]
  exact ⟨trivial, fun v s' hv ↦ by simp only [mem_support_pure_iff, reduceCtorEq] at hv⟩

theorem costs_modify (f : H.State → H.State) :
    Costs (H := H) (modify f) 0 fun _ ↦ True := fun _ ↦ ⟨trivial, fun _ _ _ ↦ trivial⟩

theorem costs_ensure (b : Bool) (msg : String) :
    Costs (H := H) (ensure b msg) 0 fun _ ↦ b = true := by
  unfold ensure
  split
  · exact costs_pure _ _ (by assumption)
  · exact costs_throw _ _

theorem costs_forIn {α β : Type} (l : List α) (init : β) (f : α → β → M H (ForInStep β))
    (c : Nat) (I : β → Prop) (hinit : I init)
    (hf : ∀ a ∈ l, ∀ b, I b → Costs (f a b) c fun r ↦ I r.value) :
    Costs (forIn l init f) (l.length * c) I := by
  induction l generalizing init with
  | nil => exact costs_pure _ _ hinit
  | cons a l ih =>
    rw [List.forIn_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine costs_bind (hf a List.mem_cons_self init hinit) fun r hr ↦ ?_
    rcases r with b | b
    · exact costs_mono (costs_pure _ _ hr) (Nat.zero_le _) fun _ h ↦ h
    · exact ih b hr fun a' ha' ↦ hf a' (List.mem_cons_of_mem a ha')

theorem costs_forIn_le {α β : Type} (l : List α) (init : β) (f : α → β → M H (ForInStep β))
    (N c : Nat) (hlen : l.length ≤ N) (I : β → Prop) (hinit : I init)
    (hf : ∀ a ∈ l, ∀ b, I b → Costs (f a b) c fun r ↦ I r.value) :
    Costs (forIn l init f) (N * c) I :=
  costs_mono (costs_forIn l init f c I hinit hf) (Nat.mul_le_mul_right _ hlen) fun _ h ↦ h

end CompStark.Fri

namespace CompStark.Merkle
open OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {F : Type} {d : Nat}

/-- Climbing a path with no shorter matrices compresses once per sibling. -/
theorem isTotalQueryBound_climbM (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hcompress : ∀ a b, IsTotalQueryBound (compress a b) 1) (values : List (List F)) :
    ∀ path index padded root,
      IsTotalQueryBound (climbM hash compress values path [] index padded root) path.length
  | [], _, _, _ => trivial
  | sib :: sibs, index, padded, root => by
    rw [climbM, List.length_cons, Nat.add_comm]
    split <;>
    · exact isTotalQueryBound_bind (hcompress _ _) fun r ↦
        isTotalQueryBound_climbM hash compress hcompress values sibs _ _ r

/-- An opening of matrices of one height `2 ^ k` hashes a leaf and climbs `k` layers, or hashes
nothing if its shape is wrong. -/
theorem isTotalQueryBound_verifyBatchM [DecidableEq F]
    (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hhash : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hcompress : ∀ a b, IsTotalQueryBound (compress a b) 1) (commit : Vector F d) (n k : Nat)
    (index : Nat) (values : List (List F)) (path : List (Vector F d)) :
    IsTotalQueryBound
      (verifyBatchM hash compress commit (List.replicate n (2 ^ k)) index values path) (1 + k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [List.replicate_zero, verifyBatchM, heightGroups, List.length_nil, List.range_zero,
      List.mergeSort_nil, List.foldr_nil]
    trivial
  unfold verifyBatchM
  rw [heightGroups_replicate n _ hn]
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have hlen : path.length = k := by rw [h.1.2]; exact log2Ceil_two_pow k
    refine isTotalQueryBound_bind (hhash _) fun leaf ↦ ?_
    have := isTotalQueryBound_climbM hash compress hcompress values path index
      (2 ^ k).nextPowerOfTwo leaf
    rw [hlen] at this
    simpa only [Nat.add_zero] using isTotalQueryBound_bind this fun x ↦
      (show IsTotalQueryBound (pure (x == commit) : OracleComp spec Bool) 0 from trivial)
  · trivial

end CompStark.Merkle

namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4

variable {K : Nat}

theorem isTotalQueryBound_query (q : Query) :
    IsTotalQueryBound (liftM ((spec K).query q) : OracleComp (spec K) _) 1 := by
  rw [← bind_pure (liftM _), isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

theorem costs_sample : Costs (sample (ideal K)) 1 fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound (Except.ok <$> (ideal K).sample s) 1
  refine (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  show IsTotalQueryBound ((withAnswers K fun q ↦ liftM ((spec K).query q)).sample s) 1
  unfold withAnswers
  dsimp only
  split
  · trivial
  · rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

theorem costs_observe (x : F) : Costs (observe (ideal K) x) 0 fun _ ↦ True := costs_modify _

theorem costs_observeList (xs : List F) : Costs (observeList (ideal K) xs) 0 fun _ ↦ True :=
  costs_modify _

theorem costs_observeExts (xs : List EF) : Costs (observeExts (ideal K) xs) 0 fun _ ↦ True :=
  costs_modify _

theorem costs_sampleExt : Costs (sampleExt (ideal K)) 4 fun _ ↦ True :=
  costs_bind costs_sample fun _ _ ↦ costs_bind costs_sample fun _ _ ↦
    costs_bind costs_sample fun _ _ ↦ costs_bind costs_sample fun _ _ ↦
      costs_pure _ (fun _ ↦ True) trivial

theorem costs_sampleBits (bits : Nat) : Costs (sampleBits (ideal K) bits) 1 fun _ ↦ True :=
  costs_bind costs_sample fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial

theorem costs_checkWitness (bits : Nat) (w : F) :
    Costs (checkWitness (ideal K) bits w) 1 fun _ ↦ True := by
  unfold checkWitness
  split
  · exact costs_mono (costs_pure _ (fun _ ↦ True) trivial) (Nat.zero_le _) fun _ h ↦ h
  · exact costs_bind (costs_observe w) fun _ _ ↦
      costs_bind (costs_sampleBits bits) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial

/-- An opening of matrices of one height `2 ^ k` costs at most `1 + k` calls. -/
theorem costs_checkOpening (commit : Digest) (n k index : Nat) (values : List (List F))
    (path : List Digest) :
    Costs (checkOpening (ideal K) commit (List.replicate n (2 ^ k)) index values path) (1 + k)
      fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound ((ExceptT.lift (Merkle.verifyBatchM (ideal K).hash
    (ideal K).compress commit (List.replicate n (2 ^ k)) index values path) >>=
      fun a ↦ pure (a, s) : ExceptT String (OracleComp (spec K)) _).run) (1 + k)
  simp only [ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ExceptT.run_pure]
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (Merkle.isTotalQueryBound_verifyBatchM _ _ (fun _ ↦ isTotalQueryBound_query _)
      (fun _ _ ↦ isTotalQueryBound_query _) commit n k index values path)
    fun x ↦ (show IsTotalQueryBound (pure (Except.ok (x, s)) : OracleComp (spec K) _) 0
      from trivial)

/-- A loop whose body makes no oracle calls makes none. -/
theorem costs_forIn_zero {α β : Type} (l : List α) (init : β)
    (f : α → β → M (ideal K) (ForInStep β)) (hf : ∀ a b, Costs (f a b) 0 fun _ ↦ True) :
    Costs (forIn l init f) 0 fun _ ↦ True := by
  simpa only [Nat.mul_zero] using
    costs_forIn l init f 0 (fun _ ↦ True) trivial fun a _ b _ ↦ hf a b

/-- The input openings of one query: one opening per round, of matrices on domains of size
`2 ^ db`. -/
theorem costs_openInput (P : Params) (logMax index : Nat) (alpha : EF)
    (inputs : List BatchOpening) (rounds : List Round) (db : Nat)
    (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) :
    Costs (openInput (ideal K) P logMax index alpha inputs rounds)
      (rounds.length * (1 + (db + P.logBlowup))) fun _ ↦ True := by
  unfold openInput
  refine costs_mono (costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind
    (costs_forIn _ _ _ (1 + (db + P.logBlowup)) (fun _ ↦ True) trivial fun a ha b _ ↦ ?_)
    fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_ fun _ _ ↦ trivial
  · obtain ⟨bo, commit, mats⟩ := a
    have hmats : ∀ mat ∈ mats, mat.1.logSize = db := hrounds _ (List.of_mem_zip ha).2
    have hheights : mats.map (fun x : Domain × List (EF × List EF) ↦ 2 ^ (x.1.logSize +
        P.logBlowup)) = List.replicate mats.length (2 ^ (db + P.logBlowup)) := by
      rw [List.eq_replicate_iff, List.length_map]
      refine ⟨rfl, fun h hh ↦ ?_⟩
      obtain ⟨mat, hmat, rfl⟩ := List.mem_map.mp hh
      rw [hmats mat hmat]
    dsimp only
    rw [hheights]
    refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_checkOpening _ _ _ _ _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (b := 0) (costs_forIn_zero _ _ _ fun x ro ↦ ?_) fun ro _ ↦ ?_) ?_
      fun _ _ ↦ trivial
    · obtain ⟨row, d, pts⟩ := x
      dsimp only
      refine costs_bind (costs_forIn_zero _ _ _ fun y acc ↦ ?_) fun _ _ ↦
        costs_pure _ (fun _ ↦ True) trivial
      exact costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_forIn_zero _ _ _
        fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
          costs_pure _ (fun _ ↦ True) trivial
    · split
      · exact costs_bind (costs_ensure _ _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial
      · exact costs_pure _ (fun _ ↦ True) trivial
    · omega
  · simp only [Nat.zero_add, Nat.add_zero, List.length_zip]
    exact Nat.mul_le_mul_right _ (Nat.min_le_right _ _)

theorem costs_checkOpening_single (commit : Digest) (k index : Nat) (values : List (List F))
    (path : List Digest) :
    Costs (checkOpening (ideal K) commit [2 ^ k] index values path) (1 + k) fun _ ↦ True :=
  costs_checkOpening commit 1 k index values path

/-- The folds of one query: one opening per fold, on domains no larger than the query's. -/
theorem costs_verifyQuery (P : Params) (logMax index : Nat) (betas : List EF)
    (commits : List Digest) (steps : List CommitStep) (ro : List (Nat × EF)) :
    Costs (verifyQuery (ideal K) P logMax index betas commits steps ro)
      (steps.length * (1 + logMax)) fun _ ↦ True := by
  unfold verifyQuery
  rcases ro with _ | ⟨⟨h0, e0⟩, tail⟩
  · exact costs_mono (costs_bind (b := 0) (costs_throw _ fun _ ↦ False) fun _ h ↦ h.elim)
      (Nat.zero_le _) fun _ h ↦ h
  dsimp only
  refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_pure _ (fun _ ↦ True) trivial)
    fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
    costs_bind (b := 0) (costs_forIn _ _ _ (1 + logMax) (fun st ↦ st.2.2.2 ≤ logMax)
      (Nat.le_refl _) fun x _ st hst ↦ ?_) fun st _ ↦ ?_) ?_ fun _ _ ↦ trivial
  · obtain ⟨⟨beta, commit⟩, step⟩ := x
    dsimp only
    refine costs_mono (P := fun r ↦ r.value.2.2.2 ≤ logMax) (costs_bind (costs_ensure _ _)
      fun _ _ ↦ costs_bind (costs_checkOpening_single _ _ _ _ _) fun _ _ ↦
      costs_bind (b := 0) (costs_ensure _ _) fun _ _ ↦ ?_) ?_ fun _ h ↦ h
    · split
      · split
        · exact costs_pure _ _ (by simp only [ForInStep.value]; omega)
        · exact costs_pure _ _ (by simp only [ForInStep.value]; omega)
      · exact costs_pure _ _ (by simp only [ForInStep.value]; omega)
    · omega
  · exact costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_pure _ (fun _ ↦ True) trivial
  · simp only [Nat.zero_add, Nat.add_zero, List.length_zip]
    exact Nat.mul_le_mul_right _ (Nat.min_le_right _ _)

/-- Every query has a fold per commit-phase commitment. -/
theorem steps_size_of_all (proof : FriProof)
    (hall : (proof.queries.all fun q ↦ q.steps.size == proof.commits.size &&
      q.steps.toList.map (·.logArity) == arities proof) = true) :
    ∀ q ∈ proof.queries.toList, q.steps.size = proof.commits.size := by
  intro q hq
  rw [Array.all_eq_true_iff_forall_mem] at hall
  have := hall q (Array.mem_toList_iff.mp hq)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

/-- With some fold, the commit-phase commitments are as many as the folds. -/
theorem commits_size_of_all (proof : FriProof)
    (hall : (proof.queries.all fun q ↦ q.steps.size == proof.commits.size &&
      q.steps.toList.map (·.logArity) == arities proof) = true) (hne : arities proof ≠ []) :
    proof.commits.size = (arities proof).length := by
  unfold arities at hne ⊢
  rcases h : proof.queries[0]? with _ | q
  · simp only [h, Option.map_none, Option.getD_none, ne_eq, not_true_eq_false] at hne
  · simp only [Option.map_some, Option.getD_some, List.length_map, Array.length_toList]
    have hq : q ∈ proof.queries.toList := by
      rw [Array.mem_toList_iff]
      exact Array.mem_of_getElem? h
    exact (steps_size_of_all proof hall q hq).symm

/-- FRI's oracle calls: four samples for `α`, five per fold, one for the query grinding, and per
query its index, its input openings and its folds. -/
theorem costs_verifyFri (P : Params) (proof : FriProof) (rounds : List Round) (db : Nat)
    (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) (hne : arities proof ≠ []) :
    Costs (verifyFri (ideal K) P proof rounds)
      (5 + 5 * (arities proof).length + P.numQueries * (1 + rounds.length * (1 + (db +
        P.logBlowup)) + (arities proof).length * (1 + ((arities proof).sum + P.logBlowup +
          P.logFinalPolyLen)))) fun _ ↦ True := by
  unfold verifyFri
  simp only [← Array.forIn_toList]
  refine costs_mono (P := fun _ ↦ True) (costs_bind costs_sampleExt fun alpha _ ↦
    costs_bind (costs_ensure _ _) fun _ hall ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
    costs_bind (costs_forIn_le _ _ _ (arities proof).length 5 ?_ (fun _ ↦ True) trivial
      fun _ _ _ _ ↦ ?_) fun betas _ ↦
    costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_observeExts _) fun _ _ ↦
    costs_bind (costs_ensure _ _) fun _ hq ↦ costs_bind (costs_forIn_zero _ _ _ fun _ _ ↦
      costs_bind (costs_observe _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
    costs_bind (costs_checkWitness _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
    costs_bind (b := 0) (costs_forIn_le _ _ _ P.numQueries
      (1 + rounds.length * (1 + (db + P.logBlowup)) + (arities proof).length *
        (1 + ((arities proof).sum + P.logBlowup + P.logFinalPolyLen)))
      ?_ (fun _ ↦ True) trivial fun q hqm _ _ ↦ ?_)
      fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_ fun _ _ ↦ trivial
  · rw [List.length_zip, Array.length_toList,
      commits_size_of_all proof (by simpa only using hall) hne]
    exact Nat.min_le_left _ _
  · exact costs_bind (costs_observeList _) fun _ _ ↦ costs_bind (costs_checkWitness _ _)
      fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind costs_sampleExt fun _ _ ↦
        costs_pure _ (fun _ ↦ True) trivial
  · rw [Array.length_toList]
    exact (beq_iff_eq.mp hq).le
  · have hsteps := steps_size_of_all proof (by simpa only using hall) q hqm
    refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_sampleBits _) fun _ _ ↦ costs_bind
      (costs_openInput P _ _ alpha _ rounds db hrounds) fun _ _ ↦ costs_bind
      (costs_verifyQuery P _ _ _ _ _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_pure _ (fun _ ↦ True) trivial) ?_ fun _ h ↦ h
    have hlen : q.steps.toList.length = (arities proof).length := by
      rw [Array.length_toList, hsteps, commits_size_of_all proof (by simpa only using hall) hne]
    rw [hlen]
    omega
  · omega

theorem costs_verifyPcs (P : Params) (rounds : List Round) (proof : FriProof) (db : Nat)
    (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) (hne : arities proof ≠ []) :
    Costs (verifyPcs (ideal K) P rounds proof)
      (5 + 5 * (arities proof).length + P.numQueries * (1 + rounds.length * (1 + (db +
        P.logBlowup)) + (arities proof).length * (1 + ((arities proof).sum + P.logBlowup +
          P.logFinalPolyLen)))) fun _ ↦ True := by
  unfold verifyPcs
  refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_forIn_zero _ _ _ fun _ _ ↦
    costs_bind (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind (costs_forIn_zero _ _ _ fun _ _ ↦
      costs_bind (costs_observeExts _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦
        costs_pure _ (fun _ ↦ True) trivial) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial)
    fun _ _ ↦ costs_verifyFri P proof rounds db hrounds hne) (by omega) fun _ h ↦ h

/-- Plonky3's fold arities sum to the halvings they fold away. -/
theorem sum_foldArities (a : Nat) : ∀ r, (foldArities a r).sum = r
  | 0 => by rw [foldArities]; rfl
  | r + 1 => by
    rw [foldArities, List.sum_cons, sum_foldArities a (r + 1 - max 1 (min a (r + 1)))]
    omega

theorem foldArities_ne_nil (a r : Nat) (hr : 0 < r) : foldArities a r ≠ [] := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [foldArities]
  exact List.cons_ne_nil _ _

end CompStark.Fri

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field

variable (S : Setup)

/-- **The verifier's oracle calls.** On a proof for `2 ^ logN` rows, the verifier makes at most
`verifierQueries` oracle calls. -/
theorem isTotalQueryBound_verifyWith (proof : Proof) (publicValues : List F)
    (hdb : proof.degreeBits = S.logN) :
    IsTotalQueryBound (verifyWith (ideal S.streamLen) S.params S.air proof publicValues)
      S.verifierQueries := by
  have hne : S.friArities ≠ [] := foldArities_ne_nil _ _ (by have := S.folds; omega)
  have hsum : S.friArities.sum = S.logN - S.params.logFinalPolyLen := sum_foldArities _ _
  unfold verifyWith
  dsimp only
  split
  · split
    · rename_i harities
      rw [beq_iff_eq, hdb] at harities
      rw [ExceptT.run_bind]
      apply IsTotalQueryBound.mono (n₁ := S.verifierQueries + 0) _ (Nat.add_zero _).le
      apply isTotalQueryBound_bind
      · refine ((?_ : Costs _ S.verifierQueries fun _ ↦ True) _).1
        refine costs_mono (P := fun _ ↦ True)
          (costs_bind (costs_observe _) fun _ _ ↦ costs_bind (costs_observe _) fun _ _ ↦
          costs_bind (costs_observe _) fun _ _ ↦ costs_bind (costs_observeList _) fun _ _ ↦
          costs_bind (costs_observeList _) fun _ _ ↦ costs_bind costs_sampleExt fun _ _ ↦
          costs_bind (costs_observeList _) fun _ _ ↦ costs_bind costs_sampleExt fun _ _ ↦
          costs_bind (a := 5 + 5 * (arities proof.fri).length + S.params.numQueries *
            (1 + 2 * (1 + (proof.degreeBits + S.params.logBlowup)) + (arities proof.fri).length *
              (1 + ((arities proof.fri).sum + S.params.logBlowup + S.params.logFinalPolyLen))))
            (b := 0) (costs_verifyPcs _ _ _ proof.degreeBits ?_
            (by rw [harities]; exact hne)) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_
          fun _ h ↦ h
        · intro r hr mat hmat
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmat
            rw [hmat]
          · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hmat
            rfl
        · have hlfp := S.folds
          have h : S.logN - S.params.logFinalPolyLen + S.params.logBlowup +
              S.params.logFinalPolyLen = S.logN + S.params.logBlowup := by omega
          rw [harities, hdb]
          change _ ≤ 13 + 5 * S.friArities.length + S.params.numQueries *
            (1 + (S.friArities.length + 2) * (1 + (S.logN + S.params.logBlowup)))
          rw [hsum, h]
          apply le_of_eq
          ring
      · intro r
        rcases r with _ | ⟨⟨alpha, zeta⟩, s⟩
        · trivial
        · dsimp only
          split
          · trivial
          · simp only [ExceptT.run_throw]
            trivial
    · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind]
      trivial
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind]
    trivial

/-- **The game's verifier's oracle calls.** On every proof, the verifier in the random-oracle
model makes at most `verifierQueries` oracle calls. -/
theorem isTotalQueryBound_verifyRo (proof : Proof) (publicValues : List F) :
    IsTotalQueryBound (S.verifyRo proof publicValues) S.verifierQueries := by
  unfold verifyRo
  split
  · exact S.isTotalQueryBound_verifyWith proof publicValues (by assumption)
  · trivial

end CompStark.Iop.Setup
