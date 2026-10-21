/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.Merkle.Multi
public import CompStark.Fri.Shapes
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.Monad.Support
public import Mathlib.Tactic.Ring

/-! # The verifier's oracle calls

The verifier makes at most `Setup.verifierQueries` oracle calls on a proof for `2 ^ logN` rows
(`isTotalQueryBound_verifyWith`), and so does the game's verifier on every proof
(`isTotalQueryBound_verifyRo`). A Merkle multi-opening of `n` queries into matrices of height
`2 ^ k` hashes at most `n` leaves and compresses at most `n` nodes per layer.

The count runs through a small program logic on the verifier's monad: `Costs x n post` says that
from every challenger state `x` makes at most `n` oracle calls, and its results satisfy `post`.
Loops are bounded by their length times the bound of their body, under an invariant of the loop
state.
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {F : Type} {H : Primitives F (OracleComp spec)}

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

/-- A check before `f` costs what `f` costs when the check passes. -/
theorem costs_ensure_bind {β : Type} {b : Bool} {msg : String} {f : Unit → M H β} {n : Nat}
    {Q : β → Prop} (hf : b = true → Costs (f ()) n Q) : Costs (ensure b msg >>= f) n Q := by
  unfold ensure
  split
  · rw [pure_bind]; exact hf (by assumption)
  · exact costs_mono (costs_bind (a := 0) (b := 0) (costs_throw msg fun _ ↦ False)
      fun _ (h : False) ↦ h.elim) (Nat.zero_le _) fun _ (h : False) ↦ h.elim

/-- A free step before `f` costs what `f` costs. -/
theorem costs_free_bind {α β : Type} {x : M H α} {f : α → M H β} {n : Nat} {P : α → Prop}
    {Q : β → Prop} (hx : Costs x 0 P) (hf : ∀ v, P v → Costs (f v) n Q) :
    Costs (x >>= f) n Q :=
  costs_mono (costs_bind hx hf) (Nat.zero_add n).le fun _ h ↦ h

theorem costs_bind_le {α β : Type} {x : M H α} {f : α → M H β} {a b n : Nat} {P : α → Prop}
    {Q : β → Prop} (hx : Costs x a P) (hf : ∀ v, P v → Costs (f v) b Q) (h : a + b ≤ n) :
    Costs (x >>= f) n Q :=
  costs_mono (costs_bind hx hf) h fun _ h ↦ h

theorem costs_bind_zero {α β : Type} {x : M H α} {f : α → M H β}
    (hx : Costs x 0 fun _ ↦ True) (hf : ∀ v, Costs (f v) 0 fun _ ↦ True) :
    Costs (x >>= f) 0 fun _ ↦ True :=
  costs_bind hx fun v _ ↦ hf v

/-- A loop whose body makes no oracle calls makes none. -/
theorem costs_forIn_zero {α β : Type} (l : List α) (init : β) (f : α → β → M H (ForInStep β))
    (hf : ∀ a b, Costs (f a b) 0 fun _ ↦ True) : Costs (forIn l init f) 0 fun _ ↦ True := by
  simpa only [Nat.mul_zero] using
    costs_forIn l init f 0 (fun _ ↦ True) trivial fun a _ b _ ↦ hf a b

/-- `mapM` costs its body's bound per element and keeps the length. -/
theorem costs_mapM {α β : Type} (f : α → M H β) (c : Nat) (hf : ∀ a, Costs (f a) c fun _ ↦ True) :
    ∀ l : List α, Costs (l.mapM f) (l.length * c) fun r ↦ r.length = l.length
  | [] => costs_pure _ _ rfl
  | a :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact costs_bind (hf a) fun b _ ↦ costs_mono (costs_bind (costs_mapM f c hf l) fun bs hbs ↦
      costs_pure _ (fun r : List β ↦ r.length = l.length + 1) (by rw [List.length_cons, hbs]))
      (Nat.add_zero _).le fun _ h ↦ h

/-- Closes a goal `Costs x 0 fun _ ↦ True` for a computation `x` of pure steps, checks, throws and
loops. -/
macro "costs_zero" : tactic => `(tactic| repeat' (first
  | exact costs_pure _ (fun _ ↦ True) trivial
  | exact costs_throw _ _
  | exact costs_mono (costs_ensure _ _) le_rfl fun _ _ ↦ trivial
  | refine costs_bind_zero ?_ fun _ ↦ ?_
  | refine costs_forIn_zero _ _ _ fun _ _ ↦ ?_
  | split
  | dsimp only))

theorem costs_forIn_le {α β : Type} (l : List α) (init : β) (f : α → β → M H (ForInStep β))
    (N c : Nat) (hlen : l.length ≤ N) (I : β → Prop) (hinit : I init)
    (hf : ∀ a ∈ l, ∀ b, I b → Costs (f a b) c fun r ↦ I r.value) :
    Costs (forIn l init f) (N * c) I :=
  costs_mono (costs_forIn l init f c I hinit hf) (Nat.mul_le_mul_right _ hlen) fun _ h ↦ h

end CompStark.Fri

namespace CompStark.Merkle
open OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {F : Type} {d : Nat}

theorem isTotalQueryBound_pure {α : Type} (a : α) :
    IsTotalQueryBound (pure a : OracleComp spec α) 0 := trivial

/-- A parent compressed in front of the rest of a level. -/
theorem levelM_cons_bound {z0 : OracleComp spec (Vector F d)} (h0 : IsTotalQueryBound z0 1)
    {rec : OracleComp spec (List (Nat × Nat × Vector F d) × List (Vector F d))} {n : Nat}
    (hrec : IsTotalQueryBound rec n ∧ ∀ r ∈ support rec, r.1.length ≤ n) (i q : Nat) :
    IsTotalQueryBound (do let z ← z0; let r ← rec; pure ((i, q, z) :: r.1, r.2)) (n + 1) ∧
      ∀ r ∈ support (do let z ← z0; let r ← rec; pure ((i, q, z) :: r.1, r.2)),
        r.1.length ≤ n + 1 := by
  refine ⟨(isTotalQueryBound_bind h0 fun _ ↦ isTotalQueryBound_bind hrec.1 fun _ ↦
    isTotalQueryBound_pure _).mono (by omega), fun r hr ↦ ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨z, -, r', hr', rfl⟩ := hr
  rw [List.length_cons]
  exact Nat.succ_le_succ (hrec.2 _ hr')

variable [Zero F]

/-- One level of a walk compresses once per parent, and has at most as many parents as nodes. -/
theorem levelM_bound (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hc : ∀ a b, IsTotalQueryBound (compress a b) 1) :
    ∀ (nodes : List (Nat × Nat × Vector F d)) (sibs : List (Vector F d)),
      IsTotalQueryBound (levelM compress nodes sibs) nodes.length ∧
        ∀ r ∈ support (levelM compress nodes sibs), r.1.length ≤ nodes.length
  | [], sibs => ⟨trivial, fun r hr ↦ by
      rw [levelM, mem_support_pure_iff] at hr
      rw [hr]⟩
  | [(i, q, x)], sibs => by
    rw [levelM]
    split <;>
    · refine ⟨(isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hc _ _) fun _ ↦
        isTotalQueryBound_pure _).mono le_rfl, fun r hr ↦ ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨z, -, rfl⟩ := hr
      exact le_rfl
  | (i, q, x) :: (j, q', y) :: rest, sibs => by
    rw [levelM]
    split
    · exact (levelM_cons_bound (hc x y) (levelM_bound compress hc rest sibs) _ _).imp
        (fun h ↦ h.mono (by simp only [List.length_cons]; omega))
        fun h r hr ↦ (h r hr).trans (by simp only [List.length_cons]; omega)
    · have ih := levelM_bound compress hc ((j, q', y) :: rest) sibs.tail
      split
      · exact levelM_cons_bound (hc _ _) ih _ _
      · exact levelM_cons_bound (hc _ _) ih _ _

/-- A walk with no shorter matrices compresses at most once per node and level. -/
theorem walkM_bound (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hc : ∀ a b, IsTotalQueryBound (compress a b) 1) (rows : List (List (List F))) :
    ∀ levels padded (nodes : List (Nat × Nat × Vector F d)) sibs,
      IsTotalQueryBound (walkM hash compress rows levels [] padded nodes sibs)
        (levels * nodes.length)
  | 0, _, _, _ => trivial
  | levels + 1, padded, nodes, sibs => by
    rw [walkM]
    refine (isTotalQueryBound_bind_of_mem_support (levelM_bound compress hc nodes sibs).1
      (suffixBound := levels * nodes.length) fun r hr ↦ ?_).mono (by rw [Nat.succ_mul]; omega)
    obtain ⟨ps, sibs'⟩ := r
    exact (walkM_bound hash compress hc rows levels _ ps sibs').mono
      (Nat.mul_le_mul_left _ ((levelM_bound compress hc nodes sibs).2 _ hr))

/-- `mapM` costs its body's bound per element and keeps the length. -/
theorem mapM_bound {α β : Type} (f : α → OracleComp spec β) (c : Nat)
    (hf : ∀ a, IsTotalQueryBound (f a) c) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * c) ∧
      ∀ r ∈ support (l.mapM f), r.length = l.length
  | [] => ⟨trivial, fun r hr ↦ by
      rw [List.mapM_nil, mem_support_pure_iff] at hr
      rw [hr]; rfl⟩
  | a :: l => by
    have ih := mapM_bound f c hf l
    rw [List.mapM_cons]
    have hb : ∀ b : β, IsTotalQueryBound (do let bs ← l.mapM f; pure (b :: bs))
        (l.length * c + 0) := fun b ↦
      isTotalQueryBound_bind ih.1 fun _ ↦ isTotalQueryBound_pure _
    refine ⟨(isTotalQueryBound_bind (hf a) hb).mono
      (by rw [List.length_cons, Nat.succ_mul]; omega), fun r hr ↦ ?_⟩
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨b, -, bs, hbs, rfl⟩ := hr
    rw [List.length_cons, List.length_cons, ih.2 _ hbs]

theorem length_frontier_le (indices : List Nat) : (frontier indices).length ≤ indices.length := by
  rw [frontier, List.length_map, List.length_mergeSort]
  exact (List.dedup_sublist indices).length_le

/-- A multi-opening of `n` queries into matrices of one height `2 ^ k` hashes at most `n` leaves
and compresses at most `n` nodes per layer, or hashes nothing if its shape is wrong. -/
theorem isTotalQueryBound_verifyMultiM [DecidableEq F]
    (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hhash : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hcompress : ∀ a b, IsTotalQueryBound (compress a b) 1) (commit : Vector F d)
    (dims : List (Nat × Nat)) (n k : Nat) (hdims : dims.map (·.1) = List.replicate n (2 ^ k))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d)) :
    IsTotalQueryBound (verifyMultiM hash compress commit dims indices rows sibs)
      (indices.length * (1 + k)) := by
  unfold verifyMultiM
  rw [hdims]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [List.replicate_zero, heightGroups, List.length_nil, List.range_zero,
      List.mergeSort_nil, List.foldr_nil]
    trivial
  rw [heightGroups_replicate n _ hn]
  dsimp only
  rw [nextPowerOfTwo_two_pow, Nat.log2_two_pow]
  split
  · have hleaves := mapM_bound (spec := spec) (fun (iq : Nat × Nat) ↦ do
      return (iq.1, iq.2, ← hash ((List.range n).flatMap fun k ↦ (rows.getD iq.2 []).getD k [])))
      1 (fun _ ↦ isTotalQueryBound_bind (hhash _) fun _ ↦ isTotalQueryBound_pure _)
      (frontier indices)
    have hf := length_frontier_le indices
    refine (isTotalQueryBound_bind_of_mem_support hleaves.1 (suffixBound := k * indices.length)
      fun leaves hl ↦ ?_).mono (by rw [Nat.mul_one]; nlinarith)
    refine (isTotalQueryBound_bind (walkM_bound hash compress hcompress rows k _ leaves sibs)
      fun _ ↦ Merkle.isTotalQueryBound_pure _).mono ?_
    rw [hleaves.2 _ hl, Nat.add_zero]
    exact Nat.mul_le_mul_left _ hf
  · trivial

end CompStark.Merkle

namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} {EF : Type} {K : Nat}

theorem isTotalQueryBound_query (q : Query F) :
    IsTotalQueryBound (liftM ((spec F K).query q) : OracleComp (spec F K) _) 1 := by
  rw [← bind_pure (liftM _), isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

variable [BaseField F] [Challenge F EF]

theorem costs_sample : Costs (sample (ideal F K)) 1 fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound (Except.ok <$> (ideal F K).sample s) 1
  refine (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  show IsTotalQueryBound ((withAnswers K fun q ↦ liftM ((spec F K).query q)).sample s) 1
  unfold withAnswers
  dsimp only
  split
  · trivial
  · rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

theorem costs_observe (x : F) : Costs (observe (ideal F K) x) 0 fun _ ↦ True := costs_modify _

theorem costs_observeList (xs : List F) : Costs (observeList (ideal F K) xs) 0 fun _ ↦ True :=
  costs_modify _

theorem costs_observeExts (xs : List EF) : Costs (observeExts (ideal F K) xs) 0 fun _ ↦ True :=
  costs_modify _

theorem costs_sampleList : ∀ n, Costs (sampleList (ideal F K) n) n fun _ ↦ True
  | 0 => costs_pure _ (fun _ ↦ True) trivial
  | n + 1 => costs_mono (costs_bind costs_sample fun _ _ ↦ costs_bind (costs_sampleList n)
      fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) (by omega) fun _ h ↦ h

theorem costs_sampleExt : Costs (sampleExt (ideal F K) : M _ EF) (Challenge.d EF) fun _ ↦ True :=
  costs_bind (costs_sampleList _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial

theorem costs_sampleBits (bits : Nat) : Costs (sampleBits (ideal F K) bits) 1 fun _ ↦ True :=
  costs_bind costs_sample fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial

theorem costs_checkWitness (bits : Nat) (w : F) :
    Costs (checkWitness (ideal F K) bits w) 1 fun _ ↦ True := by
  unfold checkWitness
  split
  · exact costs_mono (costs_pure _ (fun _ ↦ True) trivial) (Nat.zero_le _) fun _ h ↦ h
  · exact costs_bind (costs_observe w) fun _ _ ↦
      costs_bind (costs_sampleBits bits) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial

/-- A multi-opening of `n` queries into matrices of one height `2 ^ k` costs at most
`n (1 + k)` calls. -/
theorem costs_checkMulti (commit : Digest F) (dims : List (Nat × Nat)) (n k : Nat)
    (hdims : dims.map (·.1) = List.replicate n (2 ^ k)) (indices : List Nat)
    (rows : List (List (List F))) (sibs : List (Digest F)) :
    Costs (checkMulti (ideal F K) commit dims indices rows sibs) (indices.length * (1 + k))
      fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound ((ExceptT.lift (Merkle.verifyMultiM (ideal F K).hash
    (ideal F K).compress commit dims indices rows sibs) >>=
      fun a ↦ pure (a, s) : ExceptT String (OracleComp (spec F K)) _).run)
    (indices.length * (1 + k))
  simp only [ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ExceptT.run_pure]
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (Merkle.isTotalQueryBound_verifyMultiM _ _ (fun _ ↦ isTotalQueryBound_query _)
      (fun _ _ ↦ isTotalQueryBound_query _) commit dims n k hdims indices rows sibs)
    fun x ↦ (show IsTotalQueryBound (pure (Except.ok (x, s)) : OracleComp (spec F K) _) 0
      from trivial)

/-- The input multi-openings: one per round, of matrices on domains of size `2 ^ db`. -/
theorem costs_verifyInputs (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) (db : Nat)
    (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) :
    Costs (verifyInputs (ideal F K) P logMax indices inputs rounds)
      (rounds.length * (indices.length * (1 + (db + P.logBlowup)))) fun _ ↦ True := by
  unfold verifyInputs
  refine costs_mono (costs_bind (a := 0)
    (b := rounds.length * (indices.length * (1 + (db + P.logBlowup)))) (costs_ensure _ _)
    fun _ _ ↦ costs_bind (b := 0) (costs_forIn_le _ _ _
    rounds.length (indices.length * (1 + (db + P.logBlowup))) ?_ (fun _ ↦ True) trivial
    fun a ha b _ ↦ ?_) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) (by omega) fun _ _ ↦ trivial
  · rw [List.length_zip]; exact Nat.min_le_right _ _
  · obtain ⟨bo, commit, mats⟩ := a
    have hmats : ∀ mat ∈ mats, mat.1.logSize = db := hrounds _ (List.of_mem_zip ha).2
    have hheights : (mats.map fun x : Domain F × List (EF × List EF) ↦
        (2 ^ (x.1.logSize + P.logBlowup), (x.2.headD default).2.length)).map (·.1) =
        List.replicate mats.length (2 ^ (db + P.logBlowup)) := by
      rw [List.eq_replicate_iff, List.length_map, List.length_map]
      refine ⟨rfl, fun h hh ↦ ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hh
      obtain ⟨mat, hmat, rfl⟩ := List.mem_map.mp hy
      rw [hmats mat hmat]
    dsimp only
    refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_checkMulti _ _ _ _ hheights _ _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_
      fun _ _ ↦ trivial
    rw [List.length_map]
    omega

theorem costs_reduceQuery (P : Params) (logMax index : Nat) (alpha : EF)
    (rows : List (List (Array F))) (rounds : List (Round F EF)) :
    Costs (reduceQuery (ideal F K) P logMax index alpha rows rounds) 0 fun _ ↦ True := by
  unfold reduceQuery
  costs_zero

theorem costs_foldQuery (P : Params) (logMax index q : Nat) (betas : List EF) (arities : List Nat)
    (folds : List (CommitOpening F EF)) (ro : List (Nat × EF)) :
    Costs (foldQuery (ideal F K) P logMax index q betas arities folds ro) 0 fun _ ↦ True := by
  unfold foldQuery
  costs_zero

/-- FRI's oracle calls after `α`: `d + 1` per fold, one for the query grinding, and per query its
index, its input openings and its folds' openings. -/
theorem costs_verifyFri (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (db : Nat) (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) :
    Costs (verifyFri (ideal F K) P proof rounds alpha)
      (1 + (Challenge.d EF + 1) * (foldArities P.maxLogArity (db - P.logFinalPolyLen)).length +
        P.numQueries * (1 + (rounds.length +
          (foldArities P.maxLogArity (db - P.logFinalPolyLen)).length) *
            (1 + (db + P.logBlowup)))) fun _ ↦ True := by
  unfold verifyFri
  dsimp only
  refine costs_ensure_bind fun hpar ↦ costs_ensure_bind fun hany ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpar
  have hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [db + P.logBlowup] := by
    refine dedup_mergeSort_const _ _ _ (fun x hx ↦ ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r, hr, hy⟩ := List.mem_flatMap.mp hy
      rw [hrounds r hr y hy]
    · simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.isEmpty_eq_false_iff] at hany
      obtain ⟨r, hr, hne⟩ := hany
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
      exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hy⟩))
  have harities : foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
      (db + P.logBlowup) [db + P.logBlowup] =
      foldArities P.maxLogArity (db - P.logFinalPolyLen) := by
    rw [foldSchedule_single _ _ hpar.2 _ _ (Nat.sub_le _ _)]
    congr 1
    omega
  simp only [hheights, List.headD_cons, harities]
  set A := foldArities P.maxLogArity (db - P.logFinalPolyLen)
  set N := P.numQueries
  set c := 1 + (db + P.logBlowup)
  refine costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_ensure_bind fun hcs ↦ ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hcs
  -- the commit loop
  refine costs_bind_le (b := 1 + N * (1 + (rounds.length + A.length) * c))
    (costs_forIn_le _ _ _ A.length (Challenge.d EF + 1) ?_ (fun _ ↦ True) trivial
      fun _ _ _ _ ↦ ?_) (fun betas _ ↦ ?_) (le_of_eq (by ring))
  · rw [List.length_zip, Array.length_toList, hcs.1]; exact Nat.min_le_left _ _
  · exact costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le (costs_checkWitness _ _)
      (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind costs_sampleExt fun _ _ ↦
        costs_pure _ (fun _ ↦ True) trivial) (by omega)
  -- the final polynomial, the query grinding and the indices
  refine costs_free_bind (costs_observeExts _) fun _ _ ↦ costs_bind_le (costs_checkWitness _ _)
    (b := N * (1 + (rounds.length + A.length) * c)) (fun _ _ ↦ costs_ensure_bind fun _ ↦ ?_)
    le_rfl
  refine costs_bind_le (costs_mapM _ 1 (fun _ ↦ costs_sampleBits _) _)
    (b := rounds.length * (N * c) + A.length * (N * c)) (fun indices hind ↦ ?_)
    (by rw [List.length_range]; exact le_of_eq (by ring))
  rw [List.length_range] at hind
  -- the input openings
  refine costs_bind_le (costs_verifyInputs P _ indices _ rounds db hrounds)
    (b := A.length * (N * c)) (fun _ _ ↦ ?_) (by rw [hind])
  -- the queries' folds and the commit-phase openings
  refine costs_free_bind (costs_mapM _ 0 (fun iq ↦ ?_) _) fun groups hg ↦ ?_
  · refine costs_bind_zero (costs_reduceQuery _ _ _ _ _ _) fun _ ↦
      costs_bind_zero (costs_foldQuery _ _ _ _ _ _ _ _) fun _ ↦ ?_
    costs_zero
  rw [List.length_zipIdx, hind] at hg
  refine costs_bind_le (b := 0) (costs_forIn_le _ _ _ A.length (N * c) ?_
    (fun logH ↦ logH ≤ db + P.logBlowup) le_rfl fun x _ logH hlog ↦ ?_)
    (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl
  · rw [List.length_zip, List.length_zipIdx]; exact Nat.min_le_right _ _
  obtain ⟨⟨cm, o⟩, la, i⟩ := x
  dsimp only
  refine costs_bind_le (costs_checkMulti _ _ 1 (logH - la) rfl _ _ _) (b := 0)
    (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_pure _ _ (by simp only [ForInStep.value]; omega))
    ?_
  rw [List.length_map, List.length_map, hg, Nat.add_zero]
  exact Nat.mul_le_mul_left _ (by omega)

theorem costs_verifyPcs (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) (db : Nat)
    (hrounds : ∀ r ∈ rounds, ∀ mat ∈ r.2, mat.1.logSize = db) :
    Costs (verifyPcs (ideal F K) P rounds proof)
      (Challenge.d EF + 2 + (Challenge.d EF + 1) *
        (foldArities P.maxLogArity (db - P.logFinalPolyLen)).length +
        P.numQueries * (1 + (rounds.length +
          (foldArities P.maxLogArity (db - P.logFinalPolyLen)).length) *
            (1 + (db + P.logBlowup)))) fun _ ↦ True := by
  unfold verifyPcs
  refine costs_ensure_bind fun _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _
      fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero
        (costs_observeExts _) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ ↦
          costs_pure _ (fun _ ↦ True) trivial) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial)
      fun _ _ ↦ costs_bind_le (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦
        costs_bind costs_sampleExt fun alpha _ ↦ costs_verifyFri P proof rounds alpha db hrounds)
      (by omega)

end CompStark.Fri

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

/-- A verifying key that passes the shape check belongs to preprocessed columns. -/
theorem preprocessedWidth_pos {F EF : Type} {A : Air F} {k : PreprocessedKey F}
    {o : OpenedValues EF} {db : Nat} (h : preprocessedShapeOk A (some k) o db = true) :
    0 < A.preprocessedWidth := by
  rcases o with ⟨tl, tn, _ | l, n, qc⟩
  · simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  · simp only [preprocessedShapeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (S : Setup EF)

/-- The verifier opens at most `inputRounds` committed rounds at a query. -/
theorem length_openingRounds_le (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (zeta : EF)
    (hshape : preprocessedShapeOk S.air vk proof.opened proof.degreeBits = true) :
    (openingRounds S.air vk proof zeta).length ≤ S.inputRounds := by
  unfold openingRounds preprocessedRound inputRounds
  cases vk with
  | none =>
    simp only [List.length_append, List.length_cons, List.length_nil]
    split <;> omega
  | some k =>
    have h0 := preprocessedWidth_pos hshape
    simp only [Nat.pos_iff_ne_zero.mp h0, ↓reduceIte, List.length_append, List.length_cons,
      List.length_nil]
    omega

/-- **The verifier's oracle calls.** On a proof for `2 ^ logN` rows, the verifier makes at most
`verifierCalls` oracle calls. -/
theorem isTotalQueryBound_verifyWith (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (publicValues : List F) (hdb : proof.degreeBits = S.logN) :
    IsTotalQueryBound (verifyWith (ideal F S.streamLen) S.params S.air vk proof publicValues)
      S.verifierCalls := by
  have hrun (hshape : preprocessedShapeOk S.air vk proof.opened proof.degreeBits = true) :
      Costs (H := ideal F S.streamLen) (do
      observeList (ideal F S.streamLen) (starkSeedOf EF S.params S.air proof.degreeBits)
      observeList (ideal F S.streamLen) proof.traceCommit.toList
      observeList (ideal F S.streamLen) (preprocessedDigest vk)
      observeList (ideal F S.streamLen) publicValues
      let alpha ← (sampleExt (ideal F S.streamLen) : M _ EF)
      observeList (ideal F S.streamLen) proof.quotientCommit.toList
      ensure (← checkWitness (ideal F S.streamLen) S.params.oodPowBits proof.oodWitness)
        "out-of-domain witness"
      let zeta ← (sampleExt (ideal F S.streamLen) : M _ EF)
      ensure (Ext.powTwo zeta proof.degreeBits - 1 != 0) "out-of-domain point in the trace domain"
      verifyPcs (ideal F S.streamLen) S.params (openingRounds S.air vk proof zeta) proof.fri
      return (alpha, zeta)) S.verifierCalls fun _ ↦ True := by
    set A := foldArities S.params.maxLogArity (proof.degreeBits - S.params.logFinalPolyLen)
    set V := Challenge.d EF + 2 + (Challenge.d EF + 1) * A.length + S.params.numQueries *
      (1 + (S.inputRounds + A.length) * (1 + (proof.degreeBits + S.params.logBlowup)))
    refine costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeList _)
      fun _ _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
      costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le
      (b := 1 + Challenge.d EF + V) costs_sampleExt (fun alpha _ ↦ costs_free_bind
        (costs_observeList _) fun _ _ ↦ costs_bind_le (b := Challenge.d EF + V)
        (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := V)
          costs_sampleExt (fun zeta _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (a := V) (b := 0)
            (costs_mono (costs_verifyPcs _ _ _ proof.degreeBits fun r hr mat hmat ↦ ?_)
              (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
                (Nat.mul_le_mul_right _ (Nat.add_le_add_right
                  (length_openingRounds_le S vk proof zeta hshape) _)) 1)) _) fun _ h ↦ h)
            (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl) le_rfl) (by omega)) ?_
    · simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmat
        rw [hmat]
      · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hmat
        rfl
      · unfold preprocessedRound at hr
        split at hr
        · rw [List.mem_singleton] at hr
          subst hr
          rw [List.mem_singleton] at hmat
          rw [hmat]
        · exact absurd hr List.not_mem_nil
    · simp only [V, A, hdb, verifierCalls, openingQueries, friArities]
      exact le_of_eq (by ring)
  unfold verifyWith
  dsimp only
  by_cases h1 : proof.degreeBits + S.air.logQuotientChunks proof.degreeBits ≤ twoAdicity F
  · rw [ite_eq_left h1]
    by_cases h2 : S.air.periodicFits proof.degreeBits = true
    · rw [ite_eq_left h2]
      split
      · split
        · rename_i hshape
          split
          · rw [ExceptT.run_bind]
            apply IsTotalQueryBound.mono (n₁ := S.verifierCalls + 0) _ (Nat.add_zero _).le
            refine isTotalQueryBound_bind (hrun (by
              simp only [Bool.and_eq_true] at hshape
              exact hshape.2) _).1 fun r ↦ ?_
            rcases r with _ | ⟨⟨alpha, zeta⟩, s⟩
            · trivial
            · dsimp only
              split
              · trivial
              · trivial
          all_goals trivial
        all_goals trivial
      all_goals trivial
    · rw [ite_eq_right h2]
      trivial
  · rw [ite_eq_right h1]
    trivial

/-- **The game's verifier's oracle calls.** On every proof, the verifier in the random-oracle
model makes at most `verifierCalls` oracle calls. -/
theorem isTotalQueryBound_verifyRo (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (publicValues : List F) :
    IsTotalQueryBound (S.verifyRo vk proof publicValues) S.verifierCalls := by
  unfold verifyRo
  split
  · exact S.isTotalQueryBound_verifyWith vk proof publicValues (by assumption)
  · trivial

/-- **The setup's oracle calls.** -/
theorem isTotalQueryBound_setupRo : IsTotalQueryBound S.setupRo S.setupQueries := by
  have hnode : ∀ (leaf : Nat → OracleComp (spec F S.streamLen) (Digest F)),
      (∀ r, IsTotalQueryBound (leaf r) 1) → ∀ j t,
      IsTotalQueryBound (merkleNodeWith (ideal F S.streamLen) leaf j t) (2 ^ (j + 1) - 1) := by
    intro leaf hleaf j
    have hc : ∀ l r, IsTotalQueryBound ((ideal F S.streamLen).compress l r) 1 :=
      fun l r ↦ isTotalQueryBound_query (.node l r)
    induction j with
    | zero => intro t; exact hleaf t
    | succ j ih =>
      intro t
      rw [merkleNodeWith]
      refine (isTotalQueryBound_bind (ih _) fun _ ↦ isTotalQueryBound_bind (ih _) fun _ ↦
        hc _ _).mono ?_
      have := Nat.one_le_two_pow (n := j + 1)
      rw [Nat.pow_succ 2 (j + 1)]
      omega
  unfold setupRo preprocessedKeyWith setupQueries
  split
  · trivial
  · refine (isTotalQueryBound_bind (hnode _ (fun _ ↦ isTotalQueryBound_query _) _ 0)
      fun _ ↦ Merkle.isTotalQueryBound_pure _).mono ?_
    rw [Nat.add_zero, Nat.pow_succ]
    unfold size
    omega

end CompStark.Iop.Setup
