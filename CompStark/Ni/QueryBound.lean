/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.Merkle.Multi
public import CompStark.Fri.Shapes
public import CompStark.Ni.BatchRun
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.Monad.Support
public import Mathlib.Tactic.Ring

/-! # The verifier's oracle calls

The verifier makes at most `verifierCallsAt n` oracle calls on a proof for `2 ^ n` rows
(`isTotalQueryBound_verifyWith`), and the verifying key's computation at most `setupQueries`
(`isTotalQueryBound_preprocessedKeyWith`). A Merkle multi-opening of `n` queries into matrices of
heights `2 ^ j ≤ 2 ^ L` of at most `G + 1` distinct heights hashes at most `n` leaves, compresses
at most `n` nodes per layer, and hashes and compresses once more per node where it injects a shorter
height (`isTotalQueryBound_verifyMultiM`): at most `n (1 + L + 2 G)` calls, `n (1 + L)` for the
STARK's matrices of one height. So FRI makes at most so many calls per query and round
(`costs_verifyFri`).

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

/-- A walk compresses at most once per node and level, and hashes and compresses once more per
node where it injects a group. -/
theorem walkM_bound (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hh : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hc : ∀ a b, IsTotalQueryBound (compress a b) 1) (rows : List (List (List F))) :
    ∀ levels groups padded (nodes : List (Nat × Nat × Vector F d)) sibs,
      IsTotalQueryBound (walkM hash compress rows levels groups padded nodes sibs)
        (nodes.length * (levels + 2 * groups.length))
  | 0, _, _, _, _ => trivial
  | levels + 1, groups, padded, nodes, sibs => by
    rw [walkM]
    have hlev := levelM_bound compress hc nodes sibs
    refine (isTotalQueryBound_bind_of_mem_support hlev.1
      (suffixBound := nodes.length * (levels + 2 * groups.length))
      fun r hr ↦ ?_).mono (by rw [Nat.mul_add, Nat.mul_add, Nat.mul_succ]; omega)
    obtain ⟨ps, sibs'⟩ := r
    have hps : ps.length ≤ nodes.length := hlev.2 _ hr
    dsimp only
    rcases groups with _ | ⟨⟨h, is⟩, rest⟩
    · exact (walkM_bound hash compress hh hc rows levels [] _ ps sibs').mono
        (by simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; nlinarith)
    · dsimp only
      split
      · have hm := mapM_bound (spec := spec) (fun (x : Nat × Nat × Vector F d) ↦ do
          return (x.1, x.2.1, ← compress x.2.2 (← hash (is.flatMap fun k ↦
            (rows.getD x.2.1 []).getD k [])))) 2
          (fun x ↦ (isTotalQueryBound_bind (hh _) fun _ ↦ isTotalQueryBound_bind (hc _ _)
            fun _ ↦ isTotalQueryBound_pure _).mono (by omega)) ps
        refine (isTotalQueryBound_bind_of_mem_support hm.1
          (suffixBound := ps.length * (levels + 2 * rest.length)) fun ps' hps' ↦ ?_).mono ?_
        · have := walkM_bound hash compress hh hc rows levels rest (padded / 2) ps' sibs'
          rwa [hm.2 _ hps'] at this
        · simp only [List.length_cons]
          nlinarith
      · exact (walkM_bound hash compress hh hc rows levels _ _ ps sibs').mono
          (by nlinarith)

/-- **A multi-opening of mixed heights.** A multi-opening of `n` queries into matrices of
heights `2 ^ j ≤ 2 ^ L`, among at most `G + 1` heights `hs`, makes at most `n (1 + L + 2 G)`
calls. -/
theorem isTotalQueryBound_verifyMultiM [DecidableEq F]
    (hash : List F → OracleComp spec (Vector F d))
    (compress : Vector F d → Vector F d → OracleComp spec (Vector F d))
    (hhash : ∀ xs, IsTotalQueryBound (hash xs) 1)
    (hcompress : ∀ a b, IsTotalQueryBound (compress a b) 1) (cap : List (Vector F d))
    (capHeight : Nat) (dims : List (Nat × Nat)) (L G : Nat)
    (hpow : ∀ x ∈ dims, ∃ j ≤ L, x.1 = 2 ^ j)
    (hs : List Nat) (hhs : ∀ x ∈ dims, x.1 ∈ hs) (hG : hs.length ≤ G + 1)
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Vector F d)) :
    IsTotalQueryBound (verifyMultiM hash compress cap capHeight dims indices rows sibs)
      (indices.length * (1 + L + 2 * G)) := by
  obtain ⟨keys, hk, hmem, hGeq⟩ := heightGroups_eq (dims.map (·.1))
  have hsub : keys ⊆ hs := fun h hh ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hmem h).mp hh)
    exact hhs x hx
  have hklen : keys.length ≤ hs.length :=
    (List.Nodup.subperm (hk.imp fun h ↦ Nat.ne_of_gt h) hsub).length_le
  unfold verifyMultiM
  rw [hGeq]
  rcases keys with _ | ⟨maxH, ks⟩
  · trivial
  have hmaxH : maxH ∈ dims.map (·.1) := (hmem maxH).mp List.mem_cons_self
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmaxH
  obtain ⟨j, hj, hxj⟩ := hpow x hx
  rw [← hxe, hxj] at *
  simp only [List.map_cons]
  rw [capLevels_two_pow, nextPowerOfTwo_two_pow]
  dsimp only
  split
  · have hleaves := mapM_bound (spec := spec) (fun (iq : Nat × Nat) ↦ do
      return (iq.1, iq.2, ← hash (((List.range (dims.map (·.1)).length).filter
        ((dims.map (·.1)).getD · 0 == 2 ^ j)).flatMap fun k ↦ (rows.getD iq.2 []).getD k [])))
      1 (fun _ ↦ isTotalQueryBound_bind (hhash _) fun _ ↦ isTotalQueryBound_pure _)
      (frontier indices)
    have hf := length_frontier_le indices
    simp only [List.length_cons] at hklen
    refine (isTotalQueryBound_bind_of_mem_support hleaves.1
      (suffixBound := indices.length * (L + 2 * G)) fun leaves hl ↦ ?_).mono
      (by rw [Nat.mul_one]; nlinarith)
    refine (isTotalQueryBound_bind (walkM_bound hash compress hhash hcompress rows
      (j - min capHeight j) _ _ leaves sibs) fun _ ↦ isTotalQueryBound_pure _).mono ?_
    rw [hleaves.2 _ hl, Nat.add_zero, List.length_map]
    exact Nat.mul_le_mul hf (by omega)
  · trivial

end CompStark.Merkle

namespace CompStark.Fri
open CompStark.Stark CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

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

theorem costs_observeCap (c : Cap F) : Costs (observeCap (ideal F K) c) 0 fun _ ↦ True :=
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

/-- A multi-opening of mixed heights costs at most `n (1 + L + 2 G)` calls. -/
theorem costs_checkMulti (capHeight : Nat) (commit : Cap F) (dims : List (Nat × Nat)) (L G : Nat)
    (hpow : ∀ x ∈ dims, ∃ j ≤ L, x.1 = 2 ^ j) (hs : List Nat) (hhs : ∀ x ∈ dims, x.1 ∈ hs)
    (hG : hs.length ≤ G + 1) (indices : List Nat) (rows : List (List (List F)))
    (sibs : List (Digest F)) :
    Costs (checkMulti (ideal F K) capHeight commit dims indices rows sibs)
      (indices.length * (1 + L + 2 * G))
      fun _ ↦ True := fun s ↦ by
  refine ⟨?_, fun _ _ _ ↦ trivial⟩
  change IsTotalQueryBound ((ExceptT.lift (Merkle.verifyMultiM (ideal F K).hash
    (ideal F K).compress commit.toList capHeight dims indices rows sibs) >>=
      fun a ↦ pure (a, s) : ExceptT String (OracleComp (spec F K)) _).run)
    (indices.length * (1 + L + 2 * G))
  simp only [ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ExceptT.run_pure]
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (Merkle.isTotalQueryBound_verifyMultiM _ _ (fun _ ↦ isTotalQueryBound_query _)
      (fun _ _ ↦ isTotalQueryBound_query _) commit.toList capHeight dims L G hpow hs hhs hG
      indices rows sibs)
    fun x ↦ (show IsTotalQueryBound (pure (Except.ok (x, s)) : OracleComp (spec F K) _) 0
      from trivial)

/-- The input multi-openings of rounds of mixed heights: at most `n (1 + L + 2 G)` calls per
round. -/
theorem costs_verifyInputs (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) (L G : Nat)
    (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyInputs (ideal F K) P logMax indices inputs rounds)
      (rounds.length * (indices.length * (1 + L + 2 * G))) fun _ ↦ True := by
  unfold verifyInputs
  refine costs_mono (costs_bind (a := 0)
    (b := rounds.length * (indices.length * (1 + L + 2 * G))) (costs_ensure _ _)
    fun _ _ ↦ costs_bind (b := 0) (costs_forIn_le _ _ _
    rounds.length (indices.length * (1 + L + 2 * G)) ?_ (fun _ ↦ True) trivial
    fun a ha b _ ↦ ?_) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) (by omega) fun _ _ ↦ trivial
  · rw [List.length_zip]; exact Nat.min_le_right _ _
  · obtain ⟨bo, commit, mats⟩ := a
    have hmat : ∀ mat ∈ mats, mat.1.logSize + P.logBlowup ∈ matHeights P rounds :=
      fun mat hm ↦ List.mem_map.mpr ⟨mat, List.mem_flatMap.mpr ⟨_, (List.of_mem_zip ha).2, hm⟩,
        rfl⟩
    dsimp only
    refine costs_mono (P := fun _ ↦ True) (costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_bind (costs_ensure _ _) fun _ _ ↦
      costs_bind (costs_checkMulti _ _ _ L G ?_ (hs.map (2 ^ ·)) ?_
        (by rw [List.length_map]; exact hG) _ _ _) fun _ _ ↦
      costs_bind (costs_ensure _ _) fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) ?_
      fun _ _ ↦ trivial
    · intro x hx
      obtain ⟨mat, hm, rfl⟩ := List.mem_map.mp hx
      exact ⟨_, hL _ (hmat mat hm), rfl⟩
    · intro x hx
      obtain ⟨mat, hm, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hhs _ (hmat mat hm))
    · rw [List.length_map]
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

/-- FRI's oracle calls after `α` on rounds of mixed heights: `d + 1` per fold, one for the query
grinding, and per query its index, its input openings and its folds' openings. -/
theorem costs_verifyFri (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (L G : Nat) (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyFri (ideal F K) P proof rounds alpha)
      (1 + (Challenge.d EF + 1) * (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
          ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length +
        P.numQueries * (1 + (rounds.length + (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length) * (1 + L + 2 * G))) fun _ ↦ True := by
  have hmax : (descHeights (matHeights P rounds)).headD 0 ≤ L := by
    rcases hD : descHeights (matHeights P rounds) with _ | ⟨a, t⟩
    · exact Nat.zero_le _
    · exact hL a ((mem_descHeights _ a).mp (hD ▸ List.mem_cons_self))
  unfold verifyFri
  dsimp only
  change Costs (ensure _ _ >>= fun _ ↦ ensure _ _ >>= fun _ ↦
    ensure ((descHeights (matHeights P rounds)).headD 0 ≤ twoAdicity F) _ >>= _) _ _
  set A := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
    ((descHeights (matHeights P rounds)).headD 0) (descHeights (matHeights P rounds))
  set N := P.numQueries
  set c := 1 + L + 2 * G
  refine costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_ensure_bind fun _ ↦ costs_ensure_bind fun _ ↦
    costs_free_bind (costs_observeList _) fun _ _ ↦ costs_ensure_bind fun hcs ↦ ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hcs
  replace hcs := hcs.1
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
  refine costs_bind_le (costs_verifyInputs P _ indices _ rounds L G hL hs hhs hG)
    (b := A.length * (N * c)) (fun _ _ ↦ ?_) (by rw [hind])
  -- the queries' folds and the commit-phase openings
  refine costs_free_bind (costs_mapM _ 0 (fun iq ↦ ?_) _) fun groups hg ↦ ?_
  · refine costs_bind_zero (costs_reduceQuery _ _ _ _ _ _) fun _ ↦
      costs_bind_zero (costs_foldQuery _ _ _ _ _ _ _ _) fun _ ↦ ?_
    costs_zero
  rw [List.length_zipIdx, hind] at hg
  refine costs_bind_le (b := 0) (costs_forIn_le _ _ _ A.length (N * c) ?_
    (fun logH ↦ logH ≤ L) hmax fun x _ logH hlog ↦ ?_)
    (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl
  · rw [List.length_zip, List.length_zipIdx]; exact Nat.min_le_right _ _
  obtain ⟨⟨cm, o⟩, la, i⟩ := x
  dsimp only
  refine costs_bind_le (costs_checkMulti _ _ _ (logH - la) 0
    (fun y hy ↦ ⟨logH - la, le_rfl, by rw [List.mem_singleton.mp hy]⟩) [2 ^ (logH - la)]
    (fun y hy ↦ by rw [List.mem_singleton.mp hy]; exact List.mem_singleton_self _) le_rfl _ _ _)
    (b := 0)
    (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_pure _ _ (by simp only [ForInStep.value]; omega))
    ?_
  rw [List.length_map, List.length_map, hg, Nat.add_zero]
  exact Nat.mul_le_mul_left _ (by omega)

theorem costs_verifyPcs (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF)
    (L G : Nat) (hL : ∀ h ∈ matHeights P rounds, h ≤ L) (hs : List Nat)
    (hhs : ∀ h ∈ matHeights P rounds, h ∈ hs) (hG : hs.length ≤ G + 1) :
    Costs (verifyPcs (ideal F K) P rounds proof)
      (Challenge.d EF + 2 + (Challenge.d EF + 1) * (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length +
        P.numQueries * (1 + (rounds.length + (foldSchedule P.maxLogArity
          (P.logBlowup + P.logFinalPolyLen) ((descHeights (matHeights P rounds)).headD 0)
          (descHeights (matHeights P rounds))).length) * (1 + L + 2 * G))) fun _ ↦ True := by
  unfold verifyPcs
  refine costs_ensure_bind fun _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
    costs_free_bind (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _
      fun _ _ ↦ costs_bind_zero (costs_forIn_zero _ _ _ fun _ _ ↦ costs_bind_zero
        (costs_observeExts _) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial) fun _ ↦
          costs_pure _ (fun _ ↦ True) trivial) fun _ ↦ costs_pure _ (fun _ ↦ True) trivial)
      fun _ _ ↦ costs_bind_le (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦
        costs_bind costs_sampleExt fun alpha _ ↦
          costs_verifyFri P proof rounds alpha L G hL hs hhs hG)
      (by omega)

end CompStark.Fri

namespace CompStark.Ni

theorem le_foldr_max : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: l, x, .tail _ h => (le_foldr_max l x h).trans (le_max_right _ _)

end CompStark.Ni

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Ni OracleSpec OracleComp

/-- A verifying key that passes the shape check belongs to preprocessed columns. -/
theorem preprocessedWidth_pos {F EF : Type} {A : Air F} {k : PreprocessedKey F}
    {o : OpenedValues EF} {db : Nat} (h : preprocessedShapeOk A (some k) o db = true) :
    0 < A.preprocessedWidth := by
  rcases o with ⟨tl, tn, _ | l, n, qc⟩
  · simp only [preprocessedShapeOk, Bool.false_eq_true] at h
  · simp only [preprocessedShapeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The verifier opens at most `inputRoundsOf` committed rounds at a query. -/
theorem length_openingRounds_le (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (zeta : EF) (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    (openingRounds A vk proof zeta).length ≤ inputRoundsOf A := by
  unfold openingRounds preprocessedRound inputRoundsOf
  cases vk with
  | none =>
    simp only [List.length_append, List.length_cons, List.length_nil]
    split <;> omega
  | some k =>
    have h0 := preprocessedWidth_pos hshape
    simp only [Nat.pos_iff_ne_zero.mp h0, ↓reduceIte, List.length_append, List.length_cons,
      List.length_nil]
    omega

/-- **The verifier's oracle calls.** On a proof for `2 ^ n` rows, the verifier makes at most
`verifierCallsAt n` oracle calls. -/
theorem isTotalQueryBound_verifyWith (P : Fri.Params) (A : Air F) {K : Nat}
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (publicValues : List F) :
    IsTotalQueryBound (verifyWith (ideal F K) P A vk proof publicValues)
      (verifierCallsAt EF P A proof.degreeBits) := by
  have hrun (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
      Costs (H := ideal F K) (do
      observeList (ideal F K) (starkSeedOf EF P A proof.degreeBits)
      observeCap (ideal F K) proof.traceCommit
      observeList (ideal F K) (preprocessedDigest vk)
      observeList (ideal F K) publicValues
      let alpha ← (sampleExt (ideal F K) : M _ EF)
      observeCap (ideal F K) proof.quotientCommit
      ensure (← checkWitness (ideal F K) P.oodPowBits proof.oodWitness)
        "out-of-domain witness"
      let zeta ← (sampleExt (ideal F K) : M _ EF)
      ensure (Ext.powTwo zeta proof.degreeBits - 1 != 0) "out-of-domain point in the trace domain"
      verifyPcs (ideal F K) P (openingRounds A vk proof zeta) proof.fri
      return (alpha, zeta)) (verifierCallsAt EF P A proof.degreeBits) fun _ ↦ True := by
    set L := proof.degreeBits + P.logBlowup
    set Ar := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) L [L]
    set V := Challenge.d EF + 2 + (Challenge.d EF + 1) * Ar.length + P.numQueries *
      (1 + (inputRoundsOf A + Ar.length) * (1 + L + 2 * 0))
    have hpcs : ∀ zeta : EF, Costs (H := ideal F K) (verifyPcs (ideal F K)
        P (openingRounds A vk proof zeta) proof.fri) V fun _ ↦ True := by
      intro zeta
      have hmats : ∀ r ∈ openingRounds A vk proof zeta, ∀ mat ∈ r.2,
          mat.1.logSize = proof.degreeBits := by
        intro r hr mat hmat
        simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hr
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
      have hM : ∀ h ∈ matHeights P (openingRounds A vk proof zeta), h = L := by
        intro h hh
        obtain ⟨mat, hm, rfl⟩ := List.mem_map.mp hh
        obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hm
        rw [hmats r hr mat hm]
      have hD : descHeights (matHeights P (openingRounds A vk proof zeta)) = [L] :=
        dedup_mergeSort_const _ _ _ hM (List.ne_nil_of_mem (List.mem_map_of_mem
          (List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_cons_self⟩)))
      refine costs_mono (costs_verifyPcs P _ proof.fri L 0 (fun h hh ↦ (hM h hh).le) [L]
        (fun h hh ↦ by rw [hM h hh]; exact List.mem_singleton_self _) le_rfl) ?_ fun _ h ↦ h
      rw [hD, List.headD_cons]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right
          (length_openingRounds_le A vk proof zeta hshape) _)) 1)) _
    refine costs_free_bind (costs_observeList _) fun _ _ ↦ costs_free_bind (costs_observeCap _)
      fun _ _ ↦ costs_free_bind (costs_observeList _) fun _ _ ↦
      costs_free_bind (costs_observeList _) fun _ _ ↦ costs_bind_le
      (b := 1 + Challenge.d EF + V) costs_sampleExt (fun alpha _ ↦ costs_free_bind
        (costs_observeCap _) fun _ _ ↦ costs_bind_le (b := Challenge.d EF + V)
        (costs_checkWitness _ _) (fun _ _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (b := V)
          costs_sampleExt (fun zeta _ ↦ costs_ensure_bind fun _ ↦ costs_bind_le (a := V) (b := 0)
            (hpcs zeta) (fun _ _ ↦ costs_pure _ (fun _ ↦ True) trivial) le_rfl) le_rfl)
        (by omega)) ?_
    simp only [V, Ar, L, verifierCallsAt]
    exact le_of_eq (by ring)
  unfold verifyWith
  dsimp only
  by_cases h1 : proof.degreeBits + A.logQuotientChunks proof.degreeBits ≤ twoAdicity F
  · rw [ite_eq_left h1]
    by_cases h2 : A.periodicFits proof.degreeBits = true
    · rw [ite_eq_left h2]
      split
      · split
        · rename_i hshape
          split
          · split
            swap
            · trivial
            rw [ExceptT.run_bind]
            apply IsTotalQueryBound.mono (n₁ := verifierCallsAt EF P A proof.degreeBits + 0) _
              (Nat.add_zero _).le
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

variable (S : Setup EF) [S.Folds]

/-- **The setup's oracle calls.** The verifying key for `2 ^ n` rows costs a leaf hash per row of
the preprocessed trace's extension and a compression per inner node. -/
theorem isTotalQueryBound_preprocessedKeyWith (P : Fri.Params) (A : Air F) (n K : Nat) :
    IsTotalQueryBound (preprocessedKeyWith (ideal F K) P A n)
      (if A.preprocessedWidth = 0 then 0 else 2 * 2 ^ (n + P.logBlowup) - 1) := by
  have hnode : ∀ (leaf : Nat → OracleComp (spec F K) (Digest F)),
      (∀ r, IsTotalQueryBound (leaf r) 1) → ∀ j t,
      IsTotalQueryBound (merkleNodeWith (ideal F K) leaf j t) (2 ^ (j + 1) - 1) := by
    intro leaf hleaf j
    have hc : ∀ l r, IsTotalQueryBound ((ideal F K).compress l r) 1 :=
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
  unfold preprocessedKeyWith
  split
  · trivial
  · unfold merkleCapWith
    refine (isTotalQueryBound_bind (isTotalQueryBound_bind (Merkle.mapM_bound _ _
      (hnode _ (fun _ ↦ isTotalQueryBound_query _) _) _).1
      fun _ ↦ Merkle.isTotalQueryBound_pure _) fun _ ↦ Merkle.isTotalQueryBound_pure _).mono ?_
    rw [List.length_range, Nat.add_zero, Nat.add_zero]
    have hc := Nat.min_le_right P.capHeight (n + P.logBlowup)
    generalize min P.capHeight (n + P.logBlowup) = c at hc ⊢
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add,
      show c + (n + P.logBlowup - c + 1) = n + P.logBlowup + 1 by omega,
      Nat.pow_succ]
    have := Nat.one_le_two_pow (n := c)
    omega

theorem isTotalQueryBound_setupRo : IsTotalQueryBound S.setupRo S.setupQueries :=
  isTotalQueryBound_preprocessedKeyWith S.params S.air S.logN _

end CompStark.Iop.Setup
