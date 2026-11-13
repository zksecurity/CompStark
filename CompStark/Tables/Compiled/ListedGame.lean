/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.ListedOracle
public import CompStark.Compiled.MerkleOracle

/-! The record game for the list form. An adversary with `Q` oracle queries outputs a proof; the
game then expands each commitment's opening batch and climbs each opening against the oracle
(`post`), and the listing is the final log's hash inputs. A proof carrying the schedule's query
counts (`OpeningCounts`, implied by verification) has an unexplained opening under some table of
the run only if the log has a collision or a late preimage, so its probability is at most
`3 · Q'² / 2^256` with `Q' = Q + openingBudget params` (`unexplained_probability_le`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Compiled CompStark.Compiled.MerkleOracle
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp OracleSpec
open MixedMerkleTree.Knowledge Keccak.Commit.RandomOracleTrace
open scoped ENNReal

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} {Key : Type} {Response : Key → Type}

/-- The commitment slots of the compiled system. -/
abbrev Slot (params : Parameters S L k M) := Fin (treeShapes params.schedule params.semanticRowWords).length

/-- A slot's scheduled query count. -/
def slotCount (params : Parameters S L k M) (slot : Slot params) : ℕ :=
  (queryCounts params.schedule).getD slot.val 0

/-- At a slot whose batch carries its query count: the batch's expansion, then each opening's climb,
against the oracle. -/
def postSlot (shape : ℕ × ℕ × ℕ) (count : ℕ) (wire : Commit.Digest × List ℕ × Commit.Pruned) :
    OracleComp (MerkleTrace.Spec Response) Unit :=
  if wire.2.1.length = count then do
    let expanded ← expandO shape.1 shape.2.1 shape.2.2 wire.2.1 wire.2.2
    match expanded with
    | none => pure ()
    | some (_, paths) => (paths.take count).forM (climbO shape.1)
  else pure ()

/-- After the adversary's proof: every slot's expansion and climbs against the oracle. -/
def post (params : Parameters S L k M) (proof : Proof params) : OracleComp (MerkleTrace.Spec Response) Unit :=
  (List.finRange (treeShapes params.schedule params.semanticRowWords).length).forM fun slot =>
    postSlot (treeShapes params.schedule params.semanticRowWords)[slot] (slotCount params slot)
      (merkleAdversary params (fun _ : PUnit => proof) slot PUnit.unit)

/-- The queries `post` makes: at each slot, its count times twice its height plus four. -/
def openingBudget (params : Parameters S L k M) : ℕ :=
  ((List.finRange (treeShapes params.schedule params.semanticRowWords).length).map fun slot =>
    slotCount params slot * (2 * (treeShapes params.schedule params.semanticRowWords)[slot].1 + 4)).sum

/-- The record game: the adversary, then `post` on its proof. -/
def game (params : Parameters S L k M) (A : OracleComp (MerkleTrace.Spec Response) (Proof params)) :
    OracleComp (MerkleTrace.Spec Response) (Proof params) := do
  let proof ← A
  post params proof
  pure proof

/-- A list's effects add their budgets. -/
theorem forM_bound {α : Type} (f : α → OracleComp (MerkleTrace.Spec Response) PUnit) (g : α → ℕ)
    (each : ∀ x, IsTotalQueryBound (f x) (g x)) : (l : List α) → IsTotalQueryBound (l.forM f) (l.map g).sum
  | [] => pure_bound _
  | x :: l => by
    change IsTotalQueryBound (f x >>= fun _ => l.forM f) _
    rw [List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (each x) fun _ => forM_bound f g each l

/-- A list's effects log each element's queries. -/
theorem forM_covers {α : Type} (table : MerkleOracle.Table Response) (f : α → OracleComp (MerkleTrace.Spec Response) PUnit)
    (query : ByteArray ⊕ Key) : (l : List α) → (x : α) → x ∈ l →
      query ∈ (tableQueryLog (f x) table).map Sigma.fst → query ∈ (tableQueryLog (l.forM f) table).map Sigma.fst
  | [], _, member, _ => by cases member
  | y :: l, x, member, logged => by
    change query ∈ (tableQueryLog (f y >>= fun _ => l.forM f) table).map Sigma.fst
    rw [tableQueryLog_bind, List.map_append, List.mem_append]
    rcases List.mem_cons.mp member with same | later
    · subst same; exact Or.inl logged
    · exact Or.inr (forM_covers table f query l x later logged)

/-- A slot costs at most its count times twice its height plus four. -/
theorem postSlot_bound (shape : ℕ × ℕ × ℕ) (count : ℕ) (wire : Commit.Digest × List ℕ × Commit.Pruned) :
    IsTotalQueryBound (postSlot (Response := Response) shape count wire) (count * (2 * shape.1 + 4)) := by
  unfold postSlot
  split
  · rename_i h
    refine IsTotalQueryBound.mono (n₁ := count * (shape.1 + 1) + count * (shape.1 + 3)) ?_
      (by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega))
    refine isTotalQueryBound_bind (h ▸ expandO_bound _ _ _ _ _) fun expanded => ?_
    rcases expanded with _ | ⟨_, paths⟩
    · exact (pure_bound _).mono (Nat.zero_le _)
    · refine (forM_bound _ (fun _ => shape.1 + 3) (fun p => climbO_bound shape.1 p) _).mono ?_
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_take]
      exact Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
  · exact (pure_bound _).mono (Nat.zero_le _)

/-- `post` costs at most the opening budget. -/
theorem post_bound (params : Parameters S L k M) (proof : Proof params) :
    IsTotalQueryBound (post (Response := Response) params proof) (openingBudget params) :=
  forM_bound _ _ (fun _ => postSlot_bound _ _ _) _

/-- The game costs the adversary's budget plus the opening budget. -/
theorem game_bound (params : Parameters S L k M) (A : OracleComp (MerkleTrace.Spec Response) (Proof params))
    (Q : ℕ) (budget : IsTotalQueryBound A Q) :
    IsTotalQueryBound (game params A) (Q + openingBudget params) := by
  unfold game
  exact isTotalQueryBound_bind budget fun proof =>
    by simpa only [Nat.add_zero] using isTotalQueryBound_bind (post_bound params proof) fun _ => pure_bound _

/-- A derived node adversary reveals the operations of its verifying openings at its position. -/
theorem derivedAdversary_revealed {Coins Payload Digest : Type} [DecidableEq Digest] (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (height h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest) (v : MixedMerkleTree.Knowledge.Position) (c : Coins) :
    (derivedAdversary hash compress p₀ height h inj A X v c).2 = revealedOps hash compress p₀ height h inj A v c := by
  rw [derivedAdversary]

/-- An opening computes only operations of each position's shape. -/
theorem ops_shape {Payload Digest : Type} (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (height h : ℕ) (v : MixedMerkleTree.Knowledge.Position) (o : Opening Payload Digest) (op : Op Payload Digest)
    (member : op ∈ o.ops hash compress p₀ height h v) : v.opShape op = true := by
  unfold Opening.ops at member
  split at member
  · rcases hv : v.stage with _ | _ | _ | _ <;> rw [hv] at member
    · rw [List.mem_singleton] at member; subst member; simp only [Position.opShape, hv]
    · rw [List.mem_singleton] at member; subst member; simp only [Position.opShape, hv]
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp member; simp only [Position.opShape, hv]
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp member; simp only [Position.opShape, hv]
  · cases member

/-- A successful option map keeps its length. -/
theorem mapM_some_length {α β : Type} (f : α → Option β) :
    (l : List α) → (r : List β) → l.mapM f = some r → r.length = l.length
  | [], r, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    simp only [List.length_cons, mapM_some_length f l rest hrest]

/-- An expansion returns one path per query. -/
theorem expand_paths_length (hash : ByteArray → Commit.Digest) (height rowWords leafWords : ℕ)
    (queries : List ℕ) (batch : Commit.Pruned) (root : Commit.Digest) (paths : List Commit.Path)
    (expanded : Commit.expand hash height rowWords leafWords queries batch = some (root, paths)) :
    paths.length = queries.length := by
  unfold Commit.expand at expanded
  dsimp only at expanded
  split at expanded
  · cases expanded
  · obtain ⟨⟨nodes, all, unused⟩, -, expanded⟩ := Option.bind_eq_some_iff.mp expanded
    dsimp only at expanded
    split at expanded
    · cases expanded
    · obtain ⟨top, -, expanded⟩ := Option.bind_eq_some_iff.mp expanded
      obtain ⟨ordered, hordered, expanded⟩ := Option.bind_eq_some_iff.mp expanded
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at expanded
      rw [← expanded.2]
      exact mapM_some_length _ _ _ hordered

/-- A slot's wire batch carries its scheduled count when the proof carries the schedule's counts. -/
theorem wire_count (params : Parameters S L k M) (proof : Proof params) (counts : OpeningCounts params proof)
    (slot : Slot params) :
    (merkleAdversary params (fun _ : PUnit => proof) slot PUnit.unit).2.1.length = slotCount params slot := by
  have shapes := congrArg List.length (trees_shapes params proof)
  rw [List.length_map] at shapes
  have bound : slot.val < (trees params proof).length := by rw [shapes]; exact slot.isLt
  have counted := congrArg (fun l => l.getD slot.val 0) counts
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bound,
    Option.map_some, Option.getD_some] at counted
  simp only [merkleAdversary, List.getElem?_eq_getElem bound, Option.getD_some, slotCount,
    List.getD_eq_getElem?_getD]
  exact counted

/-- On a proof carrying the schedule's counts, `post` queries the bytes of every revealed operation,
each of its position's shape. -/
theorem post_covers (params : Parameters S L k M) (proof : Proof params) (counts : OpeningCounts params proof)
    (table : MerkleOracle.Table Response) (listing : List ByteArray)
    (position : Slot params × MixedMerkleTree.Knowledge.Position)
    (op : Op (List K) Commit.Digest)
    (revealed : op ∈ (listedNode table.hash params (proof, listing) position PUnit.unit).2) :
    position.2.opShape op = true ∧
      Sum.inl (Commit.operationBytes op) ∈ (tableQueryLog (post params proof) table).map Sigma.fst := by
  set shape := (treeShapes params.schedule params.semanticRowWords)[position.1]
  have count := wire_count params proof counts position.1
  unfold listedNode at revealed
  rw [derivedAdversary_revealed] at revealed
  unfold revealedOps at revealed
  obtain ⟨o, oMember, opMember⟩ := List.mem_flatMap.mp revealed
  have oListed := (List.mem_filter.mp oMember).1
  generalize hwire : merkleAdversary params (fun _ : PUnit => proof) position.1 PUnit.unit = wire at count
  obtain ⟨root, queries, batch⟩ := wire
  change o ∈ (Commit.mixedAdversary table.hash shape.1 shape.2.1 shape.2.2
    (merkleAdversary params (fun _ : PUnit => proof) position.1) PUnit.unit).2 at oListed
  simp only [Commit.mixedAdversary, hwire] at oListed
  rcases hexpand : Commit.expand table.hash shape.1 shape.2.1 shape.2.2 queries batch with _ | ⟨top, paths⟩
  · rw [hexpand] at oListed; cases oListed
  rw [hexpand] at oListed
  obtain ⟨p, pMember, rfl⟩ := List.mem_map.mp oListed
  refine ⟨ops_shape _ _ _ _ _ _ _ _ opMember, ?_⟩
  apply forM_covers table _ _ _ position.1 (List.mem_finRange _)
  rw [hwire]
  unfold postSlot
  simp only [count, ↓reduceIte]
  rw [tableQueryLog_bind, List.map_append, List.mem_append, eval_expandO]
  right
  have whole : paths.take (slotCount params position.1) = paths := List.take_of_length_le (by
    rw [expand_paths_length _ _ _ _ _ _ _ _ hexpand, count])
  change Sum.inl _ ∈ (tableQueryLog (match Commit.expand table.hash shape.1 shape.2.1 shape.2.2 queries batch with
    | none => pure ()
    | some (_, paths) => (paths.take (slotCount params position.1)).forM (climbO shape.1)) table).map Sigma.fst
  rw [hexpand]
  dsimp only
  rw [whole]
  exact forM_covers table _ _ _ p pMember (climbO_covers table shape.1 p position.2 op opMember)

/-- Each hash input of a log is cached. -/
theorem inputs_cached [DecidableEq Key] (log : QueryLog (MerkleTrace.Spec Response)) (input : ByteArray)
    (member : input ∈ inputs log) : ∃ value, Bcs.cacheOf log (.inl input) = some value := by
  have logged : ∃ entry ∈ log, entry.1 = Sum.inl input := by
    induction log with
    | nil => cases member
    | cons entry log ih =>
      rcases entry with ⟨query, answer⟩
      cases query with
      | inl other =>
        rcases List.mem_cons.mp member with same | later
        · subst same; exact ⟨_, List.mem_cons_self .., rfl⟩
        · obtain ⟨e, he, same⟩ := ih later; exact ⟨e, List.mem_cons_of_mem _ he, same⟩
      | inr _ =>
        obtain ⟨e, he, same⟩ := ih member; exact ⟨e, List.mem_cons_of_mem _ he, same⟩
  obtain ⟨entry, member, same⟩ := logged
  have known := Bcs.cacheOf_ne_none_of_mem member
  rw [same] at known
  exact Option.ne_none_iff_exists'.mp known

/-- The random-oracle bound for the list form. An adversary making at most `Q` queries outputs a
proof; the game climbs every opening against the oracle and lists the final log's hash inputs. That
the proof carries the schedule's query counts and has an unexplained opening under some table
agreeing with the run has probability at most `3 · Q'² / 2^256`, with
`Q' = Q + openingBudget params`, the budget being, over the commitment slots, the scheduled query
count times twice the tree height plus four. -/
theorem unexplained_probability_le [DecidableEq Key] [∀ key, SampleableType (Response key)]
    (params : Parameters S L k M) (A : OracleComp (MerkleTrace.Spec Response) (Proof params)) (Q : ℕ)
    (budget : IsTotalQueryBound A Q) :
    Pr{let result ← (simulateQ handler (game params A)).run []}[
        OpeningCounts params result.1 ∧ ∃ table : MerkleOracle.Table Response, Agrees table result.2 ∧
          Unexplained table.hash params (result.1, inputs result.2)] ≤
      (3 * (Q + openingBudget params) * (Q + openingBudget params) : ℕ) / (2 ^ 256 : ℝ≥0∞) := by
  have bound := MerkleTrace.exception_probability_le (fun _ : Key => ([] : List Commit.Digest)) 0
    (fun _ => le_rfl) (game params A) (Q + openingBudget params) (game_bound params A Q budget)
  refine le_trans (prEvent_mono_of_support _ _ _ fun result supported event => ?_) bound
  by_contra good
  obtain ⟨counts, table, agrees, unexplained⟩ := event
  have run := run_table (game params A) [] result supported table agrees
  have evaluated : evalWithAnswerFn (QueryImpl.ofFn table) A = result.1 := by
    have := run.1
    simp only [game, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at this
    exact this
  refine not_unexplained (fun _ => []) table result.2 agrees good params (result.1, inputs result.2)
    (fun input member => inputs_cached result.2 input member) ?_ unexplained
  intro position _ op revealed
  obtain ⟨shape, covered⟩ := post_covers params result.1 counts table (inputs result.2) position op revealed
  refine ⟨shape, mem_inputs ?_⟩
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp covered
  rw [← same]
  apply run.2.2 entry
  rw [game, tableQueryLog_bind, evaluated, tableQueryLog_bind]
  exact List.mem_append_right _ (List.mem_append_left _ entryMember)

end CompStark.Tables.Compiled
