/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.HonestRun
public import CompStark.Tables.Compiled.Acceptance
public import CompStark.Tables.Compiled.Verifier
public import CompStark.Compiled.WhirRun

/-! Completeness of the compiled system for the honest non-interactive prover that runs
(`Data.prove`): the ideal run of the compiled prover is the composed honest transcript at the
coins the duplex draws (`prover_idealRun`), so the composed completeness, the honest Merkle batches
and the duplex checks of the driven path give acceptance. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- An external argument's prover follows an honest strategy: from the argument's start
relation, every ideal run is the honest transcript at some coins. -/
def ExternalFollows (params : Parameters S L k M) (honest : params.external.Honest)
    (external : params.data.ExternalProver) : Prop :=
  ∀ o q, params.external.start o q → ∀ state path final,
    params.externalPresentation.idealRun (external o q) state = some (path, final) →
      ∃ coins, path = honest.honest o q coins

/-- The compiled prover's words decode from its rows. -/
theorem prover_faithful (params : Parameters S L k M) (external : params.data.ExternalProver)
    (w : Witness K S.tables.length) :
    Presentation.Prover.Faithful params.data.presentation (params.data.prover external w) := by
  intro _
  refine ⟨baseRows_decode _ _ (wordOfRows_full _), baseRows_length _ _ (wordOfRows_full _), ?_⟩
  exact Presentation.Prover.faithful_append (outerPresentation params)
    (whirPresentation params.data.evaluated.schedule) _ _
    (Presentation.Prover.faithful_of_shapes _ (outerPresentation_shapes params) _)
    (fun _ => whirWireProver_faithful params.data.evaluated _ _ _)

/-- The compiled prover's ideal run is the composed honest transcript at the drawn coins. -/
theorem prover_idealRun (params : Parameters S L k M) (honest : params.external.Honest)
    (external : params.data.ExternalProver) (follows : ExternalFollows params honest external)
    (w : Witness K S.tables.length) (hsat : S.Satisfied L w) (padded : S.Padded L w)
    (state : Transcript.State)
    (path : (Composed.protocol params.toParameters).tree.ExecutionPath) (final : Transcript.State)
    (h : params.data.presentation.idealRun (params.data.prover external w) state = some (path, final)) :
    ∃ coins externalCoins, path = honestPath params.toSetup params.schedule
      (fun o q => honest.honest o q externalCoins) w coins := by
  erw [Presentation.idealRun_merkle] at h
  obtain ⟨rest, hrest, pair⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hpath, -⟩ := Prod.mk.inj pair
  subst hpath
  let q := Pcs.tableOf M (S.stackValues L M w)
  have hprover : (params.data.prover external w state).2.2 =
      Presentation.Prover.append params.data.outerPresentation (whirPresentation params.data.evaluated.schedule)
        (params.data.outerProver external w q) (fun outer =>
          whirProver params.data.evaluated (Whir.TableCache.ofTable fun u => ofK (q u)).get
            (openingClaims params.data.setup (outerOutput params.data.setup outer))) := rfl
  rw [hprover] at hrest
  erw [Presentation.idealRun_append] at hrest
  obtain ⟨outer, houter, hwhirMap⟩ := Option.bind_eq_some_iff.mp hrest
  obtain ⟨whir, hwhir, rfl⟩ := Option.map_eq_some_iff.mp hwhirMap
  have houterProver : params.data.outerProver external w q =
      Presentation.Prover.append _ _
        (Presentation.Prover.append _ _ (busProver S L k w) fun busPath =>
          tableProver S L k ((Bus.outputClaim S L k busPath).getD rejectedBus) w)
        fun first =>
          let parts := splitPath (Bus.protocol S L k) (TableSumcheck.protocol S L) first
          let bus := (Bus.outputClaim S L k parts.1).getD rejectedBus
          external ((TableSumcheck.outputClaim S L k bus parts.2).getD rejectedOutput) q := rfl
  rw [houterProver] at houter
  erw [Presentation.idealRun_append] at houter
  obtain ⟨inner, hinner, hexternalMap⟩ := Option.bind_eq_some_iff.mp houter
  obtain ⟨ext, hext, rfl⟩ := Option.map_eq_some_iff.mp hexternalMap
  erw [Presentation.idealRun_append] at hinner
  obtain ⟨busRun, hbusRun, htableMap⟩ := Option.bind_eq_some_iff.mp hinner
  obtain ⟨tableRun, htableRun, rfl⟩ := Option.map_eq_some_iff.mp htableMap
  obtain ⟨busCoins, busFinal, hbus⟩ := bus_idealRun S L k w _
  rw [hbus] at hbusRun
  cases hbusRun
  obtain ⟨tableCoins, tableFinal, htable⟩ := table_idealRun S L k
    ((Bus.outputClaim S L k (honestBusPath S L k w busCoins)).getD rejectedBus) w busFinal
  rw [htable] at htableRun
  cases htableRun
  rw [splitPath_joinPath] at hext
  obtain ⟨externalCoins, hexternal⟩ := follows _ _
    (Composed.honest_start params.toParameters w hsat padded busCoins tableCoins) _ ext.1 ext.2 hext
  obtain ⟨openingCoins, hopening⟩ := whir_idealRun params.data.evaluated _ _ _ whir.1 whir.2 hwhir
  refine ⟨⟨busCoins, tableCoins, openingCoins⟩, externalCoins, ?_⟩
  rw [hopening, hexternal, TableCache_get]
  change (⟨wordOfRows (headRowsBase params.data.evaluated (Pcs.tableOf M (S.stackValues L M w))), _⟩ :
    (Composed.protocol params.toParameters).tree.ExecutionPath) = _
  rw [wordOfRows_base]
  rfl

/-- The WHIR query lists of an opened path do not depend on the openings. -/
theorem queries_openings (params : Parameters S L k M)
    (path : (StandardBcs.compile Commit.Digest (presentation params).coin).tree.ExecutionPath)
    (first second : Openings) :
    whirQueries params.schedule (executionParts params.toParameters
      ((presentation params).openedPath Commit.hash path first)).2 =
    whirQueries params.schedule (executionParts params.toParameters
      ((presentation params).openedPath Commit.hash path second)).2 := by
  obtain ⟨head, tail, -, parsed⟩ := (outerPresentation params).append_split
    (whirPresentation params.schedule) (outerPresentation_shapes params) path.2 [] 1
  have reference : ∀ openings : Openings,
      whirQueries params.schedule (executionParts params.toParameters
        ((presentation params).openedPath Commit.hash path openings)).2 =
      whirQueries params.schedule ((whirProjection params.schedule (fun _ => id)).path
        ((whirWirePresentation params.schedule).reconstruct tail [] (fun _ _ _ => none) 1)) := by
    intro openings
    unfold Presentation.openedPath
    rw [Presentation.reconstruct_opened, Presentation.reconstruct_openings]
    change whirQueries params.schedule (splitPath (outerProtocol params.toSetup)
      (Whir.opening E params.schedule)
        (((outerPresentation params).append (whirPresentation params.schedule)).reconstruct path.2 []
          _ 1)).2 = _
    rw [parsed]
    exact whirQueries_reconstruct params.schedule (fun _ => id) tail [] _ _ 1
  rw [reference first, reference second]

/-- A full row is its own leaf image. -/
theorem restoreLeaf_full (row : List K) (leafWords : ℕ) (full : row.length = leafWords) :
    Commit.restoreLeaf leafWords row = row := by
  unfold Commit.restoreLeaf
  rw [full, Nat.sub_self, List.replicate_zero, List.nil_append]

/-- Completeness of the compiled system for the honest non-interactive prover: for every witness
satisfying the system whose padding rows are the padding row, an external prover following an
honest strategy, and a schedule sampling at least one query per level, every proof the prover
produces is accepted. -/
theorem completeness (params : Parameters S L k M) (honest : params.external.Honest)
    (external : params.data.ExternalProver) (follows : ExternalFollows params honest external)
    (positive : QueriesPositive params.schedule) (w : Witness K S.tables.length)
    (hsat : S.Satisfied L w) (padded : S.Padded L w) (proof : Proof params)
    (proved : params.data.prove external w = some proof) : verify params proof := by
  unfold Data.prove at proved
  split at proved
  · cases proved
  rename_i result hrun
  cases proved
  have faithful := prover_faithful params external w
  obtain ⟨wire, grind⟩ := Presentation.run_checks _ _ _ result hrun
  rw [← check_iff]
  change (WireObserver.check _ (presentation params).observer (initialState params) result.1 &&
    (presentation params).grindingCheck result.1 (initialState params) &&
    openingCheck params (params.data.attachOpenings result.1 result.2)) = true
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨wire, grind⟩, (openingCheck_iff params _).mpr ?_⟩
  let trees0 := (presentation params).trees result.1 [] 0
  let queries0 := whirQueries params.schedule (executionParts params.toParameters
    ((presentation params).openedPath Commit.hash result.1 [])).2
  have aligned := Presentation.run_trees _ _ faithful _ result hrun [] 0
  have shapes0 : trees0.map (fun tree => (tree.height, tree.rowWords, tree.leafWords)) =
      treeShapes params.schedule params.semanticRowWords := trees_shapes params ⟨PUnit.unit, result.1, []⟩
  have lenRows : result.2.length = trees0.length := aligned.length_eq.symm
  have lenTrees : trees0.length = (treeShapes params.schedule params.semanticRowWords).length := by
    rw [← shapes0, List.length_map]
  have lenQueries : queries0.length = trees0.length :=
    (whirQueries_length _ _ _).trans lenTrees.symm
  let openings : Openings := (trees0.zip (result.2.zip queries0)).map fun entry =>
    ⟨entry.2.2, Commit.honestBatch entry.1.height entry.1.leafWords entry.2.1 entry.2.2⟩
  change openingAccept Commit.hash params ⟨PUnit.unit, result.1, openings⟩
  have lenOpenings : openings.length = trees0.length := by
    simp only [openings, List.length_map, List.length_zip, lenRows, lenQueries, Nat.min_self]
  have atIndex : ∀ j (bound : j < trees0.length), openingAt openings j =
      ⟨queries0[j]'(lenQueries ▸ bound), Commit.honestBatch trees0[j].height trees0[j].leafWords
        (result.2[j]'(lenRows ▸ bound)) (queries0[j]'(lenQueries ▸ bound))⟩ := by
    intro j bound
    rw [openingAt, List.getElem?_eq_getElem (lenOpenings ▸ bound), Option.getD_some]
    simp only [openings, List.getElem_map, List.getElem_zip]
  have treesEq : trees params ⟨PUnit.unit, result.1, openings⟩ =
      trees0.mapIdx fun index tree => { tree with opening := openingAt openings (0 + index) } :=
    Presentation.trees_openings _ result.1 openings 0
  have lenProofTrees : (trees params ⟨PUnit.unit, result.1, openings⟩).length = trees0.length := by
    rw [treesEq, List.length_mapIdx]
  have queriesEq : openings.map OpeningBatch.queries = queries0 := by
    apply List.ext_getElem
    · rw [List.length_map, lenOpenings, lenQueries]
    · intro j left right
      rw [List.getElem_map]
      simp only [openings, List.getElem_map, List.getElem_zip]
  have queryLists : openings.map OpeningBatch.queries = whirQueries params.schedule
      (executionParts params.toParameters ((presentation params).openedPath Commit.hash result.1 openings)).2 :=
    queriesEq.trans (queries_openings params result.1 [] openings)
  have length : openings.length = (trees params ⟨PUnit.unit, result.1, openings⟩).length :=
    lenOpenings.trans lenProofTrees.symm
  have treeAt : ∀ j (bound : j < trees0.length),
      (trees params ⟨PUnit.unit, result.1, openings⟩)[j]'(lenProofTrees ▸ bound) =
        { trees0[j] with opening := openingAt openings j } := by
    intro j bound
    simp only [treesEq, List.getElem_mapIdx, Nat.zero_add]
  have row : ∀ j (bound : j < trees0.length),
      trees0[j].root = Commit.root trees0[j].height
        (fun i => Commit.restoreLeaf trees0[j].leafWords ((result.2[j]'(lenRows ▸ bound)) i)) ∧
      ∀ i < 2 ^ trees0[j].height, ((result.2[j]'(lenRows ▸ bound)) i).length = trees0[j].rowWords :=
    fun j bound => aligned.get bound (lenRows ▸ bound)
  have shape : ∀ j (bound : j < trees0.length),
      (trees0[j].height, trees0[j].rowWords, trees0[j].leafWords) =
        (treeShapes params.schedule params.semanticRowWords)[j]'(lenTrees ▸ bound) := by
    intro j bound
    simp only [← shapes0, List.getElem_map]
  have full : ∀ j (bound : j < trees0.length), trees0[j].rowWords = trees0[j].leafWords := by
    intro j bound
    have entry : ((treeShapes params.schedule params.semanticRowWords)[j]'(lenTrees ▸ bound)).2.1 =
        ((treeShapes params.schedule params.semanticRowWords)[j]'(lenTrees ▸ bound)).2.2 :=
      treeShapes_full params.schedule _ (List.getElem_mem (lenTrees ▸ bound))
    rw [← shape j bound] at entry
    exact entry
  have nonempty : ∀ j (bound : j < trees0.length), queries0[j]'(lenQueries ▸ bound) ≠ [] :=
    fun j bound => whirQueries_nonempty _ positive _ j (lenQueries ▸ bound)
  have range : ∀ j (bound : j < trees0.length), ∀ x ∈ queries0[j]'(lenQueries ▸ bound),
      x < 2 ^ trees0[j].height := by
    intro j bound x member
    have inner := whirQueries_range params.schedule _ params.semanticRowWords j (lenQueries ▸ bound) x member
    have height := congrArg Prod.fst (shape j bound)
    simp only at height
    rw [height]
    exact inner
  have treesAccept : ∀ tree ∈ trees params ⟨PUnit.unit, result.1, openings⟩, tree.accepts Commit.hash := by
    intro tree member
    obtain ⟨j, bound, rfl⟩ := List.getElem_of_mem member
    have bound0 : j < trees0.length := lenProofTrees ▸ bound
    rw [treeAt j bound0]
    unfold TreeOpening.accepts
    rw [atIndex j bound0]
    change Commit.accepts Commit.hash trees0[j].height trees0[j].rowWords trees0[j].leafWords
      (queries0[j]'(lenQueries ▸ bound0)) (Commit.honestBatch trees0[j].height trees0[j].leafWords
        (result.2[j]'(lenRows ▸ bound0)) (queries0[j]'(lenQueries ▸ bound0))) trees0[j].root = true
    rw [(row j bound0).1]
    exact Commit.honest_accepts _ _ _ _ (le_of_eq (full j bound0)) (row j bound0).2 _ (nonempty j bound0)
      (range j bound0)
  let leafImage : ℕ → ℕ → Option (List K) := fun index column =>
    some ((result.2.getD index fun _ => []) column)
  have agreement : LeafAgreement (fun _ tree => tree.openedLeaves Commit.hash) (fun index _ => leafImage index) 0
      (trees params ⟨PUnit.unit, result.1, openings⟩) := by
    apply LeafAgreement.of_forall
    intro j bound query member
    have bound0 : j < trees0.length := lenProofTrees ▸ bound
    rw [treeAt j bound0] at member ⊢
    change query ∈ (openingAt openings j).queries at member
    rw [atIndex j bound0] at member
    change query ∈ queries0[j]'(lenQueries ▸ bound0) at member
    unfold TreeOpening.openedLeaves
    rw [atIndex j bound0]
    obtain ⟨paths, expanded, leaves⟩ := Commit.honest_expand trees0[j].height trees0[j].rowWords
      trees0[j].leafWords (result.2[j]'(lenRows ▸ bound0)) (le_of_eq (full j bound0)) (row j bound0).2 _
      (nonempty j bound0) (range j bound0)
    change (match Commit.expand Commit.hash trees0[j].height trees0[j].rowWords trees0[j].leafWords
        (queries0[j]'(lenQueries ▸ bound0)) (Commit.honestBatch trees0[j].height trees0[j].leafWords
          (result.2[j]'(lenRows ▸ bound0)) (queries0[j]'(lenQueries ▸ bound0))) with
      | none => fun _ => none
      | some (_, paths) => fun index =>
          (paths.find? fun path : Commit.Path => path.index == index).map Commit.Path.leaf)
        query = leafImage (0 + j) query
    rw [expanded]
    dsimp only
    have cover := (Commit.accepted_openings_verify Commit.hash _ _ _ _ _ _ paths expanded).1
    rw [← cover] at member
    obtain ⟨found, foundMember, foundIndex⟩ := List.mem_map.mp member
    cases hfind : paths.find? (fun path => path.index == query) with
    | none =>
        exact absurd (by simp only [foundIndex, beq_self_eq_true])
          (List.find?_eq_none.mp hfind found foundMember)
    | some p =>
        have pIndex : p.index = query := by simpa only [beq_iff_eq] using List.find?_some hfind
        have pLeaf := leaves p (List.mem_of_find?_eq_some hfind)
        have queryBound : query < 2 ^ trees0[j].height := range j bound0 query (cover ▸ member)
        change Option.map Commit.Path.leaf (some p) = some ((result.2.getD (0 + j) fun _ => []) query)
        rw [Option.map_some, pLeaf, pIndex, restoreLeaf_full _ _ (((row j bound0).2 query queryBound).trans (full j bound0)),
          Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lenRows ▸ bound0), Option.getD_some]
  have accepted : Composed.Accepts params.toParameters ((presentation params).originalPath
      (StandardBcs.extractedPath (coin params) result.1 ((presentation params).messages result.1 leafImage 0))) := by
    erw [Presentation.reconstruct_messages (openings := [])]
    obtain ⟨after, ideal⟩ := Presentation.run_reconstruct _ _ faithful _ result hrun [] (fun index _ => leafImage index) 0
      (by
        intro i bound tree
        funext column
        simp only [leafImage, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
          Option.getD_some])
    obtain ⟨coins, externalCoins, hpath⟩ := prover_idealRun params honest external follows w hsat padded
      _ _ _ ideal
    erw [hpath]
    exact Composed.completeness params.toParameters honest externalCoins w hsat padded coins
  exact ⟨acceptance_of_leafAgreement_complete Commit.hash params ⟨PUnit.unit, result.1, openings⟩ leafImage
    queryLists length accepted agreement, queryLists, length, treesAccept⟩

end CompStark.Tables.Compiled
