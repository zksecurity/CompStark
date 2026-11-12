/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus and BusSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.BusDecomposition
public import CompStark.Multilinear.Retained

/-! The bus argument of a set of tables as a public-coin protocol with its knowledge certificate.

The verifier draws `(α, β)`; the prover sends the common root of the pushed and pulled trees and
the root of the nonzero tree; the grand-product GKR, its riders the constraint residuals, reduces
the three roots to leaf claims at one point; the prover sends the directly opened tables'
boundary values. The endpoint (`Terminal`) owes the boundary columns' extensions, the riders at
the point, and one table debt per side. The certificate's extractor keeps the committed witness
fixed; its only non-GKR error is the fingerprint test's, `max 1 k · 2 ^ μ / |E|`. -/

@[expose] public section

namespace CompStark.Tables.Bus

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp

variable (S : System K) (L : Layout S.tables.length) (k : ℕ)

/-- The bus's depth. -/
abbrev μ : ℕ := S.depth L

/-- The bus output: challenges, the GKR's final point, one debt per side, the boundary values and
whether every public check passed. -/
structure Output where
  /-- Fingerprint coordinates. -/
  alpha : Fin k → E
  /-- Grand-product challenge. -/
  beta : E
  /-- The GKR's final point. -/
  point : List E
  /-- The push, pull and nonzero debts for the table sumcheck. -/
  remainders : Fin 3 → E
  /-- The directly opened tables' boundary values. -/
  boundary : S.BoundaryValues L
  /-- Whether every public check passed. -/
  active : Bool

/-- The output of the three leaf claims and the boundary values. -/
def output (α : Fin k → E) (β : E) (c : GrandProduct.Claim) (vals : S.BoundaryValues L)
    (active : Bool) : Output S L k :=
  ⟨α, β, c.point, fun side ↦ c.values side - S.publicPart L k α β (μ S L) vals side c.point, vals, active⟩

/-- The endpoint: boundary values are the boundary columns' extensions, the riders vanish at the
point, and each debt is its side's table debt. -/
def Terminal (o : Output S L k) (w : Witness K S.tables.length) : Prop :=
  o.active = true ∧ S.Shaped L w ∧ o.point.length = μ S L ∧
    (∀ i, GrandProduct.rider (S.riders L) w i (o.point.take ((S.riders L).height i)) = 0) ∧
    (∀ p ∈ S.boundaryColumns L, S.boundaryValue L o.boundary p.1 p.2 =
      S.column L w p.1 p.2 (o.point.take (L.logHeight p.1))) ∧
    ∀ side, o.remainders side = S.tableDebt L k o.alpha o.beta (μ S L) w side o.point

/-- The bus's input relation: shapes, balanced buses, nonzero columns and zero riders. -/
def Input (w : Witness K S.tables.length) : Prop :=
  S.Shaped L w ∧ (∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) ∧
    (∀ t, ∀ i < L.executed t, ∀ c ∈ (S.table t).nonzero, ((w t).getD i #[]).getD c 0 ≠ 0) ∧
    GrandProduct.RidersZero (S.riders L) w

/-- After the fingerprint draw: the pushed and pulled roots agree. -/
def afterFingerprint (α : Fin k → E) (β : E) (w : Witness K S.tables.length) : Prop :=
  S.Shaped L w ∧
    (∀ t, ∀ i < L.executed t, ∀ c ∈ (S.table t).nonzero, ((w t).getD i #[]).getD c 0 ≠ 0) ∧
    GrandProduct.RidersZero (S.riders L) w ∧
    GrandProduct.level (μ S L) 0 (S.leaves L k w α β) 0 0 =
      GrandProduct.level (μ S L) 0 (S.leaves L k w α β) 1 0

/-- The leaf relation at the GKR's final claim. -/
def leafRelation (α : Fin k → E) (β : E) (c : GrandProduct.Claim) (active : Bool)
    (w : Witness K S.tables.length) : Prop :=
  active = true ∧ S.Shaped L w ∧ c.Holds (μ S L) (μ S L) (S.leaves L k w α β) ∧
    ∀ i, GrandProduct.rider (S.riders L) w i (c.point.take ((S.riders L).height i)) = 0

/-- The boundary values are the bus's last message. -/
def terminalProtocol : Protocol := .public .sender (S.BoundaryValues L) fun _ ↦ .done

/-- The bus protocol. -/
def protocol : Protocol :=
  .public .receiver ((Fin k → E) × E) fun _ ↦
    .public .sender (E × E) fun _ ↦
      GrandProduct.protocol (terminalProtocol S L) (GrandProduct.layers (μ S L)) 0

/-- Prefix predicates on the bus's transcript tree, the witness fixed throughout. -/
noncomputable def labels : Retained.Labels (Witness K S.tables.length) (protocol S L k).tree :=
  ⟨Input S L, fun (ab : (Fin k → E) × E) ↦ ⟨afterFingerprint S L k ab.1 ab.2, fun (roots : E × E) ↦
    GrandProduct.labels (S.riders L) (μ S L) (fun w ↦ S.leaves L k w ab.1 ab.2)
      (terminalProtocol S L)
      (fun c active ↦ ⟨leafRelation S L k ab.1 ab.2 c active, fun vals ↦
        Terminal S L k (output S L k ab.1 ab.2 c vals active)⟩)
      (GrandProduct.layers (μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
      (decide (roots.2 ≠ 0))⟩⟩

/-- The extractor keeps the committed witness throughout. -/
noncomputable def extractor (w₀ : Witness K S.tables.length) :
    RoundExtractor (protocol S L k).tree (Retained.state w₀ (Input S L)) :=
  Retained.extractor w₀ (labels S L k)

/-- One joint `(α, β)` draw, then the GKR's draws. -/
noncomputable def challenges :
    RoundExtractor.ChallengeSchedule (protocol S L k).tree (protocol S L k).roles :=
  ⟨⟨$ᵗ ((Fin k → E) × E), overE (max 1 k * 2 ^ μ S L)⟩, fun _ ↦
    ⟨PUnit.unit, fun (roots : E × E) ↦ GrandProduct.challenges (terminalProtocol S L)
      ⟨PUnit.unit, fun _ ↦ PUnit.unit⟩ (GrandProduct.layers (μ S L)) 0
        ⟨[], ![roots.1, roots.1, roots.2]⟩⟩⟩

/-- The bus endpoint parsed from a transcript; an aborted descent exports none. -/
def outputClaim (path : (protocol S L k).tree.ExecutionPath) : Option (Output S L k) := do
  let ab : (Fin k → E) × E := path.1
  let roots : E × E := path.2.1
  let (c, active, boundaryPath) ← GrandProduct.result (terminalProtocol S L)
    (GrandProduct.layers (μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
    (decide (roots.2 ≠ 0)) path.2.2
  return output S L k ab.1 ab.2 c boundaryPath.1 active

/-- The bus endpoint's claim family. -/
def claimFamily : ClaimFamily Unit := ⟨fun _ ↦ Option (Output S L k)⟩

/-- The bus endpoint problem on the fixed witness. -/
def terminalProblem (w₀ : Witness K S.tables.length) : Problem (claimFamily S L k) where
  Witness _ _ := Witness K S.tables.length
  admissible _ _ := True
  rel _ claim w := w = w₀ ∧ match claim with | none => False | some o => Terminal S L k o w
  rel_admissible := by intros; trivial

set_option smartUnfolding false in
set_option backward.isDefEq.respectTransparency false in
/-- Parsing the transcript preserves the endpoint predicate. -/
theorem outputClaim_endpoint (path : (protocol S L k).tree.ExecutionPath) :
    Retained.endpoint (labels S L k) path =
      match outputClaim S L k path with
      | none => fun _ ↦ False
      | some o => Terminal S L k o := by
  rcases path with ⟨ab, roots, path⟩
  change (Fin k → E) × E at ab
  change E × E at roots
  change (GrandProduct.protocol (terminalProtocol S L) (GrandProduct.layers (μ S L)) 0).tree.ExecutionPath at path
  change Retained.endpoint (GrandProduct.labels (S.riders L) (μ S L)
    (fun w ↦ S.leaves L k w ab.1 ab.2) (terminalProtocol S L)
    (fun c active ↦ ⟨leafRelation S L k ab.1 ab.2 c active, fun vals ↦
      Terminal S L k (output S L k ab.1 ab.2 c vals active)⟩)
    (GrandProduct.layers (μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
    (decide (roots.2 ≠ 0))) path = _
  erw [GrandProduct.result_endpoint]
  unfold outputClaim
  dsimp only
  cases hr : GrandProduct.result (terminalProtocol S L) (GrandProduct.layers (μ S L)) 0
    ⟨[], ![roots.1, roots.1, roots.2]⟩ (decide (roots.2 ≠ 0)) path with
  | none => rfl
  | some parsed => rcases parsed with ⟨c, active, rest⟩; rfl

set_option smartUnfolding false in
set_option backward.isDefEq.respectTransparency false in
/-- The extractor's terminal knowledge is the bus endpoint. -/
noncomputable def terminalRelation (w₀ : Witness K S.tables.length) :
    TerminalRelation (extractor S L k w₀) (terminalProblem S L k w₀) (fun _ ↦ ())
      (outputClaim S L k) := by
  unfold extractor terminalProblem claimFamily
  refine ⟨Retained.terminalEquiv w₀ (labels S L k), ?_⟩
  intro path witness
  refine (Retained.terminal_iff w₀ (labels S L k) path witness).trans ?_
  dsimp only [Retained.state]
  rw [outputClaim_endpoint]
  cases outputClaim S L k path <;> rfl

/-- Every side fits the bus's depth. -/
theorem depth_fits : S.Fits L (μ S L) := by
  intro side
  have hmax : S.sideLeaves L side ≤ max (S.sideLeaves L 0) (max (S.sideLeaves L 1) (S.sideLeaves L 2)) := by
    fin_cases side <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
  calc ((S.blocks side).map fun b ↦ 2 ^ Block.height S L b).sum = S.sideLeaves L side := rfl
    _ ≤ 2 ^ Nat.clog 2 (max (S.sideLeaves L 0) (max (S.sideLeaves L 1) (S.sideLeaves L 2))) :=
        hmax.trans (Nat.le_pow_clog (by norm_num) _)
    _ ≤ 2 ^ μ S L := Nat.pow_le_pow_right (by norm_num) (le_max_of_le_right (le_max_right _ _))

/-- The riders fit the bus's depth. -/
theorem depth_cover : (S.riders L).maxHeight ≤ μ S L :=
  le_max_of_le_right (le_max_left _ _)

/-- The GKR has at least one layer. -/
theorem layers_ne_nil : GrandProduct.layers (μ S L) ≠ [] := by
  intro he
  have hz := GrandProduct.layers_sum (μ S L)
  rw [he, List.sum_nil] at hz
  have : 1 ≤ μ S L := le_max_left _ _
  omega

/-- A column a directly opened table's tuples read is a boundary column. -/
theorem mem_boundaryColumns (hT : ∀ t, (S.table t).WellFormed) (t : Fin S.tables.length) (c : ℕ)
    (hd : S.Direct L t = true) (hr : ∃ I ∈ (S.table t).interactions, Expr.cur c ∈ I.tuple) :
    (t, c) ∈ S.boundaryColumns L := by
  obtain ⟨I, hI, hc⟩ := hr
  have hw : c < (S.table t).air.width := by
    have := ((hT t).2.2.2.2.1 I hI _ hc).2
    simpa only [Expr.colsBelow, decide_eq_true_eq] using this
  simp only [boundaryColumns, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨t, ?_⟩
  simp only [hd, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range, List.any_eq_true,
    List.contains_iff_mem, Prod.mk.injEq, true_and]
  exact ⟨c, ⟨hw, I, hI, hc⟩, rfl⟩

section Certificate

variable {S L k} {width : String → ℕ} (hwf : S.WellFormed L) (hshape : S.BusShape k width)
include hwf

/-- True boundary values and table debts recover the three leaf claims. -/
theorem terminal_prover_preserving (w₀ : Witness K S.tables.length) (α : Fin k → E) (β : E)
    (c : GrandProduct.Claim) (active : Bool) :
    (Retained.extractor w₀ (show Retained.Labels (Witness K S.tables.length) (terminalProtocol S L).tree from
      ⟨leafRelation S L k α β c active, fun vals ↦
        Terminal S L k (output S L k α β c vals active)⟩)).IsProverPreserving
      (terminalProtocol S L).roles := by
  have hT : ∀ t, (S.table t).WellFormed := fun t ↦ (hwf.2.2 t).1
  have hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t := fun t ↦ (hwf.2.2 t).2.1
  have hpad := fun t ↦ (hwf.2.2 t).2.2.2.2.2.2
  refine ⟨?_, fun _ ↦ trivial⟩
  intro vals _ q known
  change Witness K S.tables.length at q
  change q = w₀ ∧ Terminal S L k (output S L k α β c vals active) q at known
  obtain ⟨same, ha, hf, hz, riders, columns, debts⟩ := known
  change q = w₀ ∧ leafRelation S L k α β c active q
  refine ⟨same, ha, hf, ⟨hz, ?_⟩, riders⟩
  intro side
  rw [show GrandProduct.level (μ S L) (μ S L) (S.leaves L k q α β) side = S.leaves L k q α β side from
    funext (GrandProduct.level_full (μ S L) (S.leaves L k q α β) side)]
  have hz' : c.point.length = μ S L := hz
  let z : Vector E (μ S L) := ⟨c.point.toArray, by simpa only [List.size_toArray] using hz'⟩
  have hzl : z.toList = c.point := rfl
  have dec := S.leaf_decomposition k α β L q hT hexec hpad (μ S L) (depth_fits S L) side z vals
    (fun t c' hd hr ↦ columns (t, c') (mem_boundaryColumns S L hT t c' hd hr))
  rw [hzl] at dec
  rw [dec]
  have hd := debts side
  change c.values side - S.publicPart L k α β (μ S L) vals side c.point = _ at hd
  exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)

/-- The shared root and a nonzero nonzero-root give the post-fingerprint relation. -/
theorem roots_prover_preserving (w₀ : Witness K S.tables.length) (α : Fin k → E) (β : E)
    (roots : E × E) (w : Witness K S.tables.length)
    (known : w = w₀ ∧ Retained.input
      (GrandProduct.labels (S.riders L) (μ S L) (fun w ↦ S.leaves L k w α β) (terminalProtocol S L)
        (fun c active ↦ ⟨leafRelation S L k α β c active, fun vals ↦
          Terminal S L k (output S L k α β c vals active)⟩)
        (GrandProduct.layers (μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
        (decide (roots.2 ≠ 0))) w) :
    w = w₀ ∧ afterFingerprint S L k α β w := by
  have hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t := fun t ↦ (hwf.2.2 t).2.1
  have hn := layers_ne_nil S L
  cases he : GrandProduct.layers (μ S L) with
  | nil => exact (hn he).elim
  | cons ρ rest =>
    rw [he] at known
    change w = w₀ ∧ GrandProduct.layerRelation (S.riders L) (μ S L) 0 (fun w ↦ S.leaves L k w α β)
      ⟨[], ![roots.1, roots.1, roots.2]⟩ (decide (roots.2 ≠ 0)) w at known
    obtain ⟨same, ha, hf, hr, _, values⟩ := known
    have hvalue (s : Fin 3) : (![roots.1, roots.1, roots.2] : Fin 3 → E) s =
        GrandProduct.level (μ S L) 0 (S.leaves L k w α β) s 0 := by
      have h := values s
      rwa [GrandProduct.mle_zero] at h
    have h0 := hvalue 0
    have h1 := hvalue 1
    have h2 := hvalue 2
    change roots.1 = _ at h0 h1
    change roots.2 = _ at h2
    have hroot : GrandProduct.level (μ S L) 0 (S.leaves L k w α β) 2 0 ≠ 0 := by
      rw [← h2]
      exact of_decide_eq_true ha
    exact ⟨same, hf, S.nonzero_of_root_ne_zero L k w (μ S L) (depth_fits S L) hexec α β hroot, hr,
      h0.symm.trans h1⟩

/-- Prover messages create no knowledge under the identity maps. -/
theorem prover_preserving (w₀ : Witness K S.tables.length) :
    (extractor S L k w₀).IsProverPreserving (protocol S L k).roles := by
  refine ⟨?_, fun ab ↦ ⟨?_, ?_⟩⟩
  · intro ab impossible
    cases impossible
  · intro roots _ q known
    exact roots_prover_preserving hwf w₀ ab.1 ab.2 roots q known
  · intro roots
    apply GrandProduct.labels_prover_preserving (S.riders L) w₀ (μ S L) (fun w ↦ S.leaves L k w ab.1 ab.2)
      (terminalProtocol S L)
      (fun c active ↦ ⟨leafRelation S L k ab.1 ab.2 c active, fun vals ↦
        Terminal S L k (output S L k ab.1 ab.2 c vals active)⟩)
      (depth_cover S L)
    · intro c good q
      rfl
    · intro c good _
      exact terminal_prover_preserving hwf w₀ ab.1 ab.2 c good
    · rfl
    · simp only [GrandProduct.layers_sum, Nat.zero_add]

include hshape in
/-- The fingerprint draw's bad event: an unbalanced witness whose roots agree. -/
theorem fingerprint_local_le (w₀ : Witness K S.tables.length) :
    Pr{let ab ← ($ᵗ ((Fin k → E) × E))}[
      RoundExtractor.badChallenge (extractor S L k w₀) ab] ≤ overE (max 1 k * 2 ^ μ S L) := by
  classical
  have hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t := fun t ↦ (hwf.2.2 t).2.1
  have inclusion (ab : (Fin k → E) × E)
      (h : RoundExtractor.badChallenge (extractor S L k w₀) ab) :
      S.Shaped L w₀ ∧ ¬ (∀ b ∈ S.buses, S.tuples L w₀ b true = S.tuples L w₀ b false) ∧
        GrandProduct.level (μ S L) 0 (S.leaves L k w₀ ab.1 ab.2) 0 0 =
          GrandProduct.level (μ S L) 0 (S.leaves L k w₀ ab.1 ab.2) 1 0 := by
    change ∃ q, ¬ (q = w₀ ∧ Input S L q) ∧ q = w₀ ∧ afterFingerprint S L k ab.1 ab.2 q at h
    obtain ⟨q, bad, rfl, fits, nonzero, riders, products⟩ := h
    exact ⟨fits, fun balanced ↦ bad ⟨rfl, fits, balanced, nonzero, riders⟩, products⟩
  by_cases hpre : S.Shaped L w₀ ∧ ¬ (∀ b ∈ S.buses, S.tuples L w₀ b true = S.tuples L w₀ b false)
  · exact (prEvent_mono _ _ _ fun ab bad ↦ (inclusion ab bad).2.2).trans
      (S.unbalanced_root_collision_le L k w₀ hshape hexec (μ S L) (depth_fits S L) hpre.2)
  · apply le_trans (prEvent_mono _ _ (fun _ ↦ False) fun ab bad ↦ ?_)
    · simp only [prEvent_false, zero_le]
    · exact hpre ⟨(inclusion ab bad).1, (inclusion ab bad).2.1⟩

include hshape in
/-- Every prefix satisfies the fingerprint, combiner, round and interpolation bounds. -/
theorem locally_bounded (w₀ : Witness K S.tables.length) :
    (extractor S L k w₀).IsLocallyBounded (protocol S L k).roles (challenges S L k) := by
  constructor
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    exact fingerprint_local_le hwf hshape w₀
  · intro ab roots
    apply GrandProduct.labels_locally_bounded (S.riders L) w₀ (μ S L) (fun w ↦ S.leaves L k w ab.1 ab.2)
      (terminalProtocol S L)
      (fun c active ↦ ⟨leafRelation S L k ab.1 ab.2 c active, fun vals ↦
        Terminal S L k (output S L k ab.1 ab.2 c vals active)⟩)
      ⟨PUnit.unit, fun _ ↦ PUnit.unit⟩ (depth_cover S L)
    · intro c good q
      rfl
    · intro c good _ vals
      trivial
    · exact GrandProduct.mem_layers (μ S L)
    · rfl
    · simp only [GrandProduct.layers_sum, Nat.zero_add]

include hshape in
/-- The bus's knowledge certificate on the fixed witness. -/
noncomputable def certificate (w₀ : Witness K S.tables.length) :
    KnowledgeCertificate (protocol S L k).tree (protocol S L k).roles
      (Retained.state w₀ (Input S L)) where
  extractor := extractor S L k w₀
  challenges := challenges S L k
  prover_preserving := prover_preserving hwf w₀
  local_bound := locally_bounded hwf hshape w₀

end Certificate

/-- The fingerprint error plus the GKR's per-layer errors. -/
noncomputable def error : ENNReal :=
  overE (max 1 k * 2 ^ μ S L + GrandProduct.errorNumerator (GrandProduct.layers (μ S L)) 0)

/-- The bus schedule's budget is its error. -/
theorem challenges_budget :
    Retained.Budget (protocol S L k).roles (challenges S L k) (error S L k) := by
  refine ⟨overE (GrandProduct.errorNumerator (GrandProduct.layers (μ S L)) 0), le_of_eq ?_, ?_⟩
  · simp only [challenges, error, overE_add]
  · intro ab roots
    have h := GrandProduct.challenges_budget (terminalProtocol S L)
      ⟨PUnit.unit, fun _ ↦ PUnit.unit⟩ 0 (by intro vals; trivial)
      (GrandProduct.layers (μ S L)) 0 ⟨[], ![roots.1, roots.1, roots.2]⟩
    simpa only [add_zero, challenges] using h

section Soundness

variable {S L k} {width : String → ℕ} (hwf : S.WellFormed L) (hshape : S.BusShape k width)
include hwf hshape

/-- Bus extraction fails against any prover with probability at most the bus error. -/
theorem knowledgeSoundness (w₀ : Witness K S.tables.length)
    (prover : Retained.Strategy (protocol S L k).tree (protocol S L k).roles) :
    Pr{let path ← Retained.play (protocol S L k).roles (challenges S L k) prover}[
      Retained.Failure (extractor S L k w₀) path] ≤ error S L k :=
  Retained.failure_le (extractor S L k w₀) (protocol S L k).roles (challenges S L k)
    (prover_preserving hwf w₀) (locally_bounded hwf hshape w₀) (error S L k)
    (challenges_budget S L k) prover

/-- A witness whose buses do not balance reaches a true bus endpoint with probability at most the
bus error. -/
theorem unbalanced_acceptance_le (w₀ : Witness K S.tables.length)
    (hne : ¬ ∀ b ∈ S.buses, S.tuples L w₀ b true = S.tuples L w₀ b false)
    (prover : Retained.Strategy (protocol S L k).tree (protocol S L k).roles) :
    Pr{let path ← Retained.play (protocol S L k).roles (challenges S L k) prover}[
      ∃ w : ((extractor S L k w₀).terminalState path).Witness,
        ((extractor S L k w₀).terminalState path).holds w] ≤ error S L k := by
  apply le_trans (prEvent_mono _ _ (Retained.Failure (extractor S L k w₀)) ?_)
  · exact knowledgeSoundness hwf hshape w₀ prover
  · rintro path ⟨w, hw⟩
    refine ⟨w, hw, ?_⟩
    change ¬ (_ = w₀ ∧ Input S L _)
    rintro ⟨same, input⟩
    have balanced := input.2.1
    rw [same] at balanced
    exact hne balanced

end Soundness


end CompStark.Tables.Bus
