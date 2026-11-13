/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.ProverRun
public import CompStark.Compiled.WhirProver

/-! The compiled WHIR prover's ideal run, projected to WHIR's opening, is the honest opening at the
drawn coins (`whir_idealRun`). The wire sends each level's first quadratic in parts; their
combination is the honest quadratic of the batched weight by linearity of `honestRound`. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Pcs
open Interaction Interaction.Oracle Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- A cached table reads as its table. -/
theorem TableCache_get {n : ℕ} (table : Whir.Table E n) : (Whir.TableCache.ofTable table).get = table :=
  funext (Whir.TableCache.get_ofTable table)

/-- The scalar rounds with the drawn coordinates: the separate first quadratic, then the folds;
projected with `f` on the first message, the honest rounds into any continuation agreeing at the
final tables with the projection of the boundary. -/
theorem foldRounds_idealRun {src tgt : Protocol} {vars : ℕ}
    (suffix : Presentation (.public .sender (Whir.Quadratic E) fun _ => src))
    (next : Whir.Table E vars → Whir.Table E vars → suffix.Prover)
    (nextP : Whir.Quadratic E → Projection src tgt) :
    (count : ℕ) → (f : Whir.Quadratic E → Whir.Quadratic E) → (first : Whir.Quadratic E) →
    (W T : Whir.Table E (count + vars)) → (state : Transcript.State) →
    (path : (Whir.scalarRounds E count (.public .sender (Whir.Quadratic E) fun _ => src)).tree.ExecutionPath) →
    (final : Transcript.State) → f first = blockHead count W T →
    (whirRounds suffix count).idealRun (separatedProver suffix next count first W T) state =
      some (path, final) →
    ∃ (rs : Fin count → E) (Wf Tf : Whir.Table E vars) (reached : Transcript.State)
      (tailPath : (Protocol.public .sender (Whir.Quadratic E) fun _ => src).tree.ExecutionPath),
      suffix.idealRun (next Wf Tf) reached = some (tailPath, final) ∧
      ∀ k : Whir.Table E vars → Whir.Table E vars → tgt.tree.ExecutionPath,
        k Wf Tf = (nextP tailPath.1).path tailPath.2 →
          (foldProjection f nextP count).path path = Pcs.honestRounds tgt count W T rs k
  | 0, _, _, W, T, state, path, final, _, h =>
      ⟨Fin.elim0, Whir.castTable (Nat.zero_add vars) W, Whir.castTable (Nat.zero_add vars) T, state,
        path, h, fun _ hk => hk.symm⟩
  | count + 1, f, first, W, T, state, path, final, hf, h => by
      let r := (scalarDraw.run (Transcript.replay state (quadraticEvents first))).1
      let W' := (Whir.TableCache.ofTable (Whir.foldMessageOne W r)).get
      let T' := (Whir.TableCache.ofTable (Whir.foldMessageOne T r)).get
      have unfolded : (whirRounds suffix (count + 1)).idealRun
          (separatedProver suffix next (count + 1) first W T) state =
          Option.map (fun result => (⟨first, result.1⟩, result.2))
            (Option.map (fun result => (⟨r, result.1⟩, result.2))
              ((whirRounds suffix count).idealRun (separatedProver suffix next count (blockHead count W' T') W' T')
                (scalarDraw.run (Transcript.replay state (quadraticEvents first))).2)) := rfl
      rw [unfolded] at h
      obtain ⟨middle, hmiddle, pair⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hpath, hfinal⟩ := Prod.mk.inj pair
      subst hpath hfinal
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hmiddle
      obtain ⟨rs, Wf, Tf, reached, tailPath, hrun, hproj⟩ :=
        foldRounds_idealRun suffix next nextP count id (blockHead count W' T') W' T' _ tail.1 tail.2 rfl
          (by rw [htail])
      refine ⟨Fin.cons r rs, Wf, Tf, reached, tailPath, hrun, fun k hk => ?_⟩
      have raw : Pcs.honestRounds tgt (count + 1) W T (Fin.cons (α := fun _ => E) r rs) k =
          ⟨honestRound W T, Fin.cons (α := fun _ => E) r rs 0,
            Pcs.honestRounds tgt count (Whir.foldMessageOne W (Fin.cons (α := fun _ => E) r rs 0))
              (Whir.foldMessageOne T (Fin.cons (α := fun _ => E) r rs 0))
              (Fin.tail (Fin.cons (α := fun _ => E) r rs)) k⟩ := rfl
      rw [raw, Fin.cons_zero, Fin.tail_cons, ← TableCache_get (Whir.foldMessageOne W r),
        ← TableCache_get (Whir.foldMessageOne T r), ← hproj k hk]
      change (⟨f first, r, (foldProjection id nextP count).path tail.1⟩ :
        (Whir.scalarRounds E (count + 1) tgt).tree.ExecutionPath) = _
      rw [hf]
      rfl

/-- The closing scalar rounds with the drawn coordinates, projected with `g` on the first message,
are the honest closing rounds. -/
theorem scalarRounds_idealRun :
    (count : ℕ) → (g : Whir.Quadratic E → Whir.Quadratic E) → (first : Whir.Quadratic E) →
    (W T : Whir.Table E (count + 0)) → (state : Transcript.State) →
    (path : (Whir.scalarRounds E count .done).tree.ExecutionPath) → (final : Transcript.State) →
    g first = blockHead count W T →
    (whirRounds .done count).idealRun
      (separatedProver (vars := 0) .done (fun _ _ => PUnit.unit) count first W T) state = some (path, final) →
    ∃ rs : Fin count → E, (scalarProjection g count).path path =
      Pcs.honestRounds .done (vars := 0) count W T rs (fun _ _ => PUnit.unit)
  | 0, _, _, _, _, _, _, _, _, _ => ⟨Fin.elim0, rfl⟩
  | count + 1, g, first, W, T, state, path, final, hg, h => by
      let r := (scalarDraw.run (Transcript.replay state (quadraticEvents first))).1
      let W' := (Whir.TableCache.ofTable (Whir.foldMessageOne W r)).get
      let T' := (Whir.TableCache.ofTable (Whir.foldMessageOne T r)).get
      have unfolded : (whirRounds .done (count + 1)).idealRun
          (separatedProver (vars := 0) .done (fun _ _ => PUnit.unit) (count + 1) first W T) state =
          Option.map (fun result => (⟨first, result.1⟩, result.2))
            (Option.map (fun result => (⟨r, result.1⟩, result.2))
              ((whirRounds .done count).idealRun
                (separatedProver (vars := 0) .done (fun _ _ => PUnit.unit) count (blockHead count W' T') W' T')
                (scalarDraw.run (Transcript.replay state (quadraticEvents first))).2)) := rfl
      rw [unfolded] at h
      obtain ⟨middle, hmiddle, pair⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hpath, hfinal⟩ := Prod.mk.inj pair
      subst hpath hfinal
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hmiddle
      obtain ⟨rs, hproj⟩ := scalarRounds_idealRun count id (blockHead count W' T') W' T' _ tail.1 tail.2 rfl
        (by rw [htail])
      refine ⟨Fin.cons r rs, ?_⟩
      have raw : Pcs.honestRounds .done (vars := 0) (count + 1) W T (Fin.cons (α := fun _ => E) r rs)
          (fun _ _ => PUnit.unit) =
          ⟨honestRound W T, Fin.cons (α := fun _ => E) r rs 0,
            Pcs.honestRounds .done (vars := 0) count (Whir.foldMessageOne W (Fin.cons (α := fun _ => E) r rs 0))
              (Whir.foldMessageOne T (Fin.cons (α := fun _ => E) r rs 0))
              (Fin.tail (Fin.cons (α := fun _ => E) r rs)) (fun _ _ => PUnit.unit)⟩ := rfl
      rw [raw, Fin.cons_zero, Fin.tail_cons, ← TableCache_get (Whir.foldMessageOne W r),
        ← TableCache_get (Whir.foldMessageOne T r), ← hproj]
      change (⟨g first, r, (scalarProjection id count).path tail.1⟩ :
        (Whir.scalarRounds E (count + 1) .done).tree.ExecutionPath) = _
      rw [hg]
      rfl

/-- Batching a list after a head claim is the head plus the scaled batch of the rest. -/
theorem batch_cons_weight {n : ℕ} (c : Whir.Claim E n) (cs : List (Whir.Claim E n)) (r : E) :
    (Whir.batch (c :: cs) r).weight = fun u => 1 * c.weight u + r * (Whir.batch cs r).weight u := by
  have shift : ∀ (cs : List (Whir.Claim E n)) (k : ℕ) (u : Whir.Cube n),
      ((cs.zipIdx (k + 1)).map fun p => r ^ p.2 * p.1.weight u).sum =
        r * ((cs.zipIdx k).map fun p => r ^ p.2 * p.1.weight u).sum := by
    intro cs
    induction cs with
    | nil => intro k u; simp only [List.zipIdx_nil, List.map_nil, List.sum_nil, mul_zero]
    | cons d ds ih =>
        intro k u
        simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1), pow_succ]
        ring
  funext u
  simp only [Whir.batch, List.zipIdx_cons, List.map_cons, List.sum_cons, pow_zero, shift cs 0 u]

/-- A level's first quadratic is linear in the weight. -/
theorem blockHead_add (count : ℕ) {vars : ℕ} (a b : E) (left right table : Whir.Table E (count + vars)) :
    blockHead count (fun u => a * left u + b * right u) table =
      (a * (blockHead count left table).1 + b * (blockHead count right table).1,
        fun i => a * (blockHead count left table).2 i + b * (blockHead count right table).2 i) := by
  cases count with
  | zero =>
      change ((0 : E), fun _ => (0 : E)) = (a * 0 + b * 0, fun _ => a * 0 + b * 0)
      simp only [mul_zero, add_zero]
  | succ count => exact honestRound_linear a b left right table

/-- The last boundary's combined quadratic is the batched weight's. -/
theorem combineLast_blockHead (count : ℕ) {vars : ℕ} (c : Whir.Claim E (count + vars))
    (cs : List (Whir.Claim E (count + vars))) (table : Whir.Table E (count + vars)) (lam : E) :
    combineLastQuadratic (blockHead count c.weight table) (blockHead count (Whir.batch cs lam).weight table) lam =
      blockHead count (Whir.batch (c :: cs) lam).weight table := by
  rw [batch_cons_weight, blockHead_add]
  simp only [combineLastQuadratic, one_mul]

/-- A nonlast boundary's combined quadratic is the batched weight's. -/
theorem combine_blockHead (count : ℕ) {vars : ℕ} (c d : Whir.Claim E (count + vars))
    (cs : List (Whir.Claim E (count + vars))) (table : Whir.Table E (count + vars)) (lam : E) :
    combineQuadratic (blockHead count c.weight table) (blockHead count d.weight table)
      (blockHead count (Whir.batch cs lam).weight table) lam =
      blockHead count (Whir.batch (c :: d :: cs) lam).weight table := by
  rw [batch_cons_weight, batch_cons_weight]
  rw [show (fun u => 1 * c.weight u + lam * (fun u => 1 * d.weight u + lam * (Whir.batch cs lam).weight u) u) =
      fun u => 1 * c.weight u + lam * (fun u => 1 * d.weight u + lam * (Whir.batch cs lam).weight u) u from rfl,
    blockHead_add, blockHead_add]
  simp only [combineQuadratic, Prod.mk.injEq]
  exact ⟨by ring, funext fun _ => by ring⟩

/-- A level's combined boundary quadratic is the batched weight's. -/
theorem levelHead_combine {t : ℕ} (rest : EvaluatedSchedule t) (c d : Whir.Claim E t)
    (cs : List (Whir.Claim E t)) (table : Whir.Table E t) (lam : E) :
    combineQuadratic (levelHead rest.schedule c.weight table) (levelHead rest.schedule d.weight table)
      (levelHead rest.schedule (Whir.batch cs lam).weight table) lam =
      levelHead rest.schedule (Whir.batch (c :: d :: cs) lam).weight table := by
  cases rest <;> exact combine_blockHead _ _ _ _ _ _

/-- The honest final claims are the residual claim and the cached query claims. -/
theorem finalClaims_eq {tail queries : ℕ} (enc : EvaluatedEncoding tail) (weight table : Whir.Table E tail)
    (xs : Fin queries → enc.encoding.Columns) :
    finalClaims enc.encoding (algebraMap K E) weight table xs =
      ⟨weight, dot weight table⟩ :: queryClaims enc table xs := by
  rw [queryClaims_eq]
  rfl

/-- The honest next claims are the residual, the OOD claim and the cached query claims. -/
theorem nextClaims_eq {tail queries : ℕ} (enc : EvaluatedEncoding tail) (weight table : Whir.Table E tail)
    (z : Fin tail → E) (answer : E) (xs : Fin queries → enc.encoding.Columns) :
    Whir.nextClaims enc.encoding (algebraMap K E) ⟨weight, dot weight table⟩ z answer xs
        (enc.encoding.encode (algebraMap K E) table) =
      ⟨weight, dot weight table⟩ :: ⟨Whir.eqWeight z, answer⟩ :: queryClaims enc table xs := by
  rw [queryClaims_eq]
  rfl

/-- The WHIR wire prover's ideal run, projected with a combination that rebuilds the first
quadratic of the batched weight, is the honest opening at the drawn coins. -/
theorem whirWire_idealRun : {n : ℕ} → (schedule : EvaluatedSchedule n) → (table : Whir.Table E n) →
    (claims : List (Whir.Claim E n)) → (introduction : E → Whir.Table E n) →
    (combine : E → Whir.Quadratic E → Whir.Quadratic E) →
    (∀ lam, combine lam (levelHead schedule.schedule (introduction lam) table) =
      levelHead schedule.schedule (Whir.batch claims lam).weight table) →
    (state : Transcript.State) → (path : (whirWireProtocol schedule.schedule).tree.ExecutionPath) →
    (final : Transcript.State) →
    (whirWirePresentation schedule.schedule).idealRun (whirWireProver schedule table claims introduction) state =
      some (path, final) →
    ∃ coins, (whirProjection schedule.schedule combine).path path =
      honestWhir (algebraMap K E) schedule.schedule table claims coins
  | _, .last lanes tail enc queries, table, claims, introduction, combine, hcombine, state, path, final, h => by
      let lam := (scalarDraw.run state).1
      erw [Presentation.idealRun_challenge] at h
      obtain ⟨rounds, hrounds, pair⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hpath, hfinal⟩ := Prod.mk.inj pair
      subst hpath hfinal
      obtain ⟨rs, Wf, Tf, reached, boundary, hboundary, hproj⟩ := foldRounds_idealRun _ _
        (whirBoundaryProjection (.last lanes tail enc.encoding queries)) lanes (combine lam) _ _ _ _ rounds.1 rounds.2 (hcombine lam) hrounds
      erw [Presentation.idealRun_sender] at hboundary
      obtain ⟨b1, hb1, pair⟩ := Option.map_eq_some_iff.mp hboundary
      obtain ⟨hb, -⟩ := Prod.mk.inj pair
      subst hb
      erw [Presentation.idealRun_sender] at hb1
      obtain ⟨b2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb1
      erw [Presentation.idealRun_grind] at hb2
      obtain ⟨nonce, -, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      erw [Presentation.idealRun_challenge] at hb3
      obtain ⟨b4, hb4, rfl⟩ := Option.map_eq_some_iff.mp hb3
      erw [Presentation.idealRun_challenge] at hb4
      obtain ⟨b5, hb5, rfl⟩ := Option.map_eq_some_iff.mp hb4
      let residual := blockHead (vars := 0) tail Wf Tf
      let s2 := Transcript.replay (Transcript.replay reached (quadraticEvents residual))
        (fieldEvents fun i : Fin (2 ^ tail) => Tf (fun bit => i.val.testBit bit.val))
      let drawn := (queryDraw queries (tail + enc.encoding.rate)).run (Transcript.grindCheck s2 17 nonce).2
      let xs := drawn.1
      let finalLam := (scalarDraw.run drawn.2).1
      have hg := combineLast_blockHead tail (vars := 0) ⟨Wf, dot Wf Tf⟩ (queryClaims enc Tf xs) Tf finalLam
      obtain ⟨rs2, hproj2⟩ := scalarRounds_idealRun tail (fun query => combineLastQuadratic residual query finalLam)
        _ _ Tf _ b5.1 b5.2 hg hb5
      refine ⟨(lam, rs, xs, finalLam, rs2), ?_⟩
      have hk := hproj (fun weight folded =>
          let closing := Whir.batch (finalClaims enc.encoding (algebraMap K E) weight folded xs) finalLam
          ⟨folded, xs, finalLam, Pcs.honestRounds .done (vars := 0) tail closing.weight folded rs2
            (fun _ _ => PUnit.unit)⟩) (by
        change (⟨Tf, xs, finalLam, Pcs.honestRounds .done (vars := 0) tail
          (Whir.batch (finalClaims enc.encoding (algebraMap K E) Wf Tf xs) finalLam).weight Tf rs2
            (fun _ _ => PUnit.unit)⟩ : (Whir.transition E (.last lanes tail enc.encoding queries)).tree.ExecutionPath) =
          ⟨Tf, xs, finalLam, (scalarProjection (fun query => combineLastQuadratic residual query finalLam) tail).path b5.1⟩
        rw [hproj2, finalClaims_eq])
      change (⟨lam, (foldProjection (combine lam) (whirBoundaryProjection (.last lanes tail enc.encoding queries))
        lanes).path rounds.1⟩ : (Whir.opening E (.last lanes tail enc.encoding queries)).tree.ExecutionPath) = _
      rw [hk]
      rfl
  | _, @EvaluatedSchedule.more tail lanes enc queries rest, table, claims, introduction, combine, hcombine,
      state, path, final, h => by
      let lam := (scalarDraw.run state).1
      erw [Presentation.idealRun_challenge] at h
      obtain ⟨rounds, hrounds, pair⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hpath, hfinal⟩ := Prod.mk.inj pair
      subst hpath hfinal
      obtain ⟨rs, Wf, Tf, reached, boundary, hboundary, hproj⟩ := foldRounds_idealRun _ _
        (whirBoundaryProjection (.more lanes enc.encoding queries rest.schedule)) lanes (combine lam) _ _ _ _
        rounds.1 rounds.2 (hcombine lam) hrounds
      erw [Presentation.idealRun_sender] at hboundary
      obtain ⟨b1, hb1, pair⟩ := Option.map_eq_some_iff.mp hboundary
      obtain ⟨hb, -⟩ := Prod.mk.inj pair
      subst hb
      erw [Presentation.idealRun_merkle] at hb1
      obtain ⟨b2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb1
      erw [Presentation.idealRun_challenge] at hb2
      obtain ⟨b3, hb3, rfl⟩ := Option.map_eq_some_iff.mp hb2
      erw [Presentation.idealRun_sender] at hb3
      obtain ⟨b4, hb4, rfl⟩ := Option.map_eq_some_iff.mp hb3
      erw [Presentation.idealRun_sender] at hb4
      obtain ⟨b5, hb5, rfl⟩ := Option.map_eq_some_iff.mp hb4
      erw [Presentation.idealRun_grind] at hb5
      obtain ⟨nonce, -, hb6⟩ := Option.bind_eq_some_iff.mp hb5
      erw [Presentation.idealRun_challenge] at hb6
      obtain ⟨b7, hb7, rfl⟩ := Option.map_eq_some_iff.mp hb6
      let residual := levelHead rest.schedule Wf Tf
      let word : Whir.oracleMessage E rest.schedule := wordOfRows (headRowsExtension rest Tf)
      let s1 := Transcript.replay (Transcript.replay reached (quadraticEvents residual))
        (Transcript.digestEvents (Commit.root (extensionLayout rest.schedule).height fun i =>
          Commit.restoreLeaf (extensionLayout rest.schedule).leafWords (extensionRows word i)))
      let z := ((vectorDraw tail).run s1).1
      let answer := Whir.mle (F := E) Tf z
      let ood := levelHead rest.schedule (Whir.eqWeight z) Tf
      let s2 := Transcript.replay (Transcript.replay ((vectorDraw tail).run s1).2 (fieldEvents ![answer]))
        (quadraticEvents ood)
      let xs := ((queryDraw queries (tail + enc.encoding.rate)).run (Transcript.grindCheck s2 17 nonce).2).1
      let claims' : List (Whir.Claim E tail) :=
        ⟨Wf, dot Wf Tf⟩ :: ⟨Whir.eqWeight z, answer⟩ :: queryClaims enc Tf xs
      have hcombine' : ∀ nextLam, combineQuadratic residual ood
          (levelHead rest.schedule (Whir.batch (queryClaims enc Tf xs) nextLam).weight Tf) nextLam =
          levelHead rest.schedule (Whir.batch claims' nextLam).weight Tf := by
        intro nextLam
        exact levelHead_combine rest ⟨Wf, dot Wf Tf⟩ ⟨Whir.eqWeight z, answer⟩ (queryClaims enc Tf xs) Tf nextLam
      obtain ⟨coins, hrest⟩ := whirWire_idealRun rest Tf claims'
        (fun nextLam => (Whir.batch (queryClaims enc Tf xs) nextLam).weight)
        (fun nextLam query => combineQuadratic residual ood query nextLam) hcombine' _ b7.1 b7.2 hb7
      refine ⟨(lam, rs, z, xs, coins), ?_⟩
      have hk := hproj (fun weight folded =>
          let answer := Whir.mle folded z
          let next := Whir.nextClaims enc.encoding (algebraMap K E) ⟨weight, dot weight folded⟩ z answer xs
            (enc.encoding.encode (algebraMap K E) folded)
          ⟨encodeLevel (algebraMap K E) rest.schedule folded, z, answer, xs,
            honestWhir (algebraMap K E) rest.schedule folded next coins⟩) (by
        change (⟨encodeLevel (algebraMap K E) rest.schedule Tf, z, answer, xs,
          honestWhir (algebraMap K E) rest.schedule Tf
            (Whir.nextClaims enc.encoding (algebraMap K E) ⟨Wf, dot Wf Tf⟩ z answer xs
              (enc.encoding.encode (algebraMap K E) Tf)) coins⟩ :
            (Whir.transition E (.more lanes enc.encoding queries rest.schedule)).tree.ExecutionPath) =
          ⟨word, z, answer, xs, (whirProjection rest.schedule
            (fun nextLam query => combineQuadratic residual ood query nextLam)).path b7.1⟩
        rw [hrest, nextClaims_eq, ← wordOfRows_extension])
      change (⟨lam, (foldProjection (combine lam)
        (whirBoundaryProjection (.more lanes enc.encoding queries rest.schedule)) lanes).path rounds.1⟩ :
          (Whir.opening E (.more lanes enc.encoding queries rest.schedule)).tree.ExecutionPath) = _
      rw [hk]
      rfl

/-- The WHIR prover's ideal run is the honest opening at the drawn coins. -/
theorem whir_idealRun {n : ℕ} (schedule : EvaluatedSchedule n) (table : Whir.Table E n)
    (claims : List (Whir.Claim E n)) (state : Transcript.State)
    (path : (Whir.opening E schedule.schedule).tree.ExecutionPath) (final : Transcript.State)
    (h : (whirPresentation schedule.schedule).idealRun (whirProver schedule table claims) state =
      some (path, final)) :
    ∃ coins, path = honestWhir (algebraMap K E) schedule.schedule table claims coins := by
  obtain ⟨wire, hwire, pair⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hpath, -⟩ := Prod.mk.inj pair
  subst hpath
  exact whirWire_idealRun schedule table claims _ (fun _ => id) (fun _ => rfl) state wire.1 wire.2 hwire

end CompStark.Compiled
