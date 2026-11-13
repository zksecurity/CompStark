/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Prover
public import CompStark.Pcs.HonestWhir
public import CompStark.Pcs.HonestRoundFast
public import CompStark.Pcs.WordEncoding

/-! The honest prover of WHIR's production presentation: each fold sends its separate first
quadratic, then folds the full accumulated weight at the drawn coordinate; a boundary sends the
residual lookahead, commits the next encoded word, answers the out-of-domain point and sends its
introduction; the last level sends the plaintext table. Tables are materialized after every fold. -/

set_option Elab.async false
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Pcs
open Interaction Interaction.Oracle Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The first quadratic of a block; an empty block has no transmitted first message. -/
def blockHead {vars : ℕ} : (count : ℕ) → Whir.Table E (count + vars) →
    Whir.Table E (count + vars) → Whir.Quadratic E
  | 0, _, _ => (0, fun _ => 0)
  | _ + 1, weight, table => honestRound weight table

/-- A level's first quadratic. -/
def levelHead : {n : ℕ} → (schedule : Whir.Schedule K n) →
    Whir.Table E n → Whir.Table E n → Whir.Quadratic E
  | _, .last lanes _ _ _, weight, table => blockHead lanes weight table
  | _, .more lanes _ _ _, weight, table => blockHead lanes weight table

/-- Honest encoding-query claims, in sampled order including repeated positions. -/
def encodingClaims {tail queries : ℕ} (enc : Whir.Encoding K tail)
    (table : Whir.Table E tail) (xs : Fin queries → enc.Columns) : List (Whir.Claim E tail) :=
  List.ofFn fun q => ⟨fun u => ofK (enc.weight (xs q) u), enc.encode (algebraMap K E) table (xs q)⟩

/-- The query claims with each weight from its certified evaluator, computed once. -/
def queryClaims {tail queries : ℕ} (enc : EvaluatedEncoding tail) (table : Whir.Table E tail)
    (xs : Fin queries → enc.encoding.Columns) : List (Whir.Claim E tail) :=
  List.ofFn fun q =>
    let cache := Whir.TableCache.ofTable (enc.query (xs q)).table
    ⟨cache.get, dot cache.get table⟩

/-- The cached query claims are the encoding-query claims. -/
theorem queryClaims_eq {tail queries : ℕ} (enc : EvaluatedEncoding tail) (table : Whir.Table E tail)
    (xs : Fin queries → enc.encoding.Columns) :
    queryClaims enc table xs = encodingClaims enc.encoding table xs := by
  have weight (q : Fin queries) :
      (Whir.TableCache.ofTable (enc.query (xs q)).table).get = fun u => ofK (enc.encoding.weight (xs q) u) := by
    funext u
    rw [Whir.TableCache.get_ofTable, enc.query_table]
  unfold queryClaims encodingClaims
  congr 1
  funext q
  simp only [weight]
  rfl

/-- The scalar rounds: send the separate first quadratic, then fold the accumulated weight and the
table at the drawn coordinate. -/
def separatedProver {tail : Protocol} (suffix : Presentation tail) {vars : ℕ}
    (next : Whir.Table E vars → Whir.Table E vars → suffix.Prover) :
    (count : ℕ) → Whir.Quadratic E → Whir.Table E (count + vars) → Whir.Table E (count + vars) →
      (whirRounds suffix count).Prover
  | 0, _, weight, table =>
      next (Whir.castTable (Nat.zero_add vars) weight) (Whir.castTable (Nat.zero_add vars) table)
  | count + 1, first, weight, table => fun _ => ⟨first, fun _ r =>
      let weightCache := Whir.TableCache.ofTable (Whir.foldMessageOne weight r)
      let tableCache := Whir.TableCache.ofTable (Whir.foldMessageOne table r)
      separatedProver suffix next count (blockHead count weightCache.get tableCache.get)
        weightCache.get tableCache.get⟩

/-- The leaf rows of the initial base-field word: each column's row values in reversed order. -/
def baseRows {lanes columns : ℕ} (word : Whir.MaskedWord K lanes columns) (column : ℕ) : List K :=
  if h : column < columns then
    match word ⟨column, h⟩ with
    | some values => List.ofFn fun j : Fin (2 ^ lanes) =>
        values (Pcs.mask lanes ⟨2 ^ lanes - 1 - j.val, by omega⟩)
    | none => []
  else []

/-- The leaf rows of a later extension-field word: each row value as its three limbs. -/
def extensionRows {lanes columns : ℕ} (word : Whir.MaskedWord E lanes columns) (column : ℕ) : List K :=
  if h : column < columns then
    match word ⟨column, h⟩ with
    | some values => List.ofFn fun j : Fin (3 * 2 ^ lanes) =>
        (values (Pcs.mask lanes ⟨j.val / 3, by omega⟩)).limb ⟨j.val % 3, by omega⟩
    | none => []
  else []

/-- The production boundary of the last level after its folds. -/
def lastBoundary (tail : ℕ) (enc : Whir.Encoding K tail) (queries : ℕ) :
    Presentation (.public .sender (Whir.Quadratic E) fun _ =>
      Compiled.whirWireTransition (.last 0 tail enc queries)) :=
  .sender quadraticEvents fun _ =>
    .sender (fun table => fieldEvents fun i : Fin (2 ^ tail) =>
      table (fun bit => i.val.testBit bit.val)) (fun _ =>
        .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + enc.rate))
          (.challenge id (fun _ => rfl) scalarDraw (whirRounds .done tail))))

/-- The production boundary of a nonlast level after its folds. -/
def moreBoundary {tail : ℕ} (enc : Whir.Encoding K tail) (queries : ℕ) {n : ℕ}
    (rest : Whir.Schedule K tail) :
    Presentation (.public .sender (Whir.Quadratic E) fun _ =>
      Compiled.whirWireTransition (.more n enc queries rest)) :=
  .sender quadraticEvents fun _ => .merkle (extensionLayout rest)
    (.challenge id (fun _ => rfl) (vectorDraw tail)
      (.sender (fun value => fieldEvents ![value]) (fun _ =>
        .sender quadraticEvents fun _ =>
          .grind 17 (.challenge id (fun _ => rfl) (queryDraw queries (tail + enc.rate))
            (whirWirePresentation rest)))))

/-- A masked word read off encoded rows. -/
def wordOfRows {R : Type} [Zero R] {lanes columns : ℕ} (rows : Vector (Array R) (2 ^ lanes)) :
    Whir.MaskedWord R lanes columns :=
  fun x => some fun row => rows[Pcs.cubeIndex lanes row].getD x.val 0

/-- The encoded rows of an evaluated schedule's head level over the base field. -/
def headRowsBase {n : ℕ} : (schedule : EvaluatedSchedule n) → Whir.Table K n →
    Vector (Array K) (2 ^ schedule.schedule.lanes)
  | .last _ _ enc _, table => enc.encodeRowsBase table
  | .more _ enc _ _, table => enc.encodeRowsBase table

/-- The encoded rows of an evaluated schedule's head level over the extension field. -/
def headRowsExtension {n : ℕ} : (schedule : EvaluatedSchedule n) → Whir.Table E n →
    Vector (Array E) (2 ^ schedule.schedule.lanes)
  | .last _ _ enc _, table => enc.encodeRowsExtension table
  | .more _ enc _ _, table => enc.encodeRowsExtension table

/-- The base-field head word read off its encoded rows is the protocol's. -/
theorem wordOfRows_base {n : ℕ} (schedule : EvaluatedSchedule n) (table : Whir.Table K n) :
    (wordOfRows (headRowsBase schedule table) : Whir.oracleMessage K schedule.schedule) =
      encodeLevel (RingHom.id K) schedule.schedule table := by
  cases schedule with
  | last lanes tail enc queries =>
    funext x
    change some (fun row => (enc.encodeRowsBase table)[Pcs.cubeIndex lanes row].getD x.val 0) =
      some (enc.encoding.interleave (RingHom.id K) table x)
    congr 1
    funext row
    refine (EvaluatedEncoding.encodeRowsBase_eq enc table (Pcs.cubeIndex lanes row) x).trans ?_
    rw [mask_cubeIndex]
    rfl
  | more lanes enc queries rest =>
    funext x
    change some (fun row => (enc.encodeRowsBase table)[Pcs.cubeIndex lanes row].getD x.val 0) =
      some (enc.encoding.interleave (RingHom.id K) table x)
    congr 1
    funext row
    refine (EvaluatedEncoding.encodeRowsBase_eq enc table (Pcs.cubeIndex lanes row) x).trans ?_
    rw [mask_cubeIndex]
    rfl

/-- The extension-field head word read off its encoded rows is the protocol's. -/
theorem wordOfRows_extension {n : ℕ} (schedule : EvaluatedSchedule n) (table : Whir.Table E n) :
    (wordOfRows (headRowsExtension schedule table) : Whir.oracleMessage E schedule.schedule) =
      encodeLevel (algebraMap K E) schedule.schedule table := by
  cases schedule with
  | last lanes tail enc queries =>
    funext x
    change some (fun row => (enc.encodeRowsExtension table)[Pcs.cubeIndex lanes row].getD x.val 0) =
      some (enc.encoding.interleave (algebraMap K E) table x)
    congr 1
    funext row
    refine (EvaluatedEncoding.encodeRowsExtension_eq enc table (Pcs.cubeIndex lanes row) x).trans ?_
    rw [mask_cubeIndex]
    rfl
  | more lanes enc queries rest =>
    funext x
    change some (fun row => (enc.encodeRowsExtension table)[Pcs.cubeIndex lanes row].getD x.val 0) =
      some (enc.encoding.interleave (algebraMap K E) table x)
    congr 1
    funext row
    refine (EvaluatedEncoding.encodeRowsExtension_eq enc table (Pcs.cubeIndex lanes row) x).trans ?_
    rw [mask_cubeIndex]
    rfl

/-- The honest prover of a level and every later level, from the table, the claims and the level's
separate first introduction. -/
def whirWireProver : {n : ℕ} → (schedule : EvaluatedSchedule n) → Whir.Table E n →
    List (Whir.Claim E n) → (E → Whir.Table E n) → (whirWirePresentation schedule.schedule).Prover
  | _, .last lanes tail enc queries, table, claims, introduction => fun _ lambda =>
      let batched := Whir.batch claims lambda
      separatedProver (lastBoundary tail enc.encoding queries) (fun weight folded => fun _ =>
          ⟨blockHead (vars := 0) tail weight folded, fun _ =>
            ⟨folded, fun _ xs => fun _ finalLambda =>
              let claims := queryClaims enc folded xs
              let closing := Whir.batch (⟨weight, dot weight folded⟩ :: claims) finalLambda
              let query := Whir.batch claims finalLambda
              separatedProver (vars := 0) .done (fun _ _ => PUnit.unit) tail
                (blockHead (vars := 0) tail query.weight folded) closing.weight folded⟩⟩)
        lanes (blockHead lanes (introduction lambda) table) batched.weight table
  | _, .more lanes enc queries rest, table, claims, introduction => fun _ lambda =>
      let batched := Whir.batch claims lambda
      separatedProver (moreBoundary enc.encoding queries (n := lanes) rest.schedule)
        (fun weight folded => fun _ =>
          ⟨levelHead rest.schedule weight folded, fun _ =>
            let word : Whir.oracleMessage E rest.schedule := wordOfRows (headRowsExtension rest folded)
            (word, extensionRows word, fun _ z =>
              let answer := Whir.mle (F := E) folded z
              fun _ => ⟨answer, fun _ => ⟨levelHead rest.schedule (Whir.eqWeight z) folded, fun _ xs =>
                let claims := queryClaims enc folded xs
                whirWireProver rest folded
                  (⟨weight, dot weight folded⟩ :: ⟨Whir.eqWeight z, answer⟩ :: claims)
                  (fun lambda => (Whir.batch claims lambda).weight)⟩⟩)⟩)
        lanes (blockHead lanes (introduction lambda) table) batched.weight table

/-- The honest prover of WHIR's presentation for a table and its claims. -/
def whirProver {n : ℕ} (schedule : EvaluatedSchedule n) (table : Whir.Table E n)
    (claims : List (Whir.Claim E n)) : (whirPresentation schedule.schedule).Prover :=
  whirWireProver schedule table claims fun lambda => (Whir.batch claims lambda).weight

end CompStark.Compiled
