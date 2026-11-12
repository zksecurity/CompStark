/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Acceptance

/-! The compiled composed system's Fiat–Shamir transcript: the duplex seeded with the parameters'
initialization vector and statement, the deterministic challenge table it replays, compiled
acceptance (the opened verifier and the grinding checks), and framing of every move's encoding. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security OracleComp
open StandardBcs StateRestoration

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

/-- The duplex seeded with the initialization vector and the statement. -/
def initialState (params : Parameters S L k M) : Transcript.State :=
  Transcript.seedDigests params.iv params.statement

/-- The deterministic challenge table replayed from a given initial duplex state. -/
def challengeTableFrom (params : Parameters S L k M) (initial : Transcript.State) :
    StateRestoration.Table PUnit PUnit (fun _ => StandardBcs.compiledCoin Commit.Digest (coin params)) := fun key =>
  let observer := (presentation params).observer
  WireObserver.decode _ observer key.2
    (Transcript.replay initial (WireObserver.encode (fun _ => observer) key).2)

/-- The challenge table from the seeded duplex. -/
def challengeTable (params : Parameters S L k M) :
    StateRestoration.Table PUnit PUnit (fun _ => StandardBcs.compiledCoin Commit.Digest (coin params)) :=
  challengeTableFrom params (initialState params)

/-- Compiled acceptance: the opened verifier and the grinding checks. -/
def accept (hash : ByteArray → Commit.Digest) (params : Parameters S L k M) (proof : Proof params) :
    Prop :=
  openingAccept hash params proof ∧ (presentation params).grindingChecks proof.2.1 (initialState params)

/-- Duplex replay agrees with the challenge table the verifier uses. -/
theorem duplex_consistent (params : Parameters S L k M)
    (messages : Messages PUnit (StandardBcs.compiledCoin Commit.Digest (coin params))) :
    CorrelationIntractable.Consistent (StandardBcs.compiledCoin Commit.Digest (coin params))
      (StateRestoration.Table.fibre (challengeTable params) PUnit.unit)
      (WireObserver.execute _ (presentation params).observer (initialState params) messages) :=
  WireObserver.execute_consistent _ _ _ _

/-- An injective re-encoding of a prefix-free encoding is prefix free. -/
theorem prefixFree_comp {A B : Type} (encode : B → List Transcript.Event) (f : A → B)
    (injective : Function.Injective f) (free : HashChain.PrefixFree encode) :
    HashChain.PrefixFree (fun a => encode (f a)) := by
  intro a b rest rest' equal
  obtain ⟨same, rest⟩ := free (f a) (f b) rest rest' equal
  exact ⟨injective same, rest⟩

/-- The transmitted values' family determines them. -/
theorem valuesFamily_injective : Function.Injective (valuesFamily S L) := by
  intro a b equal
  funext t i
  obtain ⟨t, h⟩ := t
  have := congrFun (congrFun equal t) (Fin.cast (by simp only [valuesWidth, h, ↓reduceIte]) i)
  simpa only [valuesFamily, h, ↓reduceDIte, Fin.cast_cast, Fin.cast_eq_self] using this

variable (S L k) in
/-- The bus's and the table sumcheck's encodings are prefix free and their draws squeeze. -/
theorem busTable_framed : ((busPresentation S L k).append (tablePresentation S L)).Framed := by
  have fields {n : ℕ} : HashChain.PrefixFree (fieldEvents (n := n)) :=
    fieldEvents_framed id Function.injective_id
  have scalar : (scalarDraw : Draw E).width > 0 := by decide
  have rounds {tail : Protocol} (suffix : Presentation tail) (h : suffix.Framed)
      (degree count : ℕ) : (grandRounds degree suffix count).Framed := by
    induction count with
    | zero => exact h
    | succ count ih => exact ⟨fields, scalar, ih⟩
  have interpolate {tail : Protocol} (suffix : Presentation tail) (h : suffix.Framed)
      (count : ℕ) : (interpolation suffix count).Framed := by
    induction count with
    | zero => exact h
    | succ count ih => exact ⟨scalar, ih⟩
  have product {tail : Protocol} (suffix : Presentation tail) (h : suffix.Framed)
      (layers : List ℕ) (used : ℕ) : (grandProduct suffix layers used).Framed := by
    induction layers generalizing used with
    | nil => exact h
    | cons lanes rest ih =>
        refine ⟨scalar, ?_⟩
        apply rounds
        refine ⟨?_, fun _ => interpolate _ (ih _) lanes⟩
        apply fieldEvents_framed
        intro a b equal
        funext i j
        have value := congrFun equal (finProdFinEquiv (i, j))
        have index := finProdFinEquiv.symm_apply_apply (i, j)
        exact (congrArg (fun pair : Fin 3 × Fin (2 ^ lanes) => a pair.1 pair.2) index).symm.trans
          (value.trans (congrArg (fun pair : Fin 3 × Fin (2 ^ lanes) => b pair.1 pair.2) index))
  have pair : HashChain.PrefixFree (fun roots : E × E => fieldEvents ![roots.1, roots.2]) := by
    apply fieldEvents_framed
    intro a b equal
    exact Prod.ext (congrFun equal 0) (congrFun equal 1)
  have bus : (busPresentation S L k).Framed := by
    refine ⟨by change 0 < k + 1; omega, pair, fun _ => ?_⟩
    apply product
    exact ⟨fields, fun _ => trivial⟩
  have table (count : ℕ) : (tableRounds S L count).Framed := by
    induction count with
    | zero =>
      exact ⟨prefixFree_comp (fun values : (t : Fin S.tables.length) → Fin (valuesWidth S L t) → E =>
          ((List.finRange S.tables.length).flatMap fun t => List.ofFn (values t)).map
            (fun value => Transcript.Event.absorb (.scalar value)))
        (valuesFamily S L) (valuesFamily_injective (S := S) (L := L))
        (dependentEvents_framed (valuesWidth S L)), fun _ => trivial⟩
    | succ count ih =>
        refine ⟨?_, scalar, ih⟩
        apply fieldEvents_framed
        intro a b equal
        apply Prod.ext (congrFun equal 0)
        funext i
        exact congrFun equal i.succ
  exact Presentation.Framed.append _ _ bus ⟨scalar, table _⟩

/-- The outer presentation is framed. -/
theorem outerPresentation_framed (params : Parameters S L k M) : (outerPresentation params).Framed :=
  Presentation.Framed.append _ _ (busTable_framed S L k) params.externalFramed

/-- Valid encodings and positive query counts frame the compiled observer. -/
theorem observer_framed (params : Parameters S L k M) (queries : positiveQueries params.schedule) :
    WireObserver.Framed (StandardBcs.compiledCoin Commit.Digest (coin params))
      (presentation params).observer := by
  apply Presentation.Framed.observer
  exact Presentation.Framed.append _ _ (outerPresentation_framed params)
    (whirPresentation_framed params.schedule params.security params.valid queries)

end CompStark.Tables.Compiled
