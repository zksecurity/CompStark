/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.ParallelClaims

/-! Shared evaluation of WHIR selection and every suffix backward map. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open CompStark.BinaryFields
open Interaction.Oracle.Security

/-- Select the same ordered decoded candidate using sparse numeric claim accumulation. -/
@[macro_inline] def initialExtractorCached {vars lanes : Nat} {enc : Whir.Encoding K vars}
    (decoder : Whir.ListDecoder (E := K) enc lanes) (ι : K →+* E)
    (word : Whir.MaskedWord K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Whir.Claim E (lanes + vars))) : Whir.Table K (lanes + vars) :=
  let images := (decoder.decode word).map fun f =>
    (f, Vector.ofFn fun i : Fin (2 ^ (lanes + vars)) => ι (f (mask (lanes + vars) i)))
  (firstChecked images (fun entry => imageClaimsCheckParallel claims entry.2)
    (0, Vector.replicate (2 ^ (lanes + vars)) 0)).1

/-- Sparse claim checks preserve the exact original selector, including its zero default. -/
theorem initialExtractorCached_eq {vars lanes : Nat} {enc : Whir.Encoding K vars}
    (decoder : Whir.ListDecoder (E := K) enc lanes) (ι : K →+* E)
    (word : Whir.MaskedWord K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Whir.Claim E (lanes + vars))) :
    initialExtractorCached decoder ι word claims = Whir.initialExtractor decoder ι word claims := by
  have check (f : Whir.Table K (lanes + vars)) :
      imageClaimsCheckParallel claims (Vector.ofFn fun i : Fin (2 ^ (lanes + vars)) =>
        ι (f (mask (lanes + vars) i))) =
      (claims.all fun claim => decide ((∑ u, claim.weight u * ι (f u)) = claim.value)) := by
    simpa only [imageClaimsCheckParallel_eq, innerProduct_eq] using imageClaimsCheck_ofFn claims (fun u => ι (f u))
  simp only [initialExtractorCached, firstChecked, List.find?_map, Function.comp_def,
    check, Whir.initialExtractor, Whir.Claim.Holds]
  cases (decoder.decode word).find? (fun f => claims.all fun claim =>
    decide ((∑ u, claim.weight u * ι (f u)) = claim.value)) <;> rfl

/-- The exact opening extractor with shared root selection and suffix evaluation. -/
def openingExtractorCached (ι : K →+* E) : {n : Nat} → (s : Whir.Schedule K n) →
    (nearby : Whir.ProximityFamily K E) → (input : Whir.Table K n → Prop) →
    (decoders : Whir.DecoderFamily (E := E) s) → (word : Whir.oracleMessage K s) →
    (claims : List (Whir.Claim E n)) → (decoder : Whir.InitialDecoder s) →
    RoundExtractor (Whir.opening E s).tree (⟨Whir.Table K n, input⟩)
  | _, .last lanes tail enc queries, nearby, input, decoders, word, claims, decoder =>
    Whir.rootSelection (levelExtractorCached ι (.last lanes tail enc queries) nearby decoders
      (Whir.mapMasked ι word) claims true) ⟨_, input⟩
      (initialExtractorCached decoder ι word claims)
  | _, .more lanes enc queries rest, nearby, input, decoders, word, claims, decoder =>
    Whir.rootSelection (levelExtractorCached ι (.more lanes enc queries rest) nearby decoders
      (Whir.mapMasked ι word) claims true) ⟨_, input⟩
      (initialExtractorCached decoder ι word claims)

/-- The cached selector leaves the complete WHIR extractor exactly equal to its specification. -/
theorem openingExtractorCached_eq (ι : K →+* E) {n : Nat} (s : Whir.Schedule K n)
    (nearby : Whir.ProximityFamily K E) (input : Whir.Table K n → Prop)
    (decoders : Whir.DecoderFamily (E := E) s) (word : Whir.oracleMessage K s)
    (claims : List (Whir.Claim E n)) (decoder : Whir.InitialDecoder s) :
    openingExtractorCached ι s nearby input decoders word claims decoder =
      Whir.openingExtractor ι s nearby input decoders word claims decoder := by
  cases s <;> simp only [openingExtractorCached, levelExtractorCached_eq,
    Whir.openingExtractor, Whir.selectInitial, initialExtractorCached_eq]

/-- Compute the initial candidate once before passing its function-valued table to a consumer. -/
@[noinline, nospecialize] def selectInitialPreparedWith {Result : Type} (ι : K →+* E) :
    {n : Nat} → (s : Whir.Schedule K n) → Whir.InitialDecoder s →
    Whir.oracleMessage K s → List (Whir.Claim E n) → (Whir.Table K n → Result) → Result
  | _, .last _ _ _ _, decoder, word, claims, finish => finish (initialExtractorCached decoder ι word claims)
  | _, .more _ _ _ _, decoder, word, claims, finish => finish (initialExtractorCached decoder ι word claims)

/-- Shared initial selection passes exactly the original ordered selector to every consumer. -/
theorem selectInitialPreparedWith_eq {Result : Type} (ι : K →+* E) {n : Nat} (s : Whir.Schedule K n)
    (decoder : Whir.InitialDecoder s) (word : Whir.oracleMessage K s)
    (claims : List (Whir.Claim E n)) (finish : Whir.Table K n → Result) :
    selectInitialPreparedWith ι s decoder word claims finish =
      finish (Whir.selectInitial ι s decoder word claims) := by
  cases s <;> simp only [selectInitialPreparedWith, Whir.selectInitial, initialExtractorCached_eq]

/-- The opening's fixed root selection is independent of every suffix witness. -/
theorem openingExtractor_extractWitness (ι : K →+* E) {n : Nat} (s : Whir.Schedule K n)
    (nearby : Whir.ProximityFamily K E) (input : Whir.Table K n → Prop)
    (decoders : Whir.DecoderFamily (E := E) s) (word : Whir.oracleMessage K s)
    (claims : List (Whir.Claim E n)) (decoder : Whir.InitialDecoder s)
    (path : (Whir.opening E s).tree.ExecutionPath)
    (witness : ((Whir.openingExtractor ι s nearby input decoders word claims decoder).terminalState path).Witness) :
    (Whir.openingExtractor ι s nearby input decoders word claims decoder).extractWitness path witness =
      Whir.selectInitial ι s decoder word claims := by
  cases s <;> rfl

end CompStark.Pcs
