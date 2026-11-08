/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.HonestRound

/-! An honest WHIR opening with explicit verifier coins and exact ArkLib transcript types.
Commitments contain the complete encoded words. Merkle transport and Fiat–Shamir sampling
belong to the caller; the prover never replaces retained words with short openings. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStark.Pcs
open Interaction Interaction.Oracle

/-- Verifier moves of a WHIR opening, in their protocol order. -/
def WhirCoins (K F : Type) : {n : Nat} → Whir.Schedule K n → Type
  | _, .last lanes tail enc queries =>
      F × (Fin lanes → F) × (Fin queries → enc.Columns) × F × (Fin tail → F)
  | _, @Whir.Schedule.more _ tail lanes enc queries rest =>
      F × (Fin lanes → F) × (Fin tail → F) × (Fin queries → enc.Columns) × WhirCoins K F rest

/-- Encode the head level with its supplied interleaving and additive encoding. -/
def encodeLevel {K F : Type} [Semiring K] [Semiring F] (ι : K →+* F) :
    {n : Nat} → (schedule : Whir.Schedule K n) → Whir.Table F n → Whir.oracleMessage F schedule
  | _, .last _ _ enc _, table => Whir.fullWord (enc.interleave ι table)
  | _, .more _ enc _ _, table => Whir.fullWord (enc.interleave ι table)

/-- Scalar extension commutes with the entire interleaved head commitment. -/
theorem encodeLevel_map {K F : Type} [Semiring K] [Semiring F] (ι : K →+* F)
    {n : Nat} (schedule : Whir.Schedule K n) (table : Whir.Table K n) :
    Whir.mapMasked ι (encodeLevel (RingHom.id K) schedule table) =
      encodeLevel ι schedule (fun u => ι (table u)) := by
  cases schedule <;> funext x <;>
    simp only [encodeLevel, Whir.mapMasked, Whir.fullWord, Function.comp_apply,
      Option.map_some, Option.some.injEq] <;>
    funext u <;>
    simp only [Whir.Encoding.interleave, Whir.Encoding.encode,
      map_sum, map_mul, RingHom.id_apply]

/-- Final consistency claims retain the residual first and every ordered query afterwards. -/
def finalClaims {K F : Type} [Semiring K] [CommRing F] {tail queries : Nat}
    (enc : Whir.Encoding K tail) (ι : K →+* F) (weight table : Whir.Table F tail)
    (xs : Fin queries → enc.Columns) : List (Whir.Claim F tail) :=
  ⟨weight, dot weight table⟩ :: List.ofFn (fun q =>
    ⟨fun u => ι (enc.weight (xs q) u), enc.encode ι table (xs q)⟩)

/-- All residual and query claims hold for the honest terminal table. -/
theorem finalClaims_hold {K F : Type} [Semiring K] [CommRing F] {tail queries : Nat}
    (enc : Whir.Encoding K tail) (ι : K →+* F) (weight table : Whir.Table F tail)
    (xs : Fin queries → enc.Columns) :
    ∀ claim ∈ finalClaims enc ι weight table xs, claim.Holds table := by
  intro claim hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rfl

/-- Every claim introduced at a nonterminal boundary holds for the honest folded table. -/
theorem nextClaims_hold {K F : Type} [Semiring K] [CommRing F] {tail queries : Nat}
    (enc : Whir.Encoding K tail) (ι : K →+* F) (weight table : Whir.Table F tail)
    (z : Fin tail → F) (xs : Fin queries → enc.Columns) :
    ∀ claim ∈ Whir.nextClaims enc ι ⟨weight, dot weight table⟩ z (Whir.mle table z) xs
      (enc.encode ι table), claim.Holds table := by
  intro claim hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rfl
  rcases List.mem_cons.mp hc with rfl | hc
  · rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rfl

/-- Honest opening messages, with each successor word committed before its OOD point is used. -/
@[noinline] def honestWhir {K F : Type} [Semiring K] [CommRing F] (ι : K →+* F) :
    {n : Nat} → (schedule : Whir.Schedule K n) → Whir.Table F n →
      List (Whir.Claim F n) → WhirCoins K F schedule → (Whir.opening F schedule).tree.ExecutionPath
  | _, .last lanes tail enc queries, table, claims, coins =>
      let batched := Whir.batch claims coins.1
      ⟨coins.1, honestRounds (Whir.transition F (.last lanes tail enc queries)) lanes batched.weight table coins.2.1 fun weight folded =>
        let closing := Whir.batch (finalClaims enc ι weight folded coins.2.2.1) coins.2.2.2.1
        ⟨folded, coins.2.2.1, coins.2.2.2.1,
          honestRounds .done (vars := 0) tail closing.weight folded coins.2.2.2.2
            (fun _ _ => PUnit.unit)⟩⟩
  | _, .more lanes enc queries rest, table, claims, coins =>
      let batched := Whir.batch claims coins.1
      ⟨coins.1, honestRounds (Whir.transition F (.more lanes enc queries rest)) lanes batched.weight table coins.2.1 fun weight folded =>
        let answer := Whir.mle folded coins.2.2.1
        let claims' := Whir.nextClaims enc ι ⟨weight, dot weight folded⟩ coins.2.2.1 answer
          coins.2.2.2.1 (enc.encode ι folded)
        ⟨encodeLevel ι rest folded, coins.2.2.1, answer, coins.2.2.2.1,
          honestWhir ι rest folded claims' coins.2.2.2.2⟩⟩

/-- The honest opening is accepted for every verifier-coin sequence and every true input claim. -/
theorem honestWhir_accepts {K F : Type} [Semiring K] [CommRing F] [DecidableEq F]
    (ι : K →+* F) {n : Nat} (schedule : Whir.Schedule K n) (table : Whir.Table F n)
    (claims : List (Whir.Claim F n)) (coins : WhirCoins K F schedule)
    (holds : ∀ claim ∈ claims, claim.Holds table) :
    Whir.accepts ι schedule (encodeLevel ι schedule table) claims
      (honestWhir ι schedule table claims coins) = true := by
  induction schedule with
  | last lanes tail enc queries =>
      change F × (Fin lanes → F) × (Fin queries → enc.Columns) × F × (Fin tail → F) at coins
      have hb := Whir.batch_holds claims table coins.1 holds
      change dot (Whir.batch claims coins.1).weight table = (Whir.batch claims coins.1).value at hb
      change Whir.accepts ι (.last lanes tail enc queries) (Whir.fullWord (enc.interleave ι table)) _ _ = true
      simp only [honestWhir, Whir.accepts, ← hb, read_honestRounds,
        Whir.foldMaskedWord_fullWord, Whir.fold_interleave, Option.getD_some,
        Whir.queriesKnown_fullWord, Bool.true_and]
      have hf := Whir.batch_holds
        (finalClaims enc ι (Whir.restrict (Whir.batch claims coins.1).weight coins.2.1)
          (Whir.restrict table coins.2.1) coins.2.2.1)
        (Whir.restrict table coins.2.1) coins.2.2.2.1
        (finalClaims_hold enc ι _ _ _)
      change dot _ _ = _ at hf
      simp only [finalClaims] at hf ⊢
      simp only [← hf, read_honestClosing, Bool.true_and, decide_true]
  | @more tail lanes enc queries rest ih =>
      change F × (Fin lanes → F) × (Fin tail → F) × (Fin queries → enc.Columns) × WhirCoins K F rest at coins
      have hb := Whir.batch_holds claims table coins.1 holds
      change dot (Whir.batch claims coins.1).weight table = (Whir.batch claims coins.1).value at hb
      change Whir.accepts ι (.more lanes enc queries rest) (Whir.fullWord (enc.interleave ι table)) _ _ = true
      simp only [honestWhir, Whir.accepts, ← hb, read_honestRounds,
        Whir.foldMaskedWord_fullWord, Whir.fold_interleave, Option.getD_some,
        Whir.queriesKnown_fullWord, Bool.true_and]
      exact ih _ _ _ (nextClaims_hold enc ι _ _ _ _)

end CompStark.Pcs
