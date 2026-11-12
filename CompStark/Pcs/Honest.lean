/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.RingSwitch.Prover
public import CompStark.Pcs.HonestWhir

/-! The honest binary-field PCS prover: a base-field commitment, its challenge-field WHIR opening against explicit verifier coins, and ring-switched slice claims batched into the same opening, each accepted by the WHIR verifier. -/

@[expose] public section
namespace CompStark.Pcs.Honest
open CompStark.BinaryFields Interaction Interaction.Oracle

/-- An honest PCS opening retains the complete initial word and all encoded extension words. -/
structure Opening {n : Nat} (schedule : Whir.Schedule K n) where
  /-- The complete base-field oracle; authentication paths are a separate transport. -/
  initial : Whir.oracleMessage K schedule
  /-- Actual honest messages, including complete successor oracles and the terminal table. -/
  transcript : (Whir.opening E schedule).tree.ExecutionPath

/-- Commit the base-field stack and construct its honest opening against explicit verifier coins. -/
def prove {n : Nat} (schedule : Whir.Schedule K n) (table : Whir.Table K n)
    (claims : List (Whir.Claim E n)) (coins : CompStark.Pcs.WhirCoins K E schedule) : Opening schedule :=
  ⟨CompStark.Pcs.encodeLevel (RingHom.id K) schedule table,
    CompStark.Pcs.honestWhir (algebraMap K E) schedule (fun u => ofK (table u)) claims coins⟩

/-- The honest base-field PCS opening satisfies the existing WHIR acceptance predicate. -/
theorem prove_accepts {n : Nat} (schedule : Whir.Schedule K n) (table : Whir.Table K n)
    (claims : List (Whir.Claim E n)) (coins : CompStark.Pcs.WhirCoins K E schedule)
    (holds : ∀ claim ∈ claims, claim.Holds (fun u => ofK (table u))) :
    Whir.accepts (algebraMap K E) schedule
      (Whir.mapMasked ofK (prove schedule table claims coins).initial) claims
      (prove schedule table claims coins).transcript = true := by
  change Whir.accepts (algebraMap K E) schedule
    (Whir.mapMasked (algebraMap K E) (CompStark.Pcs.encodeLevel (RingHom.id K) schedule table))
    claims (CompStark.Pcs.honestWhir (algebraMap K E) schedule (fun u => ofK (table u)) claims coins) = true
  rw [CompStark.Pcs.encodeLevel_map]
  exact CompStark.Pcs.honestWhir_accepts _ _ _ _ _ holds

/-- Open honest ring slices and true point claims with the same shared WHIR batching challenge. -/
def proveRing {n lo hi : Nat} (layout : RingSwitch.Layout n (lo + hi))
    (schedule : Whir.Schedule K (lo + hi)) (table : Whir.Table K (lo + hi))
    (point : Fin n → E) (maps : Vector E 6) (points : List (Whir.Claim E (lo + hi)))
    (coins : CompStark.Pcs.WhirCoins K E schedule) : Opening schedule :=
  prove schedule table (RingSwitch.Prover.opening layout (RingSwitch.Prover.prepare layout table point) maps :: points) coins

/-- Honest ring-switch preparation transfers completeness through the unchanged WHIR verifier. -/
theorem proveRing_accepts {n lo hi : Nat} (layout : RingSwitch.Layout n (lo + hi))
    (schedule : Whir.Schedule K (lo + hi)) (table : Whir.Table K (lo + hi))
    (point : Fin n → E) (maps : Vector E 6) (points : List (Whir.Claim E (lo + hi)))
    (coins : CompStark.Pcs.WhirCoins K E schedule)
    (holds : ∀ claim ∈ points, claim.Holds (fun u => ofK (table u))) :
    Whir.accepts (algebraMap K E) schedule
      (Whir.mapMasked ofK (proveRing layout schedule table point maps points coins).initial)
      (RingSwitch.Prover.opening layout (RingSwitch.Prover.prepare layout table point) maps :: points)
      (proveRing layout schedule table point maps points coins).transcript = true := by
  apply prove_accepts
  intro claim hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact RingSwitch.Prover.opening_holds layout table point maps
  · exact holds claim hc

end CompStark.Pcs.Honest
