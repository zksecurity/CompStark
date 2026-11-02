/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkParse
public import CompStark.Fs.Batch

/-! # Plonky3's batch verifier draws its challenges as the real completion

As for the STARK (`StarkParse.lean`, whose generic pieces `openedPath`, `replay_realCompletion`,
`duplexCache`, `sample_sampleStates`, `extDraw_idealOf` and `queryDraw_idealOf` are used here): a
selection of the batch's decoded snapshot protocol is read off a Plonky3 batch proof, and the real
completion of it draws exactly the challenges Plonky3's batch verifier samples.

* `pairDraw_idealOf`, `lookupRun_idealOf`: Plonky3's lookup phase is the lookup challenges' draw on
  the squeezes' coins, with lookups the grinding check and two extension samples, without lookups
  no squeeze and `(0, 0)`; `extDraw_idealOf_of`: an extension draw from a challenger state.
* `openingsElems_openingsOfB`, `terminalsElems_terminalsOf`: the claimed values and the terminals
  read off a proof are observed as Plonky3's PCS and lookup phase observe them.
* `Setup.parse`, `Statement.parse`: the selection's messages read off a proof, every snapshot move
  `T`: the lengths, the main cap, the lookup witness, the permutation commitment
  (`Setup.permComOf`), the terminals (`Setup.terminalsOf`), `α`'s empty witness, the quotient's cap
  and the out-of-domain witness, the claimed values (`Setup.openingsOf`) and the batching witness,
  FRI's caps and commit witnesses, the final polynomial and the query witness (`parseFri`). Its
  input is the public values and the preprocessed commitment's elements (`Statement.inputOf`).
* `Setup.openedPath_parse`: if Plonky3's batch verifier on the duplex answers accepts, the real
  completion of the proof's selection, replayed on the duplex answers, decodes, every draw
  accepting, and opens to the proof's execution path (`Setup.proofPath`).
* `Setup.isSome_parse`, `Statement.isSome_parse`: an accepted proof has a selection, its caps of
  the sizes the verifier accepts (`Setup.caps_of_verifyInstancesWith`).
-/

@[expose] public section

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle.Security.HashChain

section Draws
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}
  (answer : (q : Query F) → Answer K q)

omit [BaseField F] in
/-- `j` samples after `n` samples are `n + j` samples. -/
theorem sampleStates_add {G : Primitives F Id} (s : G.State) (n : ℕ) :
    ∀ j, Ni.sampleStates G (Ni.sampleStates G s n) j = Ni.sampleStates G s (n + j)
  | 0 => rfl
  | j + 1 => by rw [Ni.sampleStates, sampleStates_add s n j]; rfl

/-- The lookup challenges' witness from a grinding witness: none without grinding. -/
def pairWitnessOf : (bits : ℕ) → F → (pairDraw (F := F) (EF := EF) (K := K) (m := m) bits).Witness
  | 0, _ => PUnit.unit
  | _ + 1, w => w

/-- **The lookup challenges on the stream.** From the capacity of the blocks `acc` with `x₀`
pending, Plonky3's grinding check and two extension samples are the lookup challenges' draw on the
coins of the block `x₀` and the witness: the check passes as the draw accepts, the samples are the
decoded pair, and the challenger is left at the capacity after the draw's squeezes with nothing
pending. -/
theorem pairDraw_idealOf (hK : 0 < K) (bits : ℕ) (w : F) (x₀ : List F) (acc : List (List F))
    (hm : squeezesFor K (pairSamples (EF := EF) bits) ≤ m) :
    (pairDraw (F := F) (EF := EF) bits).accept (streamCoins (m := m) answer
        (x₀ ++ Ni.witnessInput bits w) acc (squeezesFor K (pairSamples (EF := EF) bits))) =
        (Ni.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).1 ∧
      (pairDraw (F := F) (EF := EF) bits).decode (streamCoins (m := m) answer
        (x₀ ++ Ni.witnessInput bits w) acc (squeezesFor K (pairSamples (EF := EF) bits))) =
        (Challenge.toSpec (Ni.smpExt (EF := EF) (idealOf answer)
          (Ni.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).1,
          Challenge.toSpec (Ni.smpExt (EF := EF) (idealOf answer) (Ni.smpExt (EF := EF)
            (idealOf answer) (Ni.chkWit (idealOf answer) bits w
              ⟨capOf answer acc, x₀, []⟩).2).2).1) ∧
      (Ni.smpExt (EF := EF) (idealOf answer) (Ni.smpExt (EF := EF) (idealOf answer)
        (Ni.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).2).2.cap =
        capOf answer (List.replicate (squeezesFor K (pairSamples (EF := EF) bits) - 1) [] ++
          (x₀ ++ Ni.witnessInput bits w) :: acc) ∧
      (Ni.smpExt (EF := EF) (idealOf answer) (Ni.smpExt (EF := EF) (idealOf answer)
        (Ni.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).2).2.input = [] := by
  have hd : 0 < Challenge.d EF := (Challenge.params EF).d_pos
  have hn := le_squeezesFor_mul (K := K) hK (pairSamples (EF := EF) bits)
  have hss (s : Sponge F) : (Ni.smpExt (EF := EF) (idealOf answer) (Ni.smpExt (EF := EF)
      (idealOf answer) s).2).2 = Ni.sampleStates (idealOf answer) s (Challenge.d EF +
        Challenge.d EF) := by
    rw [Ni.smpExt, smpList_eq, Ni.smpExt, smpList_eq, sampleStates_add]
  have hsnd (s : Sponge F) : Challenge.toSpec (Ni.smpExt (EF := EF) (idealOf answer)
      (Ni.smpExt (EF := EF) (idealOf answer) s).2).1 = Ni.extEquiv fun j =>
        ((idealOf answer).sample (Ni.sampleStates (idealOf answer) s
          (Challenge.d EF + j))).1 := by
    rw [toSpec_smpExt]
    congr 1
    funext j
    rw [Ni.smpExt, smpList_eq, sampleStates_add]
  cases bits with
  | zero =>
    have hx : x₀ ++ Ni.witnessInput 0 w = x₀ := List.append_nil x₀
    have hs : pairSamples (EF := EF) 0 = 2 * Challenge.d EF := by
      simp only [pairSamples, ↓reduceIte, Nat.add_zero]
    rw [hx]
    rw [hs] at hm hn ⊢
    have hst := sampleStates_succ_eq answer hK x₀ acc (2 * Challenge.d EF - 1)
    rw [Nat.sub_add_cancel (by omega)] at hst
    have hchk : Ni.chkWit (idealOf answer) 0 w ⟨capOf answer acc, x₀, []⟩ =
        (true, ⟨capOf answer acc, x₀, []⟩) := rfl
    rw [hchk]
    refine ⟨rfl, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change Ni.extEquiv _ = _
        rw [toSpec_smpExt]
        congr 1
        funext j
        rw [Nat.zero_add, sampleAt_streamCoins_eq answer hK hm (by omega)]
      · change Ni.extEquiv _ = _
        rw [hsnd]
        congr 1
        funext j
        rw [sampleAt_streamCoins_eq answer hK hm (by omega), Nat.zero_add]
    · rw [squeezesFor_sub_one hK (by omega), hss, show Challenge.d EF + Challenge.d EF =
        2 * Challenge.d EF by omega]
      exact hst
  | succ b =>
    have hx : Ni.witnessInput (b + 1) w = [w] := rfl
    have hs : pairSamples (EF := EF) (b + 1) = 2 * Challenge.d EF + 1 := by
      simp only [pairSamples, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hx]
    rw [hs] at hm hn ⊢
    have hchk : Ni.chkWit (idealOf answer) (b + 1) w ⟨capOf answer acc, x₀, []⟩ =
        (CompPoly.CanonicalNat.toNat ((idealOf answer).sample
          ⟨capOf answer acc, x₀ ++ [w], []⟩).1 % 2 ^ (b + 1) == 0,
          ((idealOf answer).sample ⟨capOf answer acc, x₀ ++ [w], []⟩).2) := rfl
    have hst := sampleStates_succ_eq answer hK (x₀ ++ [w]) acc (2 * Challenge.d EF)
    rw [hchk]
    refine ⟨?_, ?_, ?_⟩
    · change (powSample _ % 2 ^ (b + 1) == 0) = _
      rw [powSample, sampleAt_streamCoins_eq answer hK hm (by omega)]
      rfl
    · refine Prod.ext ?_ ?_
      · change Ni.extEquiv _ = _
        rw [toSpec_smpExt]
        congr 1
        funext j
        rw [Ni.sampleStates_sample, sampleAt_streamCoins_eq answer hK hm (by omega),
          Nat.add_comm]
      · change Ni.extEquiv _ = _
        rw [hsnd]
        congr 1
        funext j
        rw [Ni.sampleStates_sample, sampleAt_streamCoins_eq answer hK hm (by omega)]
        congr 3
        omega
    · rw [squeezesFor_sub_one hK (Nat.succ_pos _), Nat.succ_sub_one, hss,
        Ni.sampleStates_sample, show Challenge.d EF + Challenge.d EF + 1 =
          2 * Challenge.d EF + 1 by omega]
      exact hst

/-- The lookup challenges' witness from a grinding witness: none without lookups or grinding. -/
def lookupWitnessOf : (b : Bool) → (bits : ℕ) → F →
    (lookupDraw (F := F) (EF := EF) (K := K) (m := m) b bits).Witness
  | true, bits, w => pairWitnessOf bits w
  | false, _, _ => PUnit.unit

theorem pairWitnessElems_pairWitnessOf (bits : ℕ) (w : F) :
    lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) true bits
      (lookupWitnessOf true bits w) = Ni.witnessInput bits w := by
  cases bits <;> rfl

/-- **The lookup phase on the stream.** From the capacity of the blocks `acc` with `x₀` pending,
Plonky3's lookup phase is the lookup challenges' draw on the coins of the block `x₀` and the
witness: with lookups, the grinding check passes as the draw accepts, the challenges are the
decoded pair, and the challenger is left at the capacity after the draw's squeezes with nothing
pending; without lookups, the draw accepts, decodes `(0, 0)`, and the challenger is unchanged. -/
theorem lookupRun_idealOf (hK : 0 < K) (P : Fri.Params)
    (instances : List (CompStark.Batch.Instance F))
    (proof : CompStark.Batch.BatchProof F EF) {x₀ : List F} {acc : List (List F)} (s : Sponge F)
    (hs : s = ⟨capOf answer acc, x₀, []⟩)
    (hm : squeezesFor K (pairSamples (EF := EF) P.lookupPowBits) ≤ m) :
    (lookupDraw (F := F) (EF := EF) (CompStark.Batch.hasLookups instances) P.lookupPowBits).accept
        (streamCoins (m := m) answer (x₀ ++ lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m)
          (CompStark.Batch.hasLookups instances) P.lookupPowBits
          (lookupWitnessOf (F := F) (EF := EF) (K := K) (m := m)
            (CompStark.Batch.hasLookups instances) P.lookupPowBits
            (proof.lookupWitness.getD 0))) acc
          (lookupSqueezes (EF := EF) K (CompStark.Batch.hasLookups instances) P.lookupPowBits)) =
        (!CompStark.Batch.hasLookups instances || (Ni.chkWit (idealOf answer) P.lookupPowBits
          (proof.lookupWitness.getD 0) s).1) ∧
      (lookupDraw (F := F) (EF := EF) (CompStark.Batch.hasLookups instances) P.lookupPowBits).decode
        (streamCoins (m := m) answer (x₀ ++ lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m)
          (CompStark.Batch.hasLookups instances) P.lookupPowBits
          (lookupWitnessOf (F := F) (EF := EF) (K := K) (m := m)
            (CompStark.Batch.hasLookups instances) P.lookupPowBits
            (proof.lookupWitness.getD 0))) acc
          (lookupSqueezes (EF := EF) K (CompStark.Batch.hasLookups instances) P.lookupPowBits)) =
        (Challenge.toSpec (Ni.lookupRun (idealOf answer) P instances proof s).1.1,
          Challenge.toSpec (Ni.lookupRun (idealOf answer) P instances proof s).1.2) ∧
      (CompStark.Batch.hasLookups instances = true →
        (Ni.lookupRun (idealOf answer) P instances proof s).2.cap =
          capOf answer (List.replicate (squeezesFor K (pairSamples (EF := EF) P.lookupPowBits) - 1)
            [] ++ (x₀ ++ Ni.witnessInput P.lookupPowBits (proof.lookupWitness.getD 0)) :: acc) ∧
        (Ni.lookupRun (idealOf answer) P instances proof s).2.input =
          []) ∧
      (CompStark.Batch.hasLookups instances = false →
        (Ni.lookupRun (idealOf answer) P instances proof s).2 = s) := by
  subst hs
  unfold Ni.lookupRun
  cases hb : CompStark.Batch.hasLookups instances with
  | true =>
    obtain ⟨ha, hd, hc, hi⟩ := pairDraw_idealOf (m := m) answer hK P.lookupPowBits
      (proof.lookupWitness.getD 0) x₀ acc hm
    have hw := pairWitnessElems_pairWitnessOf (F := F) (EF := EF) (K := K) (m := m)
      P.lookupPowBits (proof.lookupWitness.getD 0)
    refine ⟨?_, ?_, fun _ ↦ ⟨hc, hi⟩, fun h ↦ absurd h (by decide)⟩
    · change (pairDraw P.lookupPowBits).accept (streamCoins answer (x₀ ++ lookupWitnessElems true
        P.lookupPowBits (lookupWitnessOf true P.lookupPowBits (proof.lookupWitness.getD 0))) acc
        (squeezesFor K (pairSamples (EF := EF) P.lookupPowBits))) = _
      rw [hw, ha]
      rfl
    · change (pairDraw P.lookupPowBits).decode (streamCoins answer (x₀ ++ lookupWitnessElems true
        P.lookupPowBits (lookupWitnessOf true P.lookupPowBits (proof.lookupWitness.getD 0))) acc
        (squeezesFor K (pairSamples (EF := EF) P.lookupPowBits))) = _
      rw [hw, hd]
      rfl
  | false =>
    refine ⟨rfl, ?_, fun h ↦ absurd h (by decide), fun _ ↦ rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Challenge.toSpec_zero]
    rfl

/-- **An extension draw on the stream, from a challenger.** From a challenger at the capacity of
the blocks `acc` with `x₀` pending and no sample left, Plonky3's grinding check and extension sample
are the draw on the coins of the block `x₀` and the witness's elements. -/
theorem extDraw_idealOf_of (hK : 0 < K) (bits : ℕ) (w : F) {x₀ : List F} {acc : List (List F)}
    (s : Sponge F) (hcap : s.cap = capOf answer acc) (hin : s.input = x₀) (hout : s.samples = [])
    (hm : squeezesFor K (extSamples (EF := EF) bits) ≤ m) :
    (extDraw (F := F) (EF := EF) bits).accept (streamCoins (m := m) answer
        (x₀ ++ extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits (extWitnessOf bits w))
        acc (squeezesFor K (extSamples (EF := EF) bits))) =
        (Ni.chkWit (idealOf answer) bits w s).1 ∧
      (extDraw (F := F) (EF := EF) bits).decode (streamCoins (m := m) answer
        (x₀ ++ extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits (extWitnessOf bits w))
        acc (squeezesFor K (extSamples (EF := EF) bits))) =
        Challenge.toSpec (Ni.smpExt (EF := EF) (idealOf answer)
          (Ni.chkWit (idealOf answer) bits w s).2).1 ∧
      (Ni.smpExt (EF := EF) (idealOf answer) (Ni.chkWit (idealOf answer) bits w s).2).2.cap =
        capOf answer (List.replicate (squeezesFor K (extSamples (EF := EF) bits) - 1) [] ++
          (x₀ ++ extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits (extWitnessOf bits w))
            :: acc) ∧
      (Ni.smpExt (EF := EF) (idealOf answer) (Ni.chkWit (idealOf answer) bits w s).2).2.input =
        [] := by
  obtain ⟨c, i, o⟩ := s
  dsimp only at hcap hin hout
  subst hcap hin hout
  rw [extWitnessElems_extWitnessOf]
  exact extDraw_idealOf answer hK bits w _ acc hm

theorem lookupWitnessElems_lookupWitnessOf (b : Bool) (bits : ℕ) (w : F) :
    lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) b bits (lookupWitnessOf b bits w) =
      if b then Ni.witnessInput bits w else [] := by
  cases b
  · rfl
  · exact pairWitnessElems_pairWitnessOf bits w

end Draws

end CompStark.Fs

/-! ### Steps of `openedPath` at a challenge that may not squeeze -/

namespace CompStark.Fs
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section Steps
variable {F Snap C : Type} [DecidableEq Snap] [SampleableType C]
  (coins : List F × List (List F) → ℕ → C)

/-- A challenge whose draw accepts its coins decodes them; if it squeezes, it starts a block, and
otherwise its block goes on with the witness's elements pending. -/
theorem openedPath_challenge_ite {Challenge : Type} [SampleableType Challenge]
    {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (lay : Layout F Snap (.challenge next) dec) (T : Snap) (pending tail : List F)
    (acc : List (List F)) (w : dec.1.Witness) (u : PUnit)
    (msgs : Messages PUnit (decoded C (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
      (snapDecoder next dec.2 lay.2.2 (lay.1 != 0))))
    (hacc : dec.1.accept (coins (pending ++ tail ++ lay.2.1 w, acc) lay.1) = true) :
    openedPath coins (.challenge next) dec lay false T pending tail acc
        (⟨w, u, msgs⟩ : (_ : dec.1.Witness) × (PUnit × Messages PUnit (decoded C
          (snapCoin next dec.2 lay.2.2 (lay.1 != 0)) (snapDecoder next dec.2 lay.2.2 _)))) =
      (openedPath coins next dec.2 lay.2.2 (lay.1 != 0) T
        (if lay.1 = 0 then pending ++ lay.2.1 w else [])
        (if lay.1 = 0 then tail else [])
        (if lay.1 = 0 then acc else
          List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ lay.2.1 w) :: acc) msgs).map
        fun r => ⟨dec.1.decode (coins (pending ++ tail ++ lay.2.1 w, acc) lay.1), r⟩ := by
  simp only [openedPath, hacc, Bool.cond_true]
  split <;> rfl

end Steps

end CompStark.Fs

/-! ### The claimed values as observed -/

namespace CompStark.Fs
open CompStark.Stark CompStark.Ni

section Values
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- `w` columns of `d` coordinates read off an array of `w d` elements are observed as the
array's coefficients. -/
theorem flatten_extsElems_getD {w : ℕ} (a : Array EF) (ha : a.size = w * Challenge.d EF) :
    (List.ofFn fun c : Fin w => extsElems (F := F) fun e : Fin (Challenge.d EF) =>
      Challenge.toSpec (a.getD (c.val * Challenge.d EF + e.val) 0)).flatten =
      Ni.coeffs a.toList := by
  rw [← extsElems_getD (F := F) a ha, extsElems, List.ofFn_mul,
    List.flatten_eq_flatMap (L := List.ofFn fun i => List.ofFn fun j => _), List.flatMap_assoc,
    List.flatMap_def, List.map_ofFn]
  rfl

/-- An array of no elements is observed as nothing. -/
theorem toList_of_size_zero (a : Array EF) (h : a.size = 0) : a.toList = [] := by
  rw [← Array.length_toList] at h
  exact List.eq_nil_of_length_eq_zero h

variable {lookups : List (Lookup F)} (T : Iop.Setup EF lookups) (o : OpenedValues EF)
  (cur next : Array EF)

theorem traceElems_openingsOf (htl : o.traceLocal.size = T.air.width)
    (htn : traceNextOk T.air o = true) :
    Iop.Batch.Setup.traceElems (F := F) (Ni.openingsOf T o cur next) =
      Ni.coeffs (mainVals T.air o) := by
  have h1 : extsElems (F := F) (Ni.openingsOf T o cur next).traceAt =
      Ni.coeffs o.traceLocal.toList := extsElems_getD _ htl
  have h2 : extsElems (F := F) (Ni.openingsOf T o cur next).traceNext =
      Ni.coeffs (o.traceNext.getD #[]).toList := extsElems_getD _ (traceNext_of_ok htn).1
  rw [Iop.Batch.Setup.traceElems, h1, h2, mainVals, Ni.coeffs_append]
  congr 1
  split
  · rfl
  · rename_i hn
    rw [toList_of_size_zero _ (by rw [(traceNext_of_ok htn).1, Air.mainNextWidth]; simp [hn])]

theorem quotientElems_openingsOf (hqc : o.quotientChunks.size = T.chunks)
    (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF) :
    Iop.Batch.Setup.quotientElems (F := F) (Ni.openingsOf T o cur next) =
      Ni.coeffs (quotVals o) := by
  have hl : (List.ofFn fun c : Fin T.chunks => extsElems (F := F)
      ((Ni.openingsOf T o cur next).quotientAt c)) =
      o.quotientChunks.toList.map fun ch => Ni.coeffs ch.toList := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, Array.length_toList,
      hqc]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn, List.getElem_map]
    have hi : i < o.quotientChunks.size := by rw [hqc]; simpa using h1
    have hi' : i < o.quotientChunks.toList.length := by rw [Array.length_toList]; exact hi
    have hc : o.quotientChunks.getD i #[] = o.quotientChunks.toList[i]'hi' := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
        Array.getElem_toList]
    have h4 := hq4 _ (Array.getElem_mem hi)
    change extsElems (fun e : Fin (Challenge.d EF) =>
      Challenge.toSpec ((o.quotientChunks.getD i #[]).getD e 0)) = _
    rw [extsElems_getD _ (by rw [hc, ← Array.getElem_toList] at *; exact h4), hc]
  rw [Iop.Batch.Setup.quotientElems, hl, quotVals]
  simp only [Ni.coeffs]
  rw [List.flatMap_assoc, List.flatMap_def]

theorem preprocessedElems_openingsOf
    (hpl : (o.preprocessedLocal.getD #[]).size = T.air.preprocessedWidth)
    (hpn : (o.preprocessedNext.getD #[]).size = T.air.preprocessedNextWidth) :
    Iop.Batch.Setup.preprocessedElems (F := F) (Ni.openingsOf T o cur next) =
      Ni.coeffs (prepVals T.air o) := by
  have h1 : extsElems (F := F) (Ni.openingsOf T o cur next).preprocessedAt =
      Ni.coeffs (o.preprocessedLocal.getD #[]).toList := extsElems_getD _ hpl
  have h2 : extsElems (F := F) (Ni.openingsOf T o cur next).preprocessedNext =
      Ni.coeffs (o.preprocessedNext.getD #[]).toList := extsElems_getD _ hpn
  have hle := T.air.preprocessedNextWidth_le
  rw [Iop.Batch.Setup.preprocessedElems, h1, h2, prepVals]
  split
  · rw [Ni.coeffs_append]
    congr 1
    split
    · rfl
    · rename_i hn
      rw [toList_of_size_zero _ (by rw [hpn, Air.preprocessedNextWidth]; simp [hn])]
  · rename_i hw
    rw [toList_of_size_zero _ (by rw [hpl]; omega),
      toList_of_size_zero _ (by rw [hpn]; omega)]
    rfl

theorem permElems_openingsOf (hcur : cur.size = Challenge.d EF * T.permWidth)
    (hnext : next.size = Challenge.d EF * T.permWidth) :
    Iop.Batch.Setup.permElems (F := F) (Ni.openingsOf T o cur next) =
      Ni.coeffs (permVals lookups cur next) := by
  rw [Nat.mul_comm] at hcur hnext
  rw [Iop.Batch.Setup.permElems, permVals]
  change (List.ofFn fun c : Fin T.permWidth => extsElems (F := F) fun e : Fin (Challenge.d EF) =>
      Challenge.toSpec (cur.getD (c.val * Challenge.d EF + e.val) 0)).flatten ++
    (List.ofFn fun c : Fin T.permWidth => extsElems (F := F) fun e : Fin (Challenge.d EF) =>
      Challenge.toSpec (next.getD (c.val * Challenge.d EF + e.val) 0)).flatten = _
  rw [flatten_extsElems_getD _ hcur, flatten_extsElems_getD _ hnext]
  split
  · rename_i hl
    have hw : T.permWidth = 0 := by
      rw [List.isEmpty_iff] at hl
      subst hl
      rfl
    rw [hw, Nat.zero_mul] at hcur hnext
    rw [toList_of_size_zero _ hcur, toList_of_size_zero _ hnext]
    rfl
  · rw [Ni.coeffs_append]

/-- On a proof in the instances' shapes, the claimed values read off it are observed as the batch
verifier's PCS observes the opened values. -/
theorem openingsElems_openingsOfB (S : Iop.Batch.Setup EF) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (z : EF) (hsize : proof.opened.size = S.k)
    (hlsize : proof.permutationLocal.size = S.k) (hnsize : proof.permutationNext.size = S.k)
    (hshape : ∀ i : Fin S.k, CompStark.Batch.openedShapeOk ⟨S.air i, S.logN i, S.lookups i⟩
      (proof.opened.toList.getD i noOpenings) = true)
    (hprep : common.preprocessed.isSome = S.instances.any (0 < ·.air.preprocessedWidth))
    (hpw : ∀ i : Fin S.k,
      (proof.permutationLocal.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth ∧
      (proof.permutationNext.getD i #[]).size = Challenge.d EF * (S.instanceSetup i).permWidth)
    (hperm : proof.permutationCommit.isSome = S.hasLookups) :
    S.openingsElems (S.openingsOf proof) =
      Ni.coeffs (roundValues (CompStark.Batch.batchRounds S.instances common proof z)) := by
  have hsh := fun i ↦ openedShapeOk_spec (hshape i)
  have hc (f : Fin S.k → List EF) : Ni.coeffs ((List.finRange S.k).flatMap f) =
      (List.finRange S.k).flatMap fun i ↦ Ni.coeffs (f i) := by
    simp only [Ni.coeffs]
    rw [List.flatMap_assoc]
  have hA : (List.finRange S.k).flatMap (fun i ↦ Iop.Batch.Setup.traceElems (F := F)
      (S.openingsOf proof i)) = Ni.coeffs ((List.finRange S.k).flatMap fun i ↦
        mainVals (S.air i) (proof.opened.toList.getD i noOpenings)) := by
    rw [hc]
    exact List.flatMap_congr fun i _ ↦ traceElems_openingsOf _ _ _ _ (hsh i).1 (hsh i).2.1
  have hB : (List.finRange S.k).flatMap (fun i ↦ Iop.Batch.Setup.quotientElems (F := F)
      (S.openingsOf proof i)) = Ni.coeffs ((List.finRange S.k).flatMap fun i : Fin S.k ↦
        quotVals (proof.opened.toList.getD i.val noOpenings)) := by
    rw [hc]
    exact List.flatMap_congr fun i _ ↦ quotientElems_openingsOf _ _ _ _
      ((hsh i).2.2.1.trans (congrArg (2 ^ ·) (logChunks_eq S i).symm)) (hsh i).2.2.2.1
  have hC : (List.finRange S.k).flatMap (fun i ↦ Iop.Batch.Setup.preprocessedElems (F := F)
      (S.openingsOf proof i)) = Ni.coeffs ((List.finRange S.k).flatMap fun i ↦
        prepVals (S.air i) (proof.opened.toList.getD i noOpenings)) := by
    rw [hc]
    exact List.flatMap_congr fun i _ ↦ preprocessedElems_openingsOf _ _ _ _ (hsh i).2.2.2.2.1
      (hsh i).2.2.2.2.2
  have hD : (List.finRange S.k).flatMap (fun i ↦ Iop.Batch.Setup.permElems (F := F)
      (S.openingsOf proof i)) = Ni.coeffs ((List.finRange S.k).flatMap fun i ↦
        permVals (S.lookups i) (proof.permutationLocal.getD i #[])
          (proof.permutationNext.getD i #[])) := by
    rw [hc]
    exact List.flatMap_congr fun i _ ↦ permElems_openingsOf _ _ _ _ (hpw i).1 (hpw i).2
  have hC0 : common.preprocessed = none → (List.finRange S.k).flatMap (fun i : Fin S.k ↦
      prepVals (S.air i) (proof.opened.toList.getD i noOpenings)) = [] := fun hp ↦ by
    rw [hp, Option.isSome_none, eq_comm, List.any_eq_false] at hprep
    refine List.flatMap_eq_nil_iff.mpr fun i _ ↦ ?_
    have := hprep ⟨S.air i, S.logN i, S.lookups i⟩ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simp only [decide_eq_true_eq] at this
    simp only [prepVals, this, ↓reduceIte]
  have hD0 : proof.permutationCommit = none → (List.finRange S.k).flatMap (fun i : Fin S.k ↦
      permVals (S.lookups i) (proof.permutationLocal.getD i #[])
        (proof.permutationNext.getD i #[])) = [] := fun hp ↦ by
    rw [hp, Option.isSome_none, eq_comm] at hperm
    refine List.flatMap_eq_nil_iff.mpr fun i _ ↦ ?_
    simp only [permVals, lookups_eq_nil_of S hperm i, List.isEmpty_nil, ↓reduceIte]
  rw [Iop.Batch.Setup.openingsElems, roundValues_batchRounds_eq S common proof hsize hlsize hnsize,
    Ni.coeffs_append, Ni.coeffs_append, Ni.coeffs_append, hA, hB, hC, hD]
  rcases hp1 : common.preprocessed with _ | c <;> rcases hp2 : proof.permutationCommit with _ | c'
  · rw [hC0 hp1, hD0 hp2]
  · rw [hC0 hp1]
  · rw [hD0 hp2]
  · rfl

omit [BaseField F] [Challenge F EF] in
/-- Keeping the values of the elements that pass a test is filtering and mapping. -/
theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, l.filterMap (fun a ↦ if p a then some (f a) else none) = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp only [List.filterMap_cons, h, ↓reduceIte, List.filter_cons_of_pos h, List.map_cons,
        filterMap_ite p f l]
    · simp only [List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte,
        List.filter_cons_of_neg h, filterMap_ite p f l]

/-- On a proof with a terminal exactly for the instances with lookups, the terminals read off it
are observed as Plonky3 observes the proof's terminals. -/
theorem terminalsElems_terminalsOf (S : Iop.Batch.Setup EF)
    (proof : CompStark.Batch.BatchProof F EF) (htsize : proof.lookupTerminals.size = S.k)
    (hsome : ∀ i : Fin S.k, (proof.lookupTerminals.getD i none).isSome = !(S.lookups i).isEmpty) :
    S.terminalsElems (S.terminalsOf proof) =
      Ni.coeffs (proof.lookupTerminals.toList.filterMap id) := by
  classical
  set g : Fin S.k → EF := fun i ↦ (proof.lookupTerminals.getD i none).getD 0 with hg
  have hget (j : Fin S.k) : proof.lookupTerminals.toList.getD j none =
      proof.lookupTerminals.getD j none := by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hmem (j : Fin S.k) : j ∈ S.lookupInstances ↔ (S.lookups j).isEmpty = false := by
    simp only [Iop.Batch.Setup.lookupInstances, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_eq, List.isEmpty_eq_false_iff]
  have hopt (j : Fin S.k) : proof.lookupTerminals.getD j none =
      if decide (j ∈ S.lookupInstances) then some (g j) else none := by
    have h := hsome j
    by_cases hj : j ∈ S.lookupInstances
    · rw [(hmem j).mp hj, Bool.not_false] at h
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
      simp only [hj, decide_true, ↓reduceIte, hg, hy, Option.getD_some]
    · rw [hmem, Bool.not_eq_false] at hj
      rw [hj, Bool.not_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      have hj' : j ∉ S.lookupInstances := by rw [hmem, hj]; decide
      simp only [hj', decide_false, Bool.false_eq_true, ↓reduceIte, h]
  have hsort : S.lookupInstances.sort =
      (List.finRange S.k).filter fun j ↦ decide (j ∈ S.lookupInstances) :=
    S.lookupInstances.sortedLT_sort.eq_of_mem_iff
      ((List.sortedLT_finRange S.k).pairwise.filter _).sortedLT fun a ↦ by
        simp only [Finset.mem_sort, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq]
  have hl : List.ofFn (S.terminalsOf proof ∘ S.lookupInstances.orderIsoOfFin rfl) =
      (S.lookupInstances.sort).map fun j ↦ Challenge.toSpec (g j) := by
    rw [← Finset.listMap_orderEmbOfFin_finRange S.lookupInstances rfl, List.map_map,
      List.ofFn_eq_map]
    rfl
  have hr : proof.lookupTerminals.toList.filterMap id =
      ((List.finRange S.k).filter fun j ↦ decide (j ∈ S.lookupInstances)).map g := by
    rw [filterMap_id_eq _ (by rw [Array.length_toList, htsize]), ← filterMap_ite,
      ← List.filterMap_eq_flatMap_toList]
    exact List.filterMap_congr fun j _ ↦ by rw [hget, hopt]
  rw [Iop.Batch.Setup.terminalsElems, extsElems, hl, hr, hsort, List.flatMap_map, Ni.coeffs,
    List.flatMap_map]
  exact List.flatMap_congr fun j _ ↦ extElems_toSpec _

end Values

end CompStark.Fs

/-! ### FRI's grinding checks on rounds of mixed heights -/

namespace CompStark.Fs
open CompStark.Stark CompStark.Fri

/-- **An accepting FRI verifier passes its commit loop's grinding checks**, from the challenger
after FRI's domain separator, on rounds of any heights. -/
theorem commitChecks_of_verifyFriR {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
    (G : Primitives F Id) (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) (s : G.State) (r : Unit × G.State)
    (h : verifyFri G P proof rounds alpha s = .ok r) :
    CommitChecks EF G P (proof.commits.toList.zip proof.commitWitnesses.toList)
      (Ni.obsList G s (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen)
          ((Ni.descHeights (Ni.matHeights P rounds)).headD 0)
          (Ni.descHeights (Ni.matHeights P rounds)))
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries
        ((Ni.descHeights (Ni.matHeights P rounds)).headD 0) P.logBlowup P.maxLogArity)) := by
  unfold verifyFri at h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  rw [Ni.bind_ok_of G (Ni.observeList_eq G _ s)] at h
  obtain ⟨-, h⟩ := Ni.ensure_bind_eq_ok G h
  obtain ⟨betas, st1, h1, -⟩ := Ni.bind_eq_ok G h
  exact commitChecks_of_loop G P _ (fun _ _ ↦ rfl) _ _ _ _ h1

end CompStark.Fs

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fs CompStark.Ni Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (K m : ℕ) (S : Setup EF)
  (T : (merkleSpec F).QueryCache)

/-- The permutation commitment read off a proof: with lookups, its cap, `none` unless it has the
size Plonky3's verifier accepts; without lookups, the empty commitment. -/
def permComOf : (b : Bool) → Option (Cap F) → Option (S.permCommit b).Com
  | true, c => c.bind (capVec S.params.capHeight (permLog S))
  | false, _ => some PUnit.unit

/-- The batch's messages of the snapshot protocol read off a proof, every snapshot move `T`: the
main cap and the lookup witness, then (after a snapshot if the lookup challenges squeeze) the
permutation commitment, the terminals and `α`'s (empty) witness, a snapshot, the quotient's cap
and the out-of-domain witness, a snapshot, the claimed values and the batching witness, a snapshot
and FRI's messages; `none` unless the caps have the sizes Plonky3's verifier accepts and the
commitments are one per fold. -/
noncomputable def parse (proof : CompStark.Batch.BatchProof F EF) :
    Option (Messages PUnit (decoded (Coins F K m) (snapCoin S.publicCoin (S.decoder K m)
      (S.layout K m) false) (snapDecoder S.publicCoin (S.decoder K m) (S.layout K m) false))) :=
  (capVec S.params.capHeight S.logTop proof.mainCommit).bind fun tc =>
  (S.permComOf S.hasLookups proof.permutationCommit).bind fun pc =>
  (capVec S.params.capHeight S.logTop proof.quotientCommit).bind fun qc =>
  (parseFri K m S.logTop (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.params T
    proof.fri.finalPoly proof.fri.queryWitness (S.domainSetup.friSchedule S.friHeights)
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) (friSeedB S)
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)).map fun fri =>
  ⟨tc, lookupWitnessOf S.hasLookups S.params.lookupPowBits (proof.lookupWitness.getD 0),
    PUnit.unit, wrapMsgs T (lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits != 0)
    ⟨pc, S.terminalsOf proof, extWitnessOf 0 0, PUnit.unit,
      wrapMsgs T (squeezesFor K (extSamples (EF := EF) 0) != 0)
      ⟨qc, extWitnessOf S.params.oodPowBits proof.oodWitness, PUnit.unit,
        wrapMsgs T (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits) != 0)
          ⟨S.openingsOf proof, extWitnessOf S.params.batchPowBits proof.fri.batchWitness,
            PUnit.unit, fri⟩⟩⟩⟩

/-- The permutation commitment read off a proof, present exactly with lookups, is observed as
Plonky3 observes the proof's permutation commitment, nonempty with lookups, and opens to the
permutation traces under the proof's permutation cap. -/
theorem permCommit_of_permComOf (b : Bool) (c : Option (Cap F)) (pc : (S.permCommit b).Com)
    (h : S.permComOf b c = some pc) (hb : c.isSome = b) :
    (S.permCommit b).observe pc = (c.map capElems).getD [] ∧
      (b = true → (S.permCommit b).observe pc ≠ []) ∧
      (S.permCommit b).open T pc = S.permMessageOf (merkleCache T) (c.getD #[]) := by
  cases b with
  | true =>
    obtain ⟨r, rfl⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨hv, hr⟩ := capOfElems_of_capVec (h : capVec S.params.capHeight (permLog S) r = some pc)
    refine ⟨?_, fun _ ↦ capOfElems_ne_nil pc, ?_⟩
    · change [] ++ capOfElems pc = _
      rw [hv]
      rfl
    · change S.permMessageOf (merkleCache T) pc.toArray = _
      rw [hr]
      rfl
  | false =>
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hb
    subst hb
    exact ⟨rfl, fun h ↦ absurd h (by decide), rfl⟩

local notation "𝕂" => Challenge.Spec EF

variable {S} in
/-- An execution path of the batch from its messages and challenges. -/
def pathOf (Tm : S.TraceMessage) (l : 𝕂 × 𝕂) (P : S.PermMessage) (τ : S.Terminals) (α : 𝕂)
    (Q : S.QuotientMessage) (ζ : 𝕂) (o : S.OpeningsMessage) (a : 𝕂)
    (p : S.friProtocol.tree.ExecutionPath) : S.protocol.tree.ExecutionPath :=
  ⟨Tm, l, P, τ, α, Q, ζ, o, a, p⟩

variable {S} in
theorem pathOf_congr {Tm Tm' : S.TraceMessage} {l l' : 𝕂 × 𝕂} {P P' : S.PermMessage}
    {τ τ' : S.Terminals} {α α' : 𝕂} {Q Q' : S.QuotientMessage} {ζ ζ' : 𝕂}
    {o o' : S.OpeningsMessage} {a a' : 𝕂} {p p' : S.friProtocol.tree.ExecutionPath}
    (h1 : Tm = Tm') (h2 : l = l') (h3 : P = P') (h4 : τ = τ') (h5 : α = α') (h6 : Q = Q')
    (h7 : ζ = ζ') (h8 : o = o') (h9 : a = a') (h10 : p = p') :
    pathOf Tm l P τ α Q ζ o a p = pathOf Tm' l' P' τ' α' Q' ζ' o' a' p' := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- **The selection of a batch proof.** The messages of the decoded snapshot protocol read off a
proof at the admitted lengths `n`, every snapshot move `T`: the lengths, then the batch's
(`Setup.parse`). -/
noncomputable def parse (T : (merkleSpec F).QueryCache) (n : C.Length)
    (proof : CompStark.Batch.BatchProof F EF) :
    Option (Messages PUnit (decoded (Coins F K (C.coinCount EF K))
      (snapCoin (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
        (C.layout EF K (C.coinCount EF K)) true)
      (snapDecoder (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
        (C.layout EF K (C.coinCount EF K)) true))) :=
  ((C.setup EF n).parse K (C.coinCount EF K) T proof).map fun msgs => ⟨T, n, msgs⟩

end CompStark.Iop.Batch.Statement

/-! ### The batch's path -/

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fs CompStark.Ni CompStark.RandomOracle CompStark.Fri
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-- **Plonky3's batch verifier draws the batch's challenges as the snapshot protocol's
completion.** If Plonky3's batch verifier on the answers `answer` accepts a proof of the setup's
instances against the common data `common` with the public values `pis`, its messages read off
the proof (`parse`) open, on the coins of their real chain inputs after the batch's domain
separator and the degree bits, with the public values and the preprocessed commitment observed at
the first squeeze, to the proof's execution path (`proofPath`) on the hashes of the snapshot
`T`. -/
theorem openedPath_parse (S : Setup EF) (answer : (q : Query F) → Answer K q) (hK : 0 < K)
    (hm : squeezesFor K (2 * Challenge.d EF + S.params.numQueries + 1) ≤ m)
    (T : (merkleSpec F).QueryCache) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith (idealOf answer) S.params S.instances common proof
      pis = .ok ())
    (msgs : Messages PUnit (decoded (Coins F K m) (snapCoin S.publicCoin (S.decoder K m)
      (S.layout K m) false) (snapDecoder S.publicCoin (S.decoder K m) (S.layout K m) false)))
    (hp : S.parse K m T proof = some msgs) :
    openedPath (fun r n => streamCoins (m := m) answer r.1 r.2 n) S.publicCoin (S.decoder K m)
        (S.layout K m) false T
        (CompStark.Batch.batchSeedOf EF S.params S.instances common.preprocessed ++
          Ni.coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)))
        (pis.flatten ++ prepDigest common) [] msgs =
      some (S.proofPath (merkleCache T) (idealOf answer) common proof pis) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlw, hood, -, hbc, ⟨st, hfriOk⟩, -, -⟩ :=
    verifyInstancesWith_ok (idealOf answer) S.params S.instances common proof pis h
  obtain ⟨hsize, hshape, hprep, hcs, hcws, hfp, hlsize, hnsize, htsize, hpw, hperm⟩ :=
    shape_of_verifyInstancesWith S (idealOf answer) common proof pis h
  have hD := descHeights_batchRounds S common proof
    (zetaOfB (idealOf answer) S.params S.instances common proof pis) hsize
  have hok := verifyFri_okR (idealOf answer) S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok
  rw [hD, List.headD_cons] at hok
  obtain ⟨hnq, -, -, -, -, -, -, -, hw, -, -⟩ := hok
  have hchecks := commitChecks_of_verifyFriR (idealOf answer) S.params proof.fri _ _ _ _ hfriOk
  rw [hD, List.headD_cons] at hchecks
  have he (bits : ℕ) : squeezesFor K (extSamples (EF := EF) bits) ≤ m :=
    (squeezesFor_mono ((Iop.Setup.extSamples_le bits).trans (by omega))).trans hm
  have hqm : squeezesFor K (querySamples S.params.numQueries S.params.queryPowBits) ≤ m :=
    (squeezesFor_mono ((Iop.Setup.querySamples_le _ _).trans (by omega))).trans hm
  have hmL : squeezesFor K (pairSamples (EF := EF) S.params.lookupPowBits) ≤ m :=
    (squeezesFor_mono ((pairSamples_le _).trans (by omega))).trans hm
  have hd : 0 < Challenge.d EF := (Challenge.params EF).d_pos
  have hqpos : 0 < querySamples S.params.numQueries S.params.queryPowBits := by
    simp only [querySamples]
    split <;> omega
  have hsq (bits : ℕ) : squeezesFor K (extSamples (EF := EF) bits) ≠ 0 :=
    squeezesFor_ne_zero hK (Nat.lt_of_lt_of_le hd (Nat.le_add_right _ _))
  -- the parsed messages
  unfold parse at hp
  obtain ⟨tc, htc, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨pc, hpc, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨qc, hqcv, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨fri, hfri, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨hts, rfl⟩ := capVec_eq_some htc
  obtain ⟨hqs, rfl⟩ := capVec_eq_some hqcv
  have hpp := permCommit_of_permComOf (F := F) (EF := EF) S T S.hasLookups
    proof.permutationCommit pc hpc
  have hobs := (hpp hperm).1
  have hne := (hpp hperm).2.1
  have hopen := (hpp hperm).2.2
  have hqne : capElems proof.quotientCommit ≠ [] :=
    capOfElems_ne_nil (⟨proof.quotientCommit, hqs⟩ : CapOf F S.params.capHeight _)
  have hterm := terminalsElems_terminalsOf S proof htsize fun i ↦ (hpw i).2.2
  -- the lookup challenges
  have hL0 : stateLookupB (idealOf answer) S.params S.instances common proof pis =
      ⟨capOf answer [], CompStark.Batch.batchSeedOf EF S.params S.instances common.preprocessed ++
        Ni.coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++
        ([] ++ capOfElems (⟨proof.mainCommit, hts⟩ :
          CapOf F S.params.capHeight S.logTop)) ++ (pis.flatten ++ prepDigest common), []⟩ := by
    simp only [stateLookupB, Ni.obsExts_eq, Ni.obsList_idealOf_mk, List.nil_append,
      List.append_assoc, prepDigest]
    rfl
  have hlk := lookupRun_idealOf (m := m) answer hK S.params S.instances proof _ hL0 hmL
  -- `α`
  have hterm0 : S.hasLookups = false → S.terminalsElems (F := F) (S.terminalsOf proof) = [] :=
    fun hb ↦ List.eq_nil_of_length_eq_zero (by
      rw [length_terminalsElems, Finset.card_eq_zero.mpr, Nat.zero_mul]
      refine Finset.filter_eq_empty_iff.mpr fun i _ ↦ ?_
      simp only [ne_eq, not_not]
      exact lookups_eq_nil_of S hb i)
  have hα : (stateAlphaB (idealOf answer) S.params S.instances common proof pis).cap =
        capOf answer (if lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0
          then [] else List.replicate
            (lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits - 1) [] ++
            [CompStark.Batch.batchSeedOf EF S.params S.instances common.preprocessed ++
              Ni.coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++
              ([] ++ capOfElems (⟨proof.mainCommit, hts⟩ :
                CapOf F S.params.capHeight S.logTop)) ++ (pis.flatten ++ prepDigest common) ++
              lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) S.hasLookups
                S.params.lookupPowBits
                (lookupWitnessOf S.hasLookups S.params.lookupPowBits
                  (proof.lookupWitness.getD 0))]) ∧
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis).input =
        (if lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0 then
          CompStark.Batch.batchSeedOf EF S.params S.instances common.preprocessed ++
            Ni.coeffs (S.instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) ++
            ([] ++ capOfElems (⟨proof.mainCommit, hts⟩ : CapOf F S.params.capHeight S.logTop)) ++
            lookupWitnessElems (F := F) (EF := EF) (K := K) (m := m) S.hasLookups
              S.params.lookupPowBits
              (lookupWitnessOf S.hasLookups S.params.lookupPowBits (proof.lookupWitness.getD 0))
          else []) ++ (S.permCommit S.hasLookups).observe pc ++
          S.terminalsElems (F := F) (S.terminalsOf proof) ++
          (if lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0 then
            pis.flatten ++ prepDigest common else []) ∧
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis).samples = [] := by
    rw [lookupWitnessElems_lookupWitnessOf, hobs]
    rcases Bool.eq_false_or_eq_true S.hasLookups with hb | hb
    · have hb' : CompStark.Batch.hasLookups S.instances = true := hb
      have hL : lookupSqueezes (EF := EF) K true S.params.lookupPowBits ≠ 0 :=
        squeezesFor_ne_zero hK (by simp only [pairSamples]; omega)
      have hs := hlk.2.2.1 hb'
      have hpne := hne hb
      rw [hobs] at hpne
      have hst : stateAlphaB (idealOf answer) S.params S.instances common proof pis =
          ⟨(Ni.lookupRun (idealOf answer) S.params S.instances proof
            (stateLookupB (idealOf answer) S.params S.instances common proof pis)).2.cap,
            (Ni.lookupRun (idealOf answer) S.params S.instances proof
              (stateLookupB (idealOf answer) S.params S.instances common proof pis)).2.input ++
              (proof.permutationCommit.map capElems).getD [] ++
              Ni.coeffs (proof.lookupTerminals.toList.filterMap id), []⟩ := by
        rw [stateAlphaB, Ni.obsExts_eq, Ni.obsList_idealOf_ne answer _ _ hpne,
          Ni.obsList_idealOf_mk]
      rw [hst, hterm]
      simp only [hb, hL, ↓reduceIte, hs.1, hs.2, List.nil_append, List.append_nil,
        List.append_assoc]
      exact ⟨rfl, trivial, trivial⟩
    · have hb' : CompStark.Batch.hasLookups S.instances = false := hb
      have hs := hlk.2.2.2 hb'
      have hpn : proof.permutationCommit = none := by
        rw [← Option.not_isSome_iff_eq_none, hperm, hb]
        decide
      have ht := hterm0 hb
      rw [hterm] at ht
      have hL : lookupSqueezes (EF := EF) K false S.params.lookupPowBits = 0 := rfl
      have hst : stateAlphaB (idealOf answer) S.params S.instances common proof pis =
          stateLookupB (idealOf answer) S.params S.instances common proof pis := by
        rw [stateAlphaB, hs, hpn, Ni.obsExts_eq, ht]
        rfl
      rw [hst, hL0, hterm, hpn, ht]
      simp only [hb, hL, ↓reduceIte, Bool.false_eq_true, Option.map_none, Option.getD_none,
        List.nil_append, List.append_nil, List.append_assoc]
      exact ⟨trivial, trivial, trivial⟩
  have hA := extDraw_idealOf_of (m := m) answer hK 0 0 _ hα.1 hα.2.1 hα.2.2 (he 0)
  -- `ζ`
  have hζs := Ni.obsList_idealOf_ne answer (Ni.smpExt (EF := EF) (idealOf answer)
    (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2 _ hqne
  have hζin : (Ni.obsList (idealOf answer) (Ni.smpExt (EF := EF) (idealOf answer)
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2
      (capElems proof.quotientCommit)).input =
      [] ++ ([] ++ capOfElems (⟨proof.quotientCommit, hqs⟩ :
        CapOf F S.params.capHeight S.logTop)) ++ [] := by
    rw [hζs]
    change (Ni.smpExt (EF := EF) (idealOf answer) (Ni.chkWit (idealOf answer) 0 0
      (stateAlphaB (idealOf answer) S.params S.instances common proof pis)).2).2.input ++
        capElems proof.quotientCommit = _
    rw [hA.2.2.2, List.nil_append, List.append_nil]
    rfl
  have hZ := extDraw_idealOf_of (m := m) answer hK S.params.oodPowBits proof.oodWitness _
    ((congrArg Sponge.cap hζs).trans hA.2.2.1) hζin (by rw [hζs]) (he _)
  -- the batching challenge
  have hpw' (i : Fin S.k) := And.intro (hpw i).1 (hpw i).2.1
  have hBs : Ni.pcsState (idealOf answer) S.params (CompStark.Batch.batchRounds S.instances common
      proof (zetaOfB (idealOf answer) S.params S.instances common proof pis))
      (Ni.smpExt (EF := EF) (idealOf answer)
        (oodCheckB (EF := EF) (idealOf answer) S.params S.instances common proof pis).2).2 =
      ⟨(Ni.smpExt (EF := EF) (idealOf answer)
        (oodCheckB (EF := EF) (idealOf answer) S.params S.instances common proof pis).2).2.cap,
        (Ni.smpExt (EF := EF) (idealOf answer)
          (oodCheckB (EF := EF) (idealOf answer) S.params S.instances common proof pis).2).2.input
          ++ (pcsSeedB S ++ S.openingsElems (S.openingsOf proof)), []⟩ := by
    rw [Ni.pcsState, Ni.obsOpened_eq, ← Ni.obsList_append,
      claimCounts_batchRounds_eq S common proof hsize hlsize hnsize hshape hprep hpw' hperm,
      ← openingsElems_openingsOfB S common proof _ hsize hlsize hnsize hshape hprep hpw' hperm,
      Ni.obsList_idealOf_ne answer _ _
        (List.append_ne_nil_of_left_ne_nil (Ni.pcsSeed_ne_nil _ _) _)]
    rfl
  have hBin : (Ni.pcsState (idealOf answer) S.params (CompStark.Batch.batchRounds S.instances
      common proof (zetaOfB (idealOf answer) S.params S.instances common proof pis))
      (Ni.smpExt (EF := EF) (idealOf answer)
        (oodCheckB (EF := EF) (idealOf answer) S.params S.instances common proof pis).2).2).input =
      [] ++ (pcsSeedB S ++ S.openingsElems (S.openingsOf proof)) ++ [] := by
    rw [hBs]
    change (Ni.smpExt (EF := EF) (idealOf answer) (Ni.chkWit (idealOf answer) S.params.oodPowBits
      proof.oodWitness _).2).2.input ++ _ = _
    rw [hZ.2.2.2, List.append_nil]
  have hB := extDraw_idealOf_of (m := m) answer hK S.params.batchPowBits proof.fri.batchWitness _
    ((congrArg Sponge.cap hBs).trans hZ.2.2.1) hBin (by rw [hBs]) (he _)
  refine (openedPath_oracle _ _ _ _ T _ _ [] _ _).trans (map_eq_some_of (a := ?a1) ?r1 ?v1)
  case r1 =>
    refine (openedPath_challenge_ite _ _ _ _ T _ _ [] _ _ _ ?hL).trans
      (map_eq_some_of (a := ?a2) ?r2 ?v2)
    case hL =>
      refine hlk.1.trans ?_
      cases hb : CompStark.Batch.hasLookups S.instances
      · rfl
      · exact (Bool.or_eq_true _ _).mpr (Or.inr (hlw hb))
    case r2 =>
      refine (openedPath_wrap_oracle _ _ _ _ _ T _ _ _ _).trans
        ((openedPath_oracle _ _ _ _ T _ _ _ _ _).trans (map_eq_some_of (a := ?a3) ?r3 ?v3))
      case r3 =>
        refine (openedPath_sender _ _ _ _ T _ _ _ _ _).trans (map_eq_some_of (a := ?a4) ?r4 ?v4)
        case r4 =>
          refine (openedPath_challenge _ _ _ _ T _ _ _ _ _ _ _ rfl (hsq 0) rfl).trans
            (map_eq_some_of (a := ?a5) ?r5 ?v5)
          case r5 =>
            refine (openedPath_wrap_oracle _ _ _ _ _ T [] [] _ _).trans
              ((openedPath_oracle _ _ _ _ T [] [] _ _ _).trans (map_eq_some_of (a := ?a6) ?r6 ?v6))
            case r6 =>
              refine (openedPath_challenge _ _ _ _ T _ [] _ _ _ _ _ rfl (hsq _) ?hζ).trans
                (map_eq_some_of (a := ?a7) ?r7 ?v7)
              case r7 =>
                refine (openedPath_wrap_sender _ _ _ _ _ T [] [] _ _).trans
                  ((openedPath_sender _ _ _ _ T [] [] _ _ _).trans
                    (map_eq_some_of (a := ?a8) ?r8 ?v8))
                case r8 =>
                  refine (openedPath_challenge _ _ _ _ T _ [] _ _ _ _ _ rfl (hsq _) ?hA).trans
                    (map_eq_some_of (a := ?a9) ?r9 ?v9)
                  case r9 =>
                    refine openedPath_fri (m := m) answer (S.logN S.top + S.params.logBlowup)
                      (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.params T
                      proof.fri.finalPoly proof.fri.queryWitness hK (he _) hqm hfp
                      (Nat.two_pow_pos _) hqpos (S.domainSetup.friSchedule S.friHeights) _
                      (friSeedB S) _ (stateFriB (idealOf answer) S.params S.instances common proof
                        pis) _ fri ?hcap ?hin hfri hchecks hw
                    case hcap => exact hB.2.2.1
                    case hin => exact hB.2.2.2
                  case v9 => rfl
                  case hA => exact hB.1.trans hbc
                case v8 => rfl
              case v7 => rfl
              case hζ => exact hZ.1.trans hood
            case v6 => rfl
          case v5 => rfl
        case v4 => rfl
      case v3 => rfl
    case v2 => rfl
  case v1 =>
    refine pathOf_congr rfl hlk.2.1 hopen rfl hA.2.1 rfl hZ.2.1 rfl hB.2.1 ?_
    rw [List.map_fst_zip (by rw [Array.length_toList, Array.length_toList, hcs, hcws])]
    rfl

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fs CompStark.Ni CompStark.RandomOracle CompStark.Fri OracleComp
open OracleSpec Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF]

/-- The statement's execution path at the lengths `n` with the batch's path there. -/
def pathAt (n : C.Length) (p : (C.setup EF n).protocol.tree.ExecutionPath) :
    (C.protocol EF).tree.ExecutionPath :=
  ⟨n, p⟩

variable {C EF} {K : ℕ}

/-- The batch's domain separator and the degree bits as the batch verifier observes them, on
common data with a preprocessed commitment exactly when some instance has preprocessed columns:
the layout's first elements. -/
theorem seed_eq (n : C.Length) (common : CompStark.Batch.Common F)
    (hprep : common.preprocessed.isSome =
      (C.setup EF n).instances.any (0 < ·.air.preprocessedWidth)) :
    CompStark.Batch.batchSeedOf EF (C.setup EF n).params (C.setup EF n).instances
        common.preprocessed ++
        Ni.coeffs ((C.setup EF n).instances.map fun I ↦ (Ext.ofBase (I.logN : F) : EF)) =
      C.batchSeed EF ++ C.lengthElems EF n := by
  rw [batchSeedOf_eq (C.setup EF n) common hprep, batchSeedS_setupAt]
  congr 1
  rw [lengthElems, extsElems, Iop.Batch.Setup.instances, List.map_ofFn, Ni.coeffs,
    List.ofFn_eq_map, List.ofFn_eq_map, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  exact ((congrArg extElems (Challenge.toSpec_ofBase' (EF := EF) _)).symm.trans
    (extElems_toSpec _)).symm

end CompStark.Iop.Batch.Statement

/-! ### The selection exists on an accepted proof -/

namespace CompStark.Fs
open CompStark.Stark CompStark.Fri

/-- Plonky3's schedule with inputs folds by Plonky3's arities of the heights. -/
theorem arities_plonky3_heights (maxLogArity logFinal : ℕ) : ∀ (fuel n : ℕ) (heights : List ℕ),
    Iop.scheduleArities (Fri.Interaction.Schedule.plonky3 maxLogArity logFinal fuel n heights) =
      foldSchedule maxLogArity logFinal fuel (n :: heights)
  | 0, _, _ => rfl
  | fuel + 1, n, heights => by
    by_cases hfin : n ≤ logFinal
    · simp only [Fri.Interaction.Schedule.plonky3, hfin, ↓reduceIte, Iop.scheduleArities,
        foldSchedule]
    have ih := arities_plonky3_heights maxLogArity logFinal fuel
    match heights with
    | [] =>
      simp only [Fri.Interaction.Schedule.plonky3, hfin, ↓reduceIte, Iop.scheduleArities,
        foldSchedule, Fri.Interaction.Schedule.logArity, List.headD_nil, List.head?_nil,
        reduceCtorEq, ih]
    | m :: rest =>
      rw [Ni.FriRounds.foldSchedule_cons _ _ _ _ _ _ hfin]
      simp only [Fri.Interaction.Schedule.plonky3, hfin, ↓reduceIte]
      by_cases hm : m = n - Fri.Interaction.Schedule.logArity maxLogArity logFinal n (m :: rest)
      · have hm' : m = n - Sound.FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest) := hm
        rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hm')]
        simp only [Iop.scheduleArities, ih]
        rfl
      · have hm' : ¬ m = n - Sound.FriGame.Rounds.logArity maxLogArity logFinal n (m :: rest) := hm
        rw [ite_eq_right_of_eq_false _ _ (eq_false hm), ite_eq_right_of_eq_false _ _ (eq_false hm')]
        simp only [Iop.scheduleArities, ih]
        rfl

end CompStark.Fs

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fs CompStark.Ni CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- An accepted batch proof's caps have the sizes Plonky3's verifier accepts: the main and
quotient commitments' that of the tallest instance's tree, the permutation commitment's that of
the tallest instance's with lookups, and fold `i`'s that of its tree; and every instance's
extension is at least as tall as the main commitment's cap. -/
theorem caps_of_verifyInstancesWith (S : Setup EF) (H : Primitives F Id)
    (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith H S.params S.instances common proof pis = .ok ()) :
    proof.mainCommit.size = 2 ^ min S.params.capHeight S.logTop ∧
      proof.quotientCommit.size = 2 ^ min S.params.capHeight S.logTop ∧
      (∀ root ∈ proof.permutationCommit, root.size = 2 ^ min S.params.capHeight (permLog S)) ∧
      (∀ i : Fin S.k, min S.params.capHeight S.logTop ≤ S.logN i + S.params.logBlowup) ∧
      ∀ i < S.friArities.length, (proof.fri.commits.toList.getD i #[]).size =
        2 ^ min S.params.capHeight (friDepthB S i) := by
  obtain ⟨hsize, -, hlsize, hnsize, -, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyInstancesWith_ok H S.params S.instances common proof pis h
  obtain ⟨-, hshape, -⟩ := shape_of_verifyInstancesWith S H common proof pis h
  rw [length_instances] at hsize hlsize hnsize
  have hD := descHeights_batchRounds S common proof
    (zetaOfB H S.params S.instances common proof pis) hsize
  have hok' := verifyFri_okR H S.params proof.fri _ _ _ _ hfriOk
  dsimp only at hok'
  rw [hD, List.headD_cons] at hok'
  obtain ⟨hq0, -, -, -, hfolds, -, -, -, -, hcrlen, hq⟩ := hok'
  obtain ⟨hround, hfold⟩ := size_caps_of_queryOkR _ _ _ _ _ _ _ _ _ _ _ _ _ hcrlen
    (by rw [Array.length_toList]; exact hfolds) (hq 0 hq0)
  rw [batchRounds_cases] at hround
  obtain ⟨-, hmsz, hmfit⟩ := hround _ (List.mem_append_left _ (List.mem_append_left _
    List.mem_cons_self))
  obtain ⟨-, hqsz, -⟩ := hround _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hlbM := logBatch_mainMats S proof (zetaOfB H S.params S.instances common proof pis) hsize
  have hlbQ := logBatch_quotMats S proof (zetaOfB H S.params S.instances common proof pis) hsize
    fun i ↦ (openedShapeOk_spec (hshape i)).2.2.1.trans
      (congrArg (2 ^ ·) (logChunks_eq S i).symm)
  dsimp only at hlbM hlbQ hmsz hmfit hqsz
  rw [hlbM] at hmsz hmfit
  rw [hlbQ] at hqsz
  refine ⟨hmsz, hqsz, fun root hroot ↦ ?_, fun i ↦ ?_, hfold⟩
  · rw [Option.mem_def] at hroot
    obtain ⟨-, hpsz, -⟩ := hround _ (List.mem_append_right _ (by
      rw [permRounds, hroot]; exact List.mem_cons_self))
    rwa [logBatch_permMats S proof _ hlsize hnsize] at hpsz
  · change ∀ dp ∈ mainMats S proof (zetaOfB H S.params S.instances common proof pis), _ at hmfit
    rw [mainMats_eq S proof _ hsize] at hmfit
    exact hmfit _ (List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)

/-- **An accepted proof has a selection.** Plonky3's batch verifier on any primitives accepts a
proof of the setup's instances only if its messages of the snapshot protocol can be read off
it. -/
theorem isSome_parse (S : Setup EF) (K m : ℕ) (T : (merkleSpec F).QueryCache)
    (H : Primitives F Id) (common : CompStark.Batch.Common F)
    (proof : CompStark.Batch.BatchProof F EF) (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith H S.params S.instances common proof pis = .ok ()) :
    (S.parse K m T proof).isSome = true := by
  obtain ⟨hmsz, hqsz, hpsz, -, hfsz⟩ := S.caps_of_verifyInstancesWith H common proof pis h
  obtain ⟨-, -, -, hcs, hcws, -, -, -, -, -, hperm⟩ :=
    shape_of_verifyInstancesWith S H common proof pis h
  have har : Iop.scheduleArities (S.domainSetup.friSchedule S.friHeights) = S.friArities := by
    rw [Iop.Setup.friSchedule, arities_plonky3_heights, Nat.add_comm S.params.logFinalPolyLen]
    rfl
  have hfit : CapsFit F S.params.capHeight (S.domainSetup.friSchedule S.friHeights)
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList) := by
    refine capsFit_of_sizes _ _ _ ?_ fun i hi ↦ ?_
    · rw [har, List.length_zip, Array.length_toList, Array.length_toList, hcs, hcws,
        Nat.min_self]
    · have hi' : i < proof.fri.commits.toList.length := by
        rw [List.length_zip] at hi
        omega
      have hc := hfsz i (by rw [Array.length_toList] at hi'; rw [← hcs]; exact hi')
      rw [List.getD_eq_getElem _ _ hi'] at hc
      rw [List.getElem_zip, hc, har]
      rfl
  have hfri := isSome_parseFri K m S.logTop (2 ^ S.params.logFinalPolyLen) S.params.numQueries
    S.params T proof.fri.finalPoly proof.fri.queryWitness (S.domainSetup.friSchedule S.friHeights)
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) (friSeedB S) _ hfit
  have hpc : (S.permComOf S.hasLookups proof.permutationCommit).isSome = true := by
    revert hperm hpsz
    cases S.hasLookups with
    | false => exact fun _ _ ↦ rfl
    | true =>
      intro hpsz hperm
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hperm
      rw [hr]
      change (capVec S.params.capHeight (permLog S) r).isSome = true
      simp only [capVec, hpsz r hr, ↓reduceDIte, Option.isSome_some]
  obtain ⟨pc, hpc'⟩ := Option.isSome_iff_exists.mp hpc
  obtain ⟨fr, hfr⟩ := Option.isSome_iff_exists.mp hfri
  unfold parse
  simp only [capVec, hmsz, hqsz, ↓reduceDIte, Option.bind_some, hpc', hfr]
  rfl

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fs

variable {F : Type} [BaseField F] {C : Statement F} {EF : Type} [Challenge F EF]

/-- **An accepted proof has a selection**: Plonky3's batch verifier on any primitives accepts a
proof of the instances at the admitted lengths `n` only if its messages of the snapshot protocol
can be read off it. -/
theorem isSome_parse (K : ℕ) (T : (merkleSpec F).QueryCache) (H : Primitives F Id)
    (n : C.Length) (common : CompStark.Batch.Common F) (proof : CompStark.Batch.BatchProof F EF)
    (pis : List (List F))
    (h : CompStark.Batch.verifyInstancesWith H C.params (C.setup EF n).instances common proof pis =
      .ok ()) :
    (C.parse EF K T n proof).isSome = true := by
  have hs := (C.setup EF n).isSome_parse K (C.coinCount EF K) T H common proof pis h
  unfold parse
  revert hs
  cases (C.setup EF n).parse K (C.coinCount EF K) T proof
  · exact id
  · exact fun _ ↦ rfl

end CompStark.Iop.Batch.Statement
