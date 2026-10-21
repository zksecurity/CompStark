/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Bcs
public import CompStark.Ni.Parse

/-! # The run's challenges are the oracle's answers

On the ideal primitives of an answer table (`idealOf answer`), the challenges of the verifier's
run (`alphaOf`, `zetaOf`, `batchOf`, `betasOf`, `powSampleOf`, `querySampleOf`) are read off the
answers to the duplex calls of the proof's transcript schedule (`inputs`, `keyAt`), as `Ni/Parse`
reads them (`extAt`, `challengeOffset`): every round of the schedule observes something, so every
squeeze after it duplexes once, and the round's challenges are the answer's first samples
(`challenges_idealOf`; an accepted proof observes something in every round, `nonempty_of_verify`).
The design's `Iop.committedTrace` is `traceWords` on the log's cache (`committedTrace_eq`).
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} {K : Nat}

/-! ### On any primitives -/

theorem sampleStates_succ (H : Primitives F Id) (s : H.State) :
    ∀ j, sampleStates H s (j + 1) = sampleStates H (H.sample s).2 j
  | 0 => rfl
  | j + 1 => by rw [sampleStates, sampleStates_succ H s j]; rfl

theorem obsList_append (H : Primitives F Id) (s : H.State) (a b : List F) :
    obsList H s (a ++ b) = obsList H (obsList H s a) b := List.foldl_append

theorem digest_toList_ne_nil (d : Digest F) : d.toList ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [Vector.length_toList, List.length_nil] at this
  exact absurd this (by decide)

variable [BaseField F] {EF : Type} [Challenge F EF] (answer : (q : Query F) → Answer K q)

/-! ### The ideal challenger on an answer table -/

theorem obsList_idealOf (s : Sponge F) (hs : s.samples = []) (xs : List F) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  induction xs generalizing s with
  | nil => obtain ⟨c, i, l⟩ := s; dsimp only at hs; subst hs; simp only [obsList,
      List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    rw [obsList, List.foldl_cons, ← obsList, ih _ rfl]
    simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem obsList_idealOf_mk (cap : Digest F) (input xs : List F) :
    obsList (idealOf answer) ⟨cap, input, []⟩ xs = ⟨cap, input ++ xs, []⟩ :=
  obsList_idealOf answer _ rfl xs

theorem obsList_idealOf_ne (s : Sponge F) (xs : List F) (hxs : xs ≠ []) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  rw [obsList, List.foldl_cons, ← obsList, obsList_idealOf answer _ rfl]
  simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem sample_idealOf_cons (cap : Digest F) (input : List F) (x : F) (rest : List F) :
    (idealOf answer).sample ⟨cap, input, x :: rest⟩ = (x, ⟨cap, input, rest⟩) := rfl

theorem sample_idealOf_nil (cap : Digest F) (input : List F) :
    (idealOf answer).sample ⟨cap, input, []⟩ =
      ((answer (.duplex cap input)).2.toList.headD 0,
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩) := rfl

/-- Sampling `n` elements with `n` samples left or more takes them. -/
theorem smpList_idealOf (cap : Digest F) (input : List F) :
    ∀ (n : Nat) (l : List F), n ≤ l.length →
      smpList (idealOf answer) ⟨cap, input, l⟩ n = (l.take n, ⟨cap, input, l.drop n⟩)
  | 0, _, _ => rfl
  | n + 1, x :: rest, h => by
    show (x :: (smpList (idealOf answer) ⟨cap, input, rest⟩ n).1,
      (smpList (idealOf answer) ⟨cap, input, rest⟩ n).2) = _
    rw [smpList_idealOf cap input n rest (by simp only [List.length_cons] at h; omega)]
    rfl

/-- An extension sample with `d` samples left or more takes them. -/
theorem smpExt_idealOf_pop (cap : Digest F) (input : List F) (l : List F)
    (h : Challenge.d EF ≤ l.length) :
    smpExt (idealOf answer) ⟨cap, input, l⟩ =
      ((Challenge.ofCoeffs (l.take (Challenge.d EF)) : EF),
        ⟨cap, input, l.drop (Challenge.d EF)⟩) := by
  rw [smpExt, smpList_idealOf answer cap input _ l h]

/-- An extension sample from no samples duplexes and takes the answer's first `d` samples. -/
theorem smpExt_idealOf_nil (hK : Challenge.d EF ≤ K) (cap : Digest F) (input : List F) :
    Challenge.toSpec (smpExt (idealOf answer) ⟨cap, input, []⟩ : EF × Sponge F).1 =
        extAt (answer (.duplex cap input)).2 0 ∧
      (smpExt (EF := EF) (idealOf answer) ⟨cap, input, []⟩).2 =
        ⟨(answer (.duplex cap input)).1, [],
          (answer (.duplex cap input)).2.toList.drop (Challenge.d EF)⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, Challenge.d EF = m + 1 :=
    ⟨Challenge.d EF - 1, Nat.succ_pred_eq_of_pos (Challenge.params EF).d_pos |>.symm⟩
  have hlen : m ≤ (answer (.duplex cap input)).2.toList.tail.length := by
    rw [List.length_tail, Vector.length_toList, ← Nat.add_sub_cancel m 1, ← hm]
    exact Nat.sub_le_sub_right hK 1
  have hs : smpExt (idealOf answer) ⟨cap, input, []⟩ =
      ((Challenge.ofCoeffs ((answer (.duplex cap input)).2.toList.take (Challenge.d EF)) : EF),
        ⟨(answer (.duplex cap input)).1, [],
          (answer (.duplex cap input)).2.toList.drop (Challenge.d EF)⟩) := by
    rw [smpExt, hm, smpList, sample_idealOf_nil]
    dsimp only
    rw [smpList_idealOf answer _ _ m _ hlen]
    rcases hL : (answer (.duplex cap input)).2.toList with _ | ⟨x, rest⟩
    · have := congrArg List.length hL
      rw [Vector.length_toList, List.length_nil] at this
      omega
    · rfl
  rw [hs]
  refine ⟨?_, rfl⟩
  have h := toSpec_ofCoeffs_drop (EF := EF) (answer (.duplex cap input)).2 0
  rwa [List.drop_zero] at h

theorem sampleStates_idealOf (cap : Digest F) (input : List F) :
    ∀ (l : List F) (j : Nat), j ≤ l.length →
      sampleStates (idealOf answer) ⟨cap, input, l⟩ j = ⟨cap, input, l.drop j⟩
  | _, 0, _ => rfl
  | l, j + 1, hj => by
    rw [sampleStates, sampleStates_idealOf cap input l j (by omega)]
    obtain ⟨x, rest, hx⟩ := List.exists_cons_of_length_pos (l := l.drop j)
      (by rw [List.length_drop]; omega)
    rw [hx, sample_idealOf_cons, ← List.drop_drop, hx, List.drop_one, List.tail_cons]

/-! ### Observations as lists -/

theorem coeffs_append (a b : List EF) : coeffs (a ++ b) = coeffs a ++ coeffs b :=
  List.flatMap_append

theorem obsExts_eq (H : Primitives F Id) (s : H.State) (xs : List EF) :
    obsExts H s xs = obsList H s (coeffs xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [obsExts, List.foldl_cons, ← obsExts, ih, show x :: xs = [x] ++ xs from rfl,
      coeffs_append, obsList_append,
      show coeffs [x] = Ext.coeffs x from List.append_nil _]
    rfl

theorem obsPts_eq (H : Primitives F Id) (pts : List (EF × List EF)) (s : H.State) :
    pts.foldl (fun s p ↦ obsExts H s p.2) s = obsList H s (coeffs (pts.flatMap (·.2))) := by
  induction pts generalizing s with
  | nil => rfl
  | cons p pts ih => rw [List.foldl_cons, ih, obsExts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsMats_eq (H : Primitives F Id) (mats : List (Domain F × List (EF × List EF)))
    (s : H.State) :
    mats.foldl (fun s m ↦ m.2.foldl (fun s p ↦ obsExts H s p.2) s) s =
      obsList H s (coeffs (mats.flatMap fun m ↦ m.2.flatMap (·.2))) := by
  induction mats generalizing s with
  | nil => rfl
  | cons m mats ih => rw [List.foldl_cons, ih, obsPts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsOpened_eq (H : Primitives F Id) (s : H.State) (rounds : List (Round F EF)) :
    obsOpened H s rounds = obsList H s (coeffs (roundValues rounds)) := by
  induction rounds generalizing s with
  | nil => rfl
  | cons r rounds ih =>
    rw [obsOpened, List.foldl_cons, ← obsOpened, ih, obsMats_eq,
      show roundValues (r :: rounds) = r.2.flatMap (fun m ↦ m.2.flatMap (·.2)) ++
        roundValues rounds from List.flatMap_cons, coeffs_append, obsList_append]

/-- An accepted proof opens values and has a final polynomial. -/
theorem nonempty_of_verify (S : Iop.Setup EF) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN) (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    openedValues proof.opened ≠ [] ∧ proof.fri.finalPoly.toList ≠ [] := by
  obtain ⟨-, -, hqc, hq4, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyWith_ok H S.params S.air vk proof pis h
  obtain ⟨-, hb, hh, -⟩ := friHyps S vk proof (zetaOf H S.params S.air vk proof pis) hdb
  obtain ⟨-, -, -, -, hfp, -⟩ := verifyFri_ok H S.params proof.fri _ _ _ hb hh _ _ hfriOk
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · have hpos : 0 < proof.opened.quotientChunks.size := by rw [hqc]; exact Nat.two_pow_pos _
    have h4 := hq4 _ (Array.getElem_mem hpos)
    simp only [openedValues, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at he
    have := he.1.1.2 _ (Array.getElem_mem_toList hpos)
    rw [← Array.length_toList, this, List.length_nil] at h4
    exact (Challenge.params EF).d_pos.ne h4
  · have := congrArg List.length he
    rw [Array.length_toList, hfp, List.length_nil] at this
    exact absurd this (Nat.two_pow_pos _).ne'

/-- The committed trace of the design (`Iop.committedTrace`) is the extracted trace words on the
log's cache. -/
theorem committedTrace_eq (S : Iop.Setup EF) (log : QueryLog (spec F S.streamLen))
    (proof : Proof F EF) :
    Iop.committedTrace S log proof = traceWords S (Iop.logCache log) proof := by
  funext j z
  simp only [Iop.committedTrace, traceWords, committedColumn, leafRow]
  split <;> rename_i h <;> rw [h]
  · rfl
  · simp only [Option.getD_none, List.getD_nil]

/-! ### Round by round -/

section Rounds
variable (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
  (pis : List F)

/-- A round with grinding: after observing `input`, check the grinding witness and sample an
extension element, which is the round's answer at the grinding offset. -/
theorem grindRound_idealOf (hK : Challenge.d EF + 1 ≤ K) (blocks : List (List F)) (r : Nat)
    (input : List F) (bits : Nat) (w : F)
    (hr : blocks.getD r [] = input ++ witnessInput bits w) :
    let b := smpExt (EF := EF) (idealOf answer)
      (chkWit (idealOf answer) bits w ⟨capAt answer blocks r, input, []⟩).2
    Challenge.toSpec b.1 = extAt (answer (keyAt answer blocks r)).2 (challengeOffset bits) ∧
      ∃ l, b.2 = ⟨capAt answer blocks (r + 1), [], l⟩ := by
  intro b
  simp only [b]
  by_cases hb : bits = 0
  · simp only [witnessInput, hb, ↓reduceIte, List.append_nil] at hr
    have h := smpExt_idealOf_nil (EF := EF) answer (by omega) (capAt answer blocks r)
      (blocks.getD r [])
    simp only [chkWit, hb, ↓reduceIte, challengeOffset]
    rw [← hr]
    exact ⟨h.1, _, h.2⟩
  · simp only [witnessInput, hb, ↓reduceIte] at hr
    have hst : (chkWit (idealOf answer) bits w ⟨capAt answer blocks r, input, []⟩).2 =
        ⟨(answer (keyAt answer blocks r)).1, [],
          (answer (keyAt answer blocks r)).2.toList.tail⟩ := by
      rw [chkWit, ite_eq_right hb]
      show ((idealOf answer).sample ⟨capAt answer blocks r, input ++ [w], []⟩).2 = _
      rw [sample_idealOf_nil, ← hr]
      rfl
    rw [hst]
    have hlen : Challenge.d EF ≤ (answer (keyAt answer blocks r)).2.toList.tail.length := by
      rw [List.length_tail, Vector.length_toList]; omega
    rw [show challengeOffset bits = 1 by simp only [challengeOffset, hb, ↓reduceIte],
      smpExt_idealOf_pop answer _ _ _ hlen, ← List.drop_one]
    exact ⟨toSpec_ofCoeffs_drop _ 1, _, rfl⟩

theorem stateAlpha_idealOf :
    stateAlpha (idealOf answer) P A vk proof pis =
      ⟨capAt answer (inputs P A vk pis proof) 0, (inputs P A vk pis proof).getD 0 [], []⟩ := by
  unfold stateAlpha
  rw [show (idealOf answer).init = ⟨initCap, [], []⟩ from rfl]
  simp only [obsList_idealOf_mk, List.nil_append]
  rfl

theorem alpha_idealOf (hK : Challenge.d EF ≤ K) :
    Challenge.toSpec (alphaOf (idealOf answer) P A vk proof pis) =
      extAt (answer (keyAt answer (inputs P A vk pis proof) 0)).2 0 ∧
    (smpExt (EF := EF) (idealOf answer) (stateAlpha (idealOf answer) P A vk proof pis)).2 =
      ⟨capAt answer (inputs P A vk pis proof) 1, [],
        (answer (keyAt answer (inputs P A vk pis proof) 0)).2.toList.drop (Challenge.d EF)⟩ := by
  rw [alphaOf, stateAlpha_idealOf answer P]
  exact smpExt_idealOf_nil answer hK _ _

theorem zeta_idealOf (hK : Challenge.d EF + 1 ≤ K) :
    Challenge.toSpec (zetaOf (idealOf answer) P A vk proof pis) =
      extAt (answer (keyAt answer (inputs P A vk pis proof) 1)).2 (challengeOffset P.oodPowBits) ∧
    ∃ l, (smpExt (EF := EF) (idealOf answer) (oodCheck (EF := EF) (idealOf answer) P A vk proof
      pis).2).2 = ⟨capAt answer (inputs P A vk pis proof) 2, [], l⟩ := by
  have hst : obsList (idealOf answer) (smpExt (EF := EF) (idealOf answer)
      (stateAlpha (idealOf answer) P A vk proof pis)).2 proof.quotientCommit.toList =
      ⟨capAt answer (inputs P A vk pis proof) 1, proof.quotientCommit.toList, []⟩ := by
    rw [(alpha_idealOf answer P A vk proof pis (by omega)).2,
      obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
    rfl
  have h := grindRound_idealOf (EF := EF) answer hK (inputs P A vk pis proof) 1
    proof.quotientCommit.toList P.oodPowBits proof.oodWitness (by
      simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some])
  rw [← hst] at h
  exact h

theorem batch_idealOf (hK : Challenge.d EF + 1 ≤ K) (htn : traceNextOk A proof.opened = true)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true) :
    Challenge.toSpec (batchOf (idealOf answer) P A vk proof pis) =
      extAt (answer (keyAt answer (inputs P A vk pis proof) 2)).2 (challengeOffset P.batchPowBits) ∧
    ∃ l, stateFri (idealOf answer) P A vk proof pis =
      ⟨capAt answer (inputs P A vk pis proof) 3, [], l⟩ := by
  obtain ⟨-, l, hl⟩ := zeta_idealOf answer P A vk proof pis hK
  have hst : pcsState (idealOf answer) P
      (openingRounds A vk proof (zetaOf (idealOf answer) P A vk proof pis))
      (smpExt (EF := EF) (idealOf answer) (oodCheck (EF := EF) (idealOf answer) P A vk proof
        pis).2).2 =
      ⟨capAt answer (inputs P A vk pis proof) 2, DomainSeparator.pcsSeed F EF
        (pcsCounts proof.opened) P.batchPowBits ++ coeffs (openedValues proof.opened), []⟩ := by
    rw [hl, pcsState, obsOpened_eq, roundValues_openingRounds A vk proof _ htn hshape,
      claimCounts_openingRounds A vk proof _ htn hshape,
      obsList_idealOf_ne answer _ _ (pcsSeed_ne_nil _ _), obsList_idealOf answer _ rfl]
    rfl
  have h := grindRound_idealOf (EF := EF) answer hK (inputs P A vk pis proof) 2
    (DomainSeparator.pcsSeed F EF (pcsCounts proof.opened) P.batchPowBits ++
      coeffs (openedValues proof.opened)) P.batchPowBits proof.fri.batchWitness (by
      simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some])
  rw [← hst] at h
  exact h

/-- A fold round: observe the commitment after `pre` and the witness, check the grinding sample,
and sample `β`, which is the round's answer at the grinding offset. -/
theorem foldRound_idealOf (hK : Challenge.d EF + 1 ≤ K) (blocks : List (List F)) (r : Nat)
    (pre rest : List F) (c : Digest F) (w : F)
    (hr : blocks.getD r [] = pre ++ c.toList ++ witnessInput P.commitPowBits w) :
    let b := smpExt (EF := EF) (idealOf answer) (chkWit (idealOf answer) P.commitPowBits w
      (obsList (idealOf answer) ⟨capAt answer blocks r, pre, rest⟩ c.toList)).2
    Challenge.toSpec b.1 = extAt (answer (keyAt answer blocks r)).2
      (challengeOffset P.commitPowBits) ∧
    ∃ l, b.2 = ⟨capAt answer blocks (r + 1), [], l⟩ := by
  intro b
  simp only [b]
  rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil c)]
  exact grindRound_idealOf answer hK blocks r _ _ w hr

theorem commitReplay_idealOf (hK : Challenge.d EF + 1 ≤ K) (blocks : List (List F)) :
    ∀ (cws : List (Digest F × F)) (r : Nat) (pre rest : List F),
      (∀ i (hi : i < cws.length), blocks.getD (r + i) [] =
        seedAt pre i ++ cws[i].1.toList ++ witnessInput P.commitPowBits cws[i].2) →
      (commitReplay (EF := EF) (idealOf answer) P cws ⟨capAt answer blocks r, pre, rest⟩).1.length =
          cws.length ∧
        (∀ i < cws.length, Challenge.toSpec
          ((commitReplay (EF := EF) (idealOf answer) P cws
            ⟨capAt answer blocks r, pre, rest⟩).1.getD i 0) =
            extAt (answer (keyAt answer blocks (r + i))).2 (challengeOffset P.commitPowBits)) ∧
        ∃ l, (commitReplay (EF := EF) (idealOf answer) P cws
          ⟨capAt answer blocks r, pre, rest⟩).2 =
          ⟨capAt answer blocks (r + cws.length), seedAt pre cws.length, l⟩
  | [], r, pre, rest, _ => ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _), rest, rfl⟩
  | (c, w) :: cws, r, pre, rest, hr => by
    obtain ⟨hβ, l, hl⟩ := foldRound_idealOf answer P hK blocks r pre rest c w (hr 0 (by simp))
    have ih := commitReplay_idealOf hK blocks cws (r + 1) [] l (fun i hi ↦ by
      rw [show r + 1 + i = r + (i + 1) by omega]
      have := hr (i + 1) (by simp only [List.length_cons]; omega)
      simpa only [seedAt, Nat.add_one_ne_zero, ↓reduceIte, ite_self,
        List.getElem_cons_succ] using this)
    simp only [commitReplay, hl] at ih ⊢
    obtain ⟨ih1, ih2, l', hl'⟩ := ih
    refine ⟨by rw [List.length_cons, ih1, List.length_cons], fun i hi ↦ ?_, l', ?_⟩
    · cases i with
      | zero => exact hβ
      | succ i =>
        rw [List.getD_cons_succ, ih2 i (by simp only [List.length_cons] at hi; omega),
          show r + 1 + i = r + (i + 1) by omega]
    · rw [hl', List.length_cons, show r + 1 + cws.length = r + (cws.length + 1) by omega]
      simp only [seedAt, Nat.add_one_ne_zero, ↓reduceIte, ite_self]

theorem sample_drop_idealOf (cap : Digest F) (input : List F) (l : List F) (j : Nat)
    (hj : j < l.length) :
    ((idealOf answer).sample ⟨cap, input, l.drop j⟩).1 = l.getD j 0 := by
  rw [List.drop_eq_getElem_cons hj, sample_idealOf_cons, List.getD_eq_getElem _ _ hj]

/-- The query round: observe the final polynomial after `pre` and the witness; the grinding
sample is the round's first answered sample, and query `j`'s sample the one at the grinding
offset plus `j`. -/
theorem queryRound_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K) (blocks : List (List F))
    (r : Nat) (pre rest : List F) (hfp : proof.fri.finalPoly.toList ≠ [])
    (hr : blocks.getD r [] = pre ++ coeffs proof.fri.finalPoly.toList ++
      witnessInput P.queryPowBits proof.fri.queryWitness) :
    let qs := obsExts (idealOf answer) ⟨capAt answer blocks r, pre, rest⟩ proof.fri.finalPoly.toList
    (P.queryPowBits ≠ 0 →
      ((idealOf answer).sample ((idealOf answer).observe qs proof.fri.queryWitness)).1 =
        (answer (keyAt answer blocks r)).2.toList.getD 0 0) ∧
    ∀ j < P.numQueries, ((idealOf answer).sample (sampleStates (idealOf answer)
      (chkWit (idealOf answer) P.queryPowBits proof.fri.queryWitness qs).2 j)).1 =
        (answer (keyAt answer blocks r)).2.toList.getD (challengeOffset P.queryPowBits + j) 0 := by
  intro qs
  have hqs : qs = ⟨capAt answer blocks r, pre ++ coeffs proof.fri.finalPoly.toList, []⟩ := by
    simp only [qs]
    rw [obsExts_eq, obsList_idealOf_ne answer _ _ (coeffs_ne_nil hfp)]
  have hlen :
      P.numQueries + Challenge.d EF + 1 ≤ (answer (keyAt answer blocks r)).2.toList.length := by
    rw [Vector.length_toList]; exact hK
  have htail : ∀ j < P.numQueries, sampleStates (idealOf answer)
      ⟨(answer (keyAt answer blocks r)).1, [], (answer (keyAt answer blocks r)).2.toList.tail⟩ j =
      ⟨(answer (keyAt answer blocks r)).1, [],
        (answer (keyAt answer blocks r)).2.toList.tail.drop j⟩ := fun j hj ↦
    sampleStates_idealOf answer _ _ _ j (by rw [List.length_tail]; omega)
  have hhead : ∀ j < P.numQueries, ((idealOf answer).sample ⟨(answer (keyAt answer blocks r)).1,
      [], (answer (keyAt answer blocks r)).2.toList.tail.drop j⟩).1 =
      (answer (keyAt answer blocks r)).2.toList.getD (1 + j) 0 := fun j hj ↦ by
    rw [sample_drop_idealOf answer _ _ _ _ (by rw [List.length_tail]; omega)]
    obtain ⟨x, l, hx⟩ := List.exists_cons_of_length_pos
      (l := (answer (keyAt answer blocks r)).2.toList) (by omega)
    rw [hx, List.tail_cons, Nat.add_comm, List.getD_cons_succ]
  by_cases hb : P.queryPowBits = 0
  · simp only [witnessInput, hb, ↓reduceIte, List.append_nil] at hr
    have hw : (chkWit (idealOf answer) P.queryPowBits proof.fri.queryWitness qs).2 =
        ⟨capAt answer blocks r, blocks.getD r [], []⟩ := by
      rw [chkWit, ite_eq_left_of_eq_true _ _ (eq_true hb), hqs, hr]
    refine ⟨fun h ↦ absurd hb h, fun j hj ↦ ?_⟩
    rw [hw, show challengeOffset P.queryPowBits = 0 by simp only [challengeOffset, hb,
      ↓reduceIte], Nat.zero_add]
    cases j with
    | zero =>
      show ((idealOf answer).sample ⟨capAt answer blocks r, blocks.getD r [], []⟩).1 = _
      rw [sample_idealOf_nil]
      obtain ⟨x, l, hx⟩ := List.exists_cons_of_length_pos
        (l := (answer (keyAt answer blocks r)).2.toList) (by omega)
      change (answer (keyAt answer blocks r)).2.toList.headD 0 = _
      rw [hx, List.headD_cons, List.getD_cons_zero]
    | succ j =>
      rw [sampleStates_succ, sample_idealOf_nil]
      exact (htail j (by omega)) ▸ (hhead j (by omega)).trans (by rw [Nat.add_comm])
  · simp only [witnessInput, hb, ↓reduceIte] at hr
    have hobs : (idealOf answer).observe qs proof.fri.queryWitness =
        ⟨capAt answer blocks r, blocks.getD r [], []⟩ := by rw [hqs, hr]
    have hw : (chkWit (idealOf answer) P.queryPowBits proof.fri.queryWitness qs).2 =
        ⟨(answer (keyAt answer blocks r)).1, [],
          (answer (keyAt answer blocks r)).2.toList.tail⟩ := by
      rw [chkWit, ite_eq_right hb]
      show ((idealOf answer).sample ((idealOf answer).observe qs proof.fri.queryWitness)).2 = _
      rw [hobs, sample_idealOf_nil]
      rfl
    refine ⟨fun _ ↦ ?_, fun j hj ↦ ?_⟩
    · rw [hobs, sample_idealOf_nil]
      obtain ⟨x, l, hx⟩ := List.exists_cons_of_length_pos
        (l := (answer (keyAt answer blocks r)).2.toList) (by omega)
      change (answer (keyAt answer blocks r)).2.toList.headD 0 = _
      rw [hx, List.headD_cons, List.getD_cons_zero]
    · rw [hw, htail j hj, show challengeOffset P.queryPowBits = 1 by simp only [challengeOffset,
        hb, ↓reduceIte]]
      exact hhead j hj

/-- **The run's challenges are the oracle's answers.** On the ideal primitives of an answer
table, with streams long enough for the query round, on a proof with a final polynomial: `α` is
the first `d` samples of round `0`; `ζ`, the batching challenge and `β_i` are read at the grinding
offsets of rounds `1`, `2` and `3 + i`; and the query round's grinding sample and query samples
are its samples from `0` and from the grinding offset. -/
theorem challenges_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K)
    (htn : traceNextOk A proof.opened = true)
    (hshape : preprocessedShapeOk A vk proof.opened proof.degreeBits = true)
    (hfp : proof.fri.finalPoly.toList ≠ []) :
    let u := fun j ↦ (answer (keyAt answer (inputs P A vk pis proof) j)).2
    let n := (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length
    Challenge.toSpec (alphaOf (idealOf answer) P A vk proof pis) = extAt (u 0) 0 ∧
      Challenge.toSpec (zetaOf (idealOf answer) P A vk proof pis) =
        extAt (u 1) (challengeOffset P.oodPowBits) ∧
      Challenge.toSpec (batchOf (idealOf answer) P A vk proof pis) =
        extAt (u 2) (challengeOffset P.batchPowBits) ∧
      (betasOf (idealOf answer) P A vk proof pis).length = n ∧
      (∀ i < n, Challenge.toSpec ((betasOf (idealOf answer) P A vk proof pis).getD i 0) =
        extAt (u (3 + i)) (challengeOffset P.commitPowBits)) ∧
      (P.queryPowBits ≠ 0 → powSampleOf (idealOf answer) P A vk proof pis =
        ((u (3 + n)).toList.getD 0 0)) ∧
      ∀ j < P.numQueries, querySampleOf (idealOf answer) P A vk proof pis j =
        ((u (3 + n)).toList.getD (challengeOffset P.queryPowBits + j) 0) := by
  intro u n
  obtain ⟨hb1, l₀, hl₀⟩ := batch_idealOf answer P A vk proof pis (by omega) htn hshape
  have hstart : friStart (idealOf answer) P A vk proof pis =
      ⟨capAt answer (inputs P A vk pis proof) 3, friSeedOf P proof, []⟩ := by
    rw [friStart, hl₀, obsList_idealOf_ne answer _ _ (friSeed_ne_nil _ _ _ _ _ _ _ _)]
    rfl
  obtain ⟨hc1, hc2, l, hl⟩ := commitReplay_idealOf (EF := EF) answer P (by omega)
    (inputs P A vk pis proof) (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList) 3
    (friSeedOf P proof) [] (fun i hi ↦ inputs_getD_fold P A vk pis proof i hi)
  rw [← hstart] at hc1 hc2 hl
  obtain ⟨hq1, hq2⟩ := queryRound_idealOf answer P proof (by omega) (inputs P A vk pis proof)
    (3 + n) _ l hfp (inputs_getD_last P A vk pis proof)
  have hqs : queryState (idealOf answer) P A vk proof pis =
      obsExts (idealOf answer) ⟨capAt answer (inputs P A vk pis proof) (3 + n),
        seedAt (friSeedOf P proof) n, l⟩ proof.fri.finalPoly.toList := by
    rw [queryState, hl]
  refine ⟨(alpha_idealOf answer P A vk proof pis (by omega)).1,
    (zeta_idealOf answer P A vk proof pis (by omega)).1, hb1, hc1, hc2, fun hb ↦ ?_, fun j hj ↦ ?_⟩
  · rw [powSampleOf, ite_eq_right hb, hqs, hq1 hb]
  · rw [querySampleOf, hqs, hq2 j hj]

end Rounds

end CompStark.Ni
