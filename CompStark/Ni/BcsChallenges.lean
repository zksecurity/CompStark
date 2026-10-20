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
open CompStark.Stark CompStark.Fri CompStark.RandomOracle Montgomery.Native32 OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field

variable {EF : Type} [Challenge EF] {K : Nat} (answer : (q : Query) → Answer K q)

/-! ### The ideal challenger on an answer table -/

theorem obsList_idealOf (s : Sponge) (hs : s.samples = []) (xs : List F) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  induction xs generalizing s with
  | nil => obtain ⟨c, i, l⟩ := s; dsimp only at hs; subst hs; simp only [obsList,
      List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    rw [obsList, List.foldl_cons, ← obsList, ih _ rfl]
    simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem obsList_idealOf_ne (s : Sponge) (xs : List F) (hxs : xs ≠ []) :
    obsList (idealOf answer) s xs = ⟨s.cap, s.input ++ xs, []⟩ := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  rw [obsList, List.foldl_cons, ← obsList, obsList_idealOf answer _ rfl]
  simp only [idealOf, withAnswers, List.append_assoc, List.singleton_append]

theorem sample_idealOf_cons (cap : Digest) (input : List F) (x : F) (rest : List F) :
    (idealOf answer).sample ⟨cap, input, x :: rest⟩ = (x, ⟨cap, input, rest⟩) := rfl

theorem sample_idealOf_nil (cap : Digest) (input : List F) :
    (idealOf answer).sample ⟨cap, input, []⟩ =
      ((answer (.duplex cap input)).2.toList.headD 0,
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.tail⟩) := rfl

/-- Sampling `n` elements with `n` samples left or more takes them. -/
theorem smpList_idealOf (cap : Digest) (input : List F) :
    ∀ (n : Nat) (l : List F), n ≤ l.length →
      smpList (idealOf answer) ⟨cap, input, l⟩ n = (l.take n, ⟨cap, input, l.drop n⟩)
  | 0, _, _ => rfl
  | n + 1, x :: rest, h => by
    show (x :: (smpList (idealOf answer) ⟨cap, input, rest⟩ n).1,
      (smpList (idealOf answer) ⟨cap, input, rest⟩ n).2) = _
    rw [smpList_idealOf cap input n rest (by simp only [List.length_cons] at h; omega)]
    rfl

/-- An extension sample with `d` samples left or more takes them. -/
theorem smpExt_idealOf_pop (cap : Digest) (input : List F) (l : List F)
    (h : Challenge.d EF ≤ l.length) :
    smpExt (idealOf answer) ⟨cap, input, l⟩ =
      ((Challenge.ofCoeffs (l.take (Challenge.d EF)) : EF),
        ⟨cap, input, l.drop (Challenge.d EF)⟩) := by
  rw [smpExt, smpList_idealOf answer cap input _ l h]

/-- An extension sample from no samples duplexes and takes the answer's first `d` samples. -/
theorem smpExt_idealOf_nil (hK : Challenge.d EF ≤ K) (cap : Digest) (input : List F) :
    Challenge.toSpec (smpExt (idealOf answer) ⟨cap, input, []⟩ : EF × Sponge).1 =
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

theorem sampleStates_idealOf (cap : Digest) (input : List F) :
    ∀ (l : List F) (j : Nat), j ≤ l.length →
      sampleStates (idealOf answer) ⟨cap, input, l⟩ j = ⟨cap, input, l.drop j⟩
  | _, 0, _ => rfl
  | l, j + 1, hj => by
    rw [sampleStates, sampleStates_idealOf cap input l j (by omega)]
    obtain ⟨x, rest, hx⟩ := List.exists_cons_of_length_pos (l := l.drop j)
      (by rw [List.length_drop]; omega)
    rw [hx, sample_idealOf_cons, ← List.drop_drop, hx, List.drop_one, List.tail_cons]

theorem sampleStates_succ (H : Primitives Id) (s : H.State) :
    ∀ j, sampleStates H s (j + 1) = sampleStates H (H.sample s).2 j
  | 0 => rfl
  | j + 1 => by rw [sampleStates, sampleStates_succ H s j]; rfl

/-! ### Observations as lists -/

theorem obsList_append (H : Primitives Id) (s : H.State) (a b : List F) :
    obsList H s (a ++ b) = obsList H (obsList H s a) b := List.foldl_append

theorem coeffs_append (a b : List EF) : coeffs (a ++ b) = coeffs a ++ coeffs b :=
  List.flatMap_append

theorem obsExts_eq (H : Primitives Id) (s : H.State) (xs : List EF) :
    obsExts H s xs = obsList H s (coeffs xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [obsExts, List.foldl_cons, ← obsExts, ih, show x :: xs = [x] ++ xs from rfl,
      coeffs_append, obsList_append,
      show coeffs [x] = Ext.coeffs x from List.append_nil _]
    rfl

theorem obsPts_eq (H : Primitives Id) (pts : List (EF × List EF)) (s : H.State) :
    pts.foldl (fun s p ↦ obsExts H s p.2) s = obsList H s (coeffs (pts.flatMap (·.2))) := by
  induction pts generalizing s with
  | nil => rfl
  | cons p pts ih => rw [List.foldl_cons, ih, obsExts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsMats_eq (H : Primitives Id) (mats : List (Domain × List (EF × List EF)))
    (s : H.State) :
    mats.foldl (fun s m ↦ m.2.foldl (fun s p ↦ obsExts H s p.2) s) s =
      obsList H s (coeffs (mats.flatMap fun m ↦ m.2.flatMap (·.2))) := by
  induction mats generalizing s with
  | nil => rfl
  | cons m mats ih => rw [List.foldl_cons, ih, obsPts_eq, List.flatMap_cons, coeffs_append,
      obsList_append]

theorem obsOpened_eq (H : Primitives Id) (s : H.State) (rounds : List (Round EF)) :
    obsOpened H s rounds = obsList H s (coeffs (roundValues rounds)) := by
  induction rounds generalizing s with
  | nil => rfl
  | cons r rounds ih =>
    rw [obsOpened, List.foldl_cons, ← obsOpened, ih, obsMats_eq,
      show roundValues (r :: rounds) = r.2.flatMap (fun m ↦ m.2.flatMap (·.2)) ++
        roundValues rounds from List.flatMap_cons, coeffs_append, obsList_append]

theorem roundValues_vRounds (proof : Proof EF) (zeta : EF) :
    roundValues (vRounds proof zeta) = openedValues proof.opened := by
  simp only [roundValues, vRounds, openedValues, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_map, List.append_assoc]

/-- An accepted proof of `2 ^ logN` rows opens values and has a final polynomial. -/
theorem nonempty_of_verify (S : Iop.Setup EF) (H : Primitives Id) (proof : Proof
    EF)
    (pis : List F)
    (hdb : proof.degreeBits = S.logN) (h : verifyWith H S.params S.air proof pis = .ok ()) :
    openedValues proof.opened ≠ [] ∧ proof.fri.finalPoly.toList ≠ [] := by
  obtain ⟨-, -, hqc, hq4, harity, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok H S.params S.air proof pis h
  rw [hdb] at harity
  obtain ⟨-, hb, hne, hh⟩ := friHyps S H proof pis hdb harity
  obtain ⟨-, -, hfp, -⟩ := verifyFri_ok H S.params proof.fri _ hb hne hh _ _ hfriOk
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · have hpos : 0 < proof.opened.quotientChunks.size := by rw [hqc]; exact Nat.two_pow_pos _
    have h4 := hq4 _ (Array.getElem_mem hpos)
    have : proof.opened.quotientChunks[0].toList ∈
        proof.opened.quotientChunks.toList.map (·.toList) :=
      List.mem_map_of_mem (Array.getElem_mem_toList hpos)
    rw [openedValues, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at he
    have := he.2 _ (Array.getElem_mem_toList hpos)
    rw [← Array.length_toList, this, List.length_nil] at h4
    exact (Challenge.params EF).d_pos.ne h4
  · have := congrArg List.length he
    rw [Array.length_toList, hfp, List.length_nil] at this
    exact absurd this (Nat.two_pow_pos _).ne'

/-- The committed trace of the design (`Iop.committedTrace`) is the extracted trace words on the
log's cache. -/
theorem committedTrace_eq (S : Iop.Setup EF) (log : QueryLog (spec S.streamLen))
    (proof : Proof EF) : Iop.committedTrace S log proof = traceWords S (Iop.logCache log) proof :=
        by
  funext j z
  simp only [Iop.committedTrace, traceWords, committedColumn, leafRow]
  split <;> rename_i h <;> rw [h]
  · rfl
  · simp only [Option.getD_none, List.getD_nil, toField_zero]

/-! ### Round by round -/

theorem digest_toList_ne_nil (d : Digest) : d.toList ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [Vector.length_toList, List.length_nil] at this
  exact absurd this (by decide)

section Rounds
variable (P : Params) (proof : Proof EF) (pis : List F)

theorem stateAlpha_idealOf :
    stateAlpha (idealOf answer) proof pis =
      ⟨capAt answer (inputs P pis proof) 0, (inputs P pis proof).getD 0 [], []⟩ := by
  unfold stateAlpha
  rw [obsList_idealOf answer _ rfl proof.traceCommit.toList, obsList_idealOf answer _ rfl]
  rfl

theorem alpha_idealOf (hK : Challenge.d EF ≤ K) :
    Challenge.toSpec (alphaOf (idealOf answer) proof pis) =
      extAt (answer (keyAt answer (inputs P pis proof) 0)).2 0 ∧
    (smpExt (EF := EF) (idealOf answer) (stateAlpha (idealOf answer) proof pis)).2 =
      ⟨capAt answer (inputs P pis proof) 1, [],
        (answer (keyAt answer (inputs P pis proof) 0)).2.toList.drop (Challenge.d EF)⟩ := by
  rw [alphaOf, stateAlpha_idealOf answer P]
  exact smpExt_idealOf_nil answer hK _ _

theorem stateZeta_idealOf (hK : Challenge.d EF ≤ K) :
    stateZeta (idealOf answer) proof pis =
      ⟨capAt answer (inputs P pis proof) 1, (inputs P pis proof).getD 1 [], []⟩ := by
  rw [stateZeta, (alpha_idealOf answer P proof pis hK).2,
    obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
  rfl

theorem zeta_idealOf (hK : Challenge.d EF ≤ K) :
    Challenge.toSpec (zetaOf (idealOf answer) proof pis) =
      extAt (answer (keyAt answer (inputs P pis proof) 1)).2 0 ∧
    (smpExt (EF := EF) (idealOf answer) (stateZeta (idealOf answer) proof pis)).2 =
      ⟨capAt answer (inputs P pis proof) 2, [],
        (answer (keyAt answer (inputs P pis proof) 1)).2.toList.drop (Challenge.d EF)⟩ := by
  rw [zetaOf, stateZeta_idealOf answer P proof pis hK]
  exact smpExt_idealOf_nil answer hK _ _

theorem stateFri_idealOf (hK : Challenge.d EF ≤ K) (hopen : openedValues proof.opened ≠ []) :
    stateFri (idealOf answer) proof pis =
      ⟨capAt answer (inputs P pis proof) 2, (inputs P pis proof).getD 2 [], []⟩ := by
  rw [stateFri, (zeta_idealOf answer P proof pis hK).2, obsOpened_eq, roundValues_vRounds,
    obsList_idealOf_ne answer _ _ (coeffs_ne_nil hopen)]
  rfl

theorem batch_idealOf (hK : Challenge.d EF ≤ K) (hopen : openedValues proof.opened ≠ []) :
    Challenge.toSpec (batchOf (idealOf answer) proof pis) =
      extAt (answer (keyAt answer (inputs P pis proof) 2)).2 0 ∧
    (smpExt (EF := EF) (idealOf answer) (stateFri (idealOf answer) proof pis)).2 =
      ⟨capAt answer (inputs P pis proof) 3, [],
        (answer (keyAt answer (inputs P pis proof) 2)).2.toList.drop (Challenge.d EF)⟩ := by
  rw [batchOf, stateFri_idealOf answer P proof pis hK hopen]
  exact smpExt_idealOf_nil answer hK _ _

/-- A fold round: observe the commitment and the witness, check the grinding sample, and sample
`β`, which is the round's answer at the grinding offset. -/
theorem foldRound_idealOf (hK : Challenge.d EF + 1 ≤ K) (blocks : List (List F)) (r : Nat)
    (rest : List F) (c : Digest) (w : F)
    (hr : blocks.getD r [] = c.toList ++ witnessInput P.commitPowBits w) :
    let b := smpExt (EF := EF) (idealOf answer) (chkWit (idealOf answer) P.commitPowBits w
      (obsList (idealOf answer) ⟨capAt answer blocks r, [], rest⟩ c.toList)).2
    Challenge.toSpec b.1 = extAt (answer (keyAt answer blocks r)).2
      (challengeOffset P.commitPowBits) ∧
    ∃ l, b.2 = ⟨capAt answer blocks (r + 1), [], l⟩ := by
  intro b
  simp only [b]
  rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil c), List.nil_append]
  by_cases hb : P.commitPowBits = 0
  · simp only [witnessInput, hb, ↓reduceIte, List.append_nil] at hr
    have h := smpExt_idealOf_nil (EF := EF) answer (by omega) (capAt answer blocks r)
      (blocks.getD r [])
    simp only [chkWit, hb, ↓reduceIte, challengeOffset]
    rw [← hr]
    exact ⟨h.1, _, h.2⟩
  · simp only [witnessInput, hb, ↓reduceIte] at hr
    have hst : (chkWit (idealOf answer) P.commitPowBits w
        ⟨capAt answer blocks r, c.toList, []⟩).2 =
        ⟨(answer (keyAt answer blocks r)).1, [],
          (answer (keyAt answer blocks r)).2.toList.tail⟩ := by
      rw [chkWit, ite_eq_right hb]
      show ((idealOf answer).sample ⟨capAt answer blocks r, c.toList ++ [w], []⟩).2 = _
      rw [sample_idealOf_nil, ← hr]
      rfl
    rw [hst]
    have hlen : Challenge.d EF ≤ (answer (keyAt answer blocks r)).2.toList.tail.length := by
      rw [List.length_tail, Vector.length_toList]; omega
    rw [show challengeOffset P.commitPowBits = 1 by simp only [challengeOffset, hb, ↓reduceIte],
      smpExt_idealOf_pop answer _ _ _ hlen, ← List.drop_one]
    exact ⟨toSpec_ofCoeffs_drop _ 1, _, rfl⟩

theorem commitReplay_idealOf (hK : Challenge.d EF + 1 ≤ K) (blocks : List (List F)) :
    ∀ (cws : List (Digest × F)) (r : Nat) (rest : List F),
      (∀ i (hi : i < cws.length), blocks.getD (r + i) [] =
        cws[i].1.toList ++ witnessInput P.commitPowBits cws[i].2) →
      (commitReplay (EF := EF) (idealOf answer) P cws ⟨capAt answer blocks r, [], rest⟩).1.length =
          cws.length ∧
        (∀ i < cws.length, Challenge.toSpec
          ((commitReplay (EF := EF) (idealOf answer) P cws ⟨capAt answer blocks r, [], rest⟩).1.getD
            i 0) =
            extAt (answer (keyAt answer blocks (r + i))).2 (challengeOffset P.commitPowBits)) ∧
        ∃ l, (commitReplay (EF := EF) (idealOf answer) P cws ⟨capAt answer blocks r, [], rest⟩).2 =
          ⟨capAt answer blocks (r + cws.length), [], l⟩
  | [], r, rest, _ => ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _), rest, rfl⟩
  | (c, w) :: cws, r, rest, hr => by
    obtain ⟨hβ, l, hl⟩ := foldRound_idealOf answer P hK blocks r rest c w (hr 0 (by simp))
    have ih := commitReplay_idealOf hK blocks cws (r + 1) l (fun i hi ↦ by
      rw [show r + 1 + i = r + (i + 1) by omega]
      exact hr (i + 1) (by simp only [List.length_cons]; omega))
    simp only [commitReplay, hl] at ih ⊢
    obtain ⟨ih1, ih2, l', hl'⟩ := ih
    refine ⟨by rw [List.length_cons, ih1, List.length_cons], fun i hi ↦ ?_, l', ?_⟩
    · cases i with
      | zero => exact hβ
      | succ i =>
        rw [List.getD_cons_succ, ih2 i (by simp only [List.length_cons] at hi; omega),
          show r + 1 + i = r + (i + 1) by omega]
    · rw [hl', List.length_cons, show r + 1 + cws.length = r + (cws.length + 1) by omega]

theorem sample_drop_idealOf (cap : Digest) (input : List F) (l : List F) (j : Nat)
    (hj : j < l.length) :
    ((idealOf answer).sample ⟨cap, input, l.drop j⟩).1 = l.getD j 0 := by
  rw [List.drop_eq_getElem_cons hj, sample_idealOf_cons, List.getD_eq_getElem _ _ hj]

/-- The query round: observe the final polynomial, the arities and the witness; the grinding
sample is the round's first answered sample, and query `j`'s sample the one at the grinding
offset plus `j`. -/
theorem queryRound_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K) (blocks : List (List F))
    (r : Nat) (rest : List F) (hfp : proof.fri.finalPoly.toList ≠ [])
    (hr : blocks.getD r [] = coeffs proof.fri.finalPoly.toList ++
      (arities proof.fri).map (fun a : Nat ↦ (a : F)) ++
      witnessInput P.queryPowBits proof.fri.queryWitness) :
    let qs := (arities proof.fri).foldl (fun s (a : Nat) ↦ (idealOf answer).observe s (a : F))
      (obsExts (idealOf answer) ⟨capAt answer blocks r, [], rest⟩ proof.fri.finalPoly.toList)
    (P.queryPowBits ≠ 0 →
      ((idealOf answer).sample ((idealOf answer).observe qs proof.fri.queryWitness)).1 =
        (answer (keyAt answer blocks r)).2.toList.getD 0 0) ∧
    ∀ j < P.numQueries, ((idealOf answer).sample (sampleStates (idealOf answer)
      (chkWit (idealOf answer) P.queryPowBits proof.fri.queryWitness qs).2 j)).1 =
        (answer (keyAt answer blocks r)).2.toList.getD (challengeOffset P.queryPowBits + j) 0 := by
  intro qs
  have hqs : qs = ⟨capAt answer blocks r, coeffs proof.fri.finalPoly.toList ++
      (arities proof.fri).map (fun a : Nat ↦ (a : F)), []⟩ := by
    simp only [qs]
    rw [obsExts_eq, obsList_idealOf_ne answer _ _ (coeffs_ne_nil hfp), List.nil_append,
      ← List.foldl_map (f := fun a : Nat ↦ (a : F)) (g := (idealOf answer).observe), ← obsList,
      obsList_idealOf answer _ rfl]
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
table, with streams long enough for the query round, on a proof that opens values and has a
final polynomial: `α`, `ζ` and the batching challenge are the first `d` samples of rounds `0`,
`1`, `2`; `β_i` is read at the grinding offset of round `3 + i`; and the query round's grinding
sample and query samples are its samples from `0` and from the grinding offset. -/
theorem challenges_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K)
    (hopen : openedValues proof.opened ≠ []) (hfp : proof.fri.finalPoly.toList ≠ []) :
    let u := fun j ↦ (answer (keyAt answer (inputs P pis proof) j)).2
    let n := (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length
    Challenge.toSpec (alphaOf (idealOf answer) proof pis) = extAt (u 0) 0 ∧
      Challenge.toSpec (zetaOf (idealOf answer) proof pis) = extAt (u 1) 0 ∧
      Challenge.toSpec (batchOf (idealOf answer) proof pis) = extAt (u 2) 0 ∧
      (betasOf (idealOf answer) P proof pis).length = n ∧
      (∀ i < n, Challenge.toSpec ((betasOf (idealOf answer) P proof pis).getD i 0) =
        extAt (u (3 + i)) (challengeOffset P.commitPowBits)) ∧
      (P.queryPowBits ≠ 0 → powSampleOf (idealOf answer) P proof pis =
        FastField.toField ((u (3 + n)).toList.getD 0 0)) ∧
      ∀ j < P.numQueries, querySampleOf (idealOf answer) P proof pis j =
        FastField.toField ((u (3 + n)).toList.getD (challengeOffset P.queryPowBits + j) 0) := by
  intro u n
  have h4 : Challenge.d EF ≤ K := by omega
  obtain ⟨hb1, hb2⟩ := batch_idealOf answer P proof pis h4 hopen
  obtain ⟨hc1, hc2, l, hl⟩ := commitReplay_idealOf (EF := EF) answer P (by omega)
    (inputs P pis proof) (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList) 3 _
    (fun i hi ↦ by
      rw [show 3 + i = 2 + 1 + i by omega]; exact inputs_getD_fold P pis proof i hi)
  rw [← hb2] at hc1 hc2 hl
  obtain ⟨hq1, hq2⟩ := queryRound_idealOf answer P proof (by omega) (inputs P pis proof)
    (3 + n) l hfp (by rw [show 3 + n = 2 + 1 + n by omega]; exact inputs_getD_last P pis proof)
  have hqs : queryState (idealOf answer) P proof pis =
      (arities proof.fri).foldl (fun s (a : Nat) ↦ (idealOf answer).observe s (a : F))
        (obsExts (idealOf answer) ⟨capAt answer (inputs P pis proof) (3 + n), [], l⟩
          proof.fri.finalPoly.toList) := by
    rw [queryState, hl]
  refine ⟨(alpha_idealOf answer P proof pis h4).1, (zeta_idealOf answer P proof pis h4).1, hb1,
    hc1, hc2, fun hb ↦ ?_, fun j hj ↦ ?_⟩
  · rw [powSampleOf, ite_eq_right hb, hqs, hq1 hb]
  · rw [querySampleOf, hqs, hq2 j hj]

end Rounds

end CompStark.Ni
