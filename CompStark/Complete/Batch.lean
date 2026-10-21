/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Pcs
public import CompStark.Complete.Quotient
public import CompStark.Plonky3.Batch

/-! # The specification prover's batch proofs verify

The batch-STARK layer of completeness. The verifier replays the prover's transcript: it observes
the same domain separator, degree bits, commitments and public values, checks the same grinding
witness, so it samples the same `α` and `ζ`, and `ζ` off the base field is off every trace
domain. Its rounds are the honest rounds of the prover's openings (`batchRounds_eq`), on which
`verifyPcs` accepts `openPcs`'s proof (`verifyPcs_openPcs`); every instance's opened values are
`uni-stark`'s honest openings (`opened_eq`), so its constraint check passes
(`checkConstraints_honest`).
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Complete

variable {F : Type} [BaseField F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

section Exts
variable (P : Params) (Is : List (Instance F)) (ts : List (Array F))

/-- The traces' extensions. -/
def bExts : List (Mat F) :=
  (Is.zip ts).map fun (I, t) ↦ ldeRef I.logN P.logBlowup gen I.air.width t

theorem length_bExts (hts : ts.length = Is.length) : (bExts P Is ts).length = Is.length := by
  rw [bExts, List.length_map, List.length_zip, hts, Nat.min_self]

theorem getElem_bExts (hts : ts.length = Is.length) (i : Nat) (hi : i < Is.length) :
    (bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; exact hi) =
      ldeRef Is[i].logN P.logBlowup gen Is[i].air.width (ts[i]'(by rw [hts]; exact hi)) := by
  simp only [bExts, List.getElem_map, List.getElem_zip]

end Exts

variable [Poseidon2Field F] {EF : Type} [Challenge F EF]

/-! ### The prover's run, step by step -/

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- The preprocessed traces' extensions, one per instance that has preprocessed columns, and their
commitment if any. -/
def bPrep : List (Option (Mat F)) × Option (Committed F) := setupBatchWith (specBackend EF) P Is

/-- The transcript after the domain separator, the degree bits, the main commitment, the public
values and the preprocessed commitment. -/
def bTA : Transcript F 24 :=
  ((((Poseidon2.initTranscript.observeList
    (batchSeedOf EF P Is ⟨(bPrep EF P Is).2.map Committed.root⟩)).observeExts
      (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).observeList
    (Committed.ofMats hashF compF (bExts P Is ts)).root.toList).observeList ps.flatten).observeList
    (((bPrep EF P Is).2.map fun c ↦ c.root.toList).getD [])

/-- The constraint-folding challenge. -/
def bAlpha : EF := ((bTA EF P Is ts ps).sampleExtValue : EF)

/-- Every instance's quotient chunks' extensions. -/
def bChunks : List (List (Mat F)) :=
  ((Is.zip (bExts P Is ts)).zip ((bPrep EF P Is).1.zip ps)).map fun ((I, ext), (pext, p)) ↦
    quotientChunks (specBackend EF) P I.air I.logN ext pext p (bAlpha EF P Is ts ps)

/-- The transcript after the quotient commitment. -/
def bTC : Transcript F 24 :=
  (Transcript.sampleExtState EF (bTA EF P Is ts ps)).observeList
    (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root.toList

/-- The out-of-domain grinding: its witness and the transcript after it. -/
def bOod : F × Transcript F 24 := (bTC EF P Is ts ps).grind P.oodPowBits

/-- The out-of-domain point. -/
def bZeta : EF := ((bOod EF P Is ts ps).2.sampleExtValue : EF)

theorem batchCommitAndSample_run :
    (batchCommitAndSample (specBackend EF) P Is (bPrep EF P Is) ts ps).run
      Poseidon2.initTranscript =
      ((bExts P Is ts, Committed.ofMats hashF compF (bExts P Is ts), bChunks EF P Is ts ps,
        Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten, bZeta EF P Is ts ps,
        (bOod EF P Is ts ps).1), Transcript.sampleExtState EF (bOod EF P Is ts ps).2) := rfl

theorem batchOutOfDomainPoint_eq :
    batchOutOfDomainPoint EF P Is ts ps = bZeta EF P Is ts ps := rfl

end Honest

/-! ### The proof -/

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- `ζ ω` on an instance's trace domain. -/
def bZetaNext (I : Instance F) : EF := bZeta EF P Is ts ps * Ext.ofBase (twoAdicGen I.logN)

/-- The preprocessed traces' round, if any. -/
def bPrepRound : Option (OpenRound (specBackend EF)) :=
  (bPrep EF P Is).2.map fun pc ↦ (pc, (Is.zip (bPrep EF P Is).1).filterMap fun (I, pext) ↦
    pext.map fun e ↦
      (e, preprocessedPoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I)))

/-- The rounds the prover opens. -/
def bRounds : List (OpenRound (specBackend EF)) :=
  [(Committed.ofMats hashF compF (bExts P Is ts), (Is.zip (bExts P Is ts)).map fun (I, e) ↦
      (e, tracePoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I))),
    (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten,
      (bChunks EF P Is ts ps).flatten.map fun m ↦ (m, [bZeta EF P Is ts ps]))] ++
    (bPrepRound EF P Is ts ps).toList

/-- The opening argument's run: the opened values, the FRI proof and the final transcript. -/
def bPcs : (List (List (List (Array EF))) × FriProof F EF) × Transcript F 24 :=
  (openPcs (specBackend EF) P (bRounds EF P Is ts ps)).run
    (Transcript.sampleExtState EF (bOod EF P Is ts ps).2)

theorem proveBatch_eq : proveBatch EF P Is ts ps =
    { mainCommit := (Committed.ofMats hashF compF (bExts P Is ts)).root
      quotientCommit := (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root
      opened := (Is.zipIdx.map fun (I, i) ↦ instanceOpened I.air (bPcs EF P Is ts ps).1.1 i
        (((bChunks EF P Is ts ps).map List.length).getD i 0)
        (((bChunks EF P Is ts ps).map List.length).take i).sum
        ((Is.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1).take i).sum).toArray
      fri := (bPcs EF P Is ts ps).1.2
      degreeBits := (Is.map (·.logN)).toArray
      oodWitness := (bOod EF P Is ts ps).1 } := by
  unfold proveBatch proveBatchWith
  dsimp only
  rw [prun_bind]
  erw [batchCommitAndSample_run]
  rfl

theorem proveBatchTranscript_eq :
    proveBatchTranscript EF P Is ts ps = (bPcs EF P Is ts ps).2 := by
  unfold proveBatchTranscript
  dsimp only
  rw [prun_bind]
  erw [batchCommitAndSample_run]
  rfl

end Honest

/-! ### Reading the openings by instance -/

/-- Entry `c` of list `i` of a list of lists, in their concatenation. -/
theorem getD_flatten_offset {α : Type} (d : α) : ∀ (L : List (List α)) (i c : Nat),
    i < L.length → c < (L.getD i []).length →
    L.flatten.getD (((L.map List.length).take i).sum + c) d = (L.getD i []).getD c d
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | l :: L, 0, c, _, hc => by
    simp only [List.getD_cons_zero] at hc ⊢
    simp only [List.map_cons, List.take_zero, List.sum_nil, Nat.zero_add, List.flatten_cons]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hc, ← List.getD_eq_getElem?_getD]
  | l :: L, i + 1, c, hi, hc => by
    simp only [List.getD_cons_succ] at hc ⊢
    simp only [List.map_cons, List.take_succ_cons, List.sum_cons, List.flatten_cons]
    rw [List.getD_eq_getElem?_getD, Nat.add_assoc, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    exact getD_flatten_offset d L i c (by simp only [List.length_cons] at hi; omega) hc

/-- The image of element `i` in a `filterMap`, after the images of the elements before it. -/
theorem getD_filterMap_offset {α β : Type} (f : α → Option β) (d : β) : ∀ (l : List α) (i : Nat)
    (hi : i < l.length) (y : β), f l[i] = some y →
    (l.filterMap f).getD ((l.take i).map fun x ↦ if (f x).isSome then 1 else 0).sum d = y
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, _, y, hy => by
    simp only [List.getElem_cons_zero] at hy
    simp only [List.take_zero, List.map_nil, List.sum_nil, List.filterMap_cons, hy,
      List.getD_cons_zero]
  | a :: l, i + 1, hi, y, hy => by
    simp only [List.getElem_cons_succ] at hy
    have ih := getD_filterMap_offset f d l i (by simp only [List.length_cons] at hi; omega) y hy
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.filterMap_cons]
    cases hfa : f a with
    | none => simpa only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        using ih
    | some z =>
      simp only [Option.isSome_some, ↓reduceIte]
      rw [Nat.add_comm, List.getD_cons_succ]
      exact ih

/-- Reading a mapped list. -/
theorem getD_map_of {α β : Type} (f : α → β) (l : List α) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem zip_map_filterMap {α β γ : Type} (g : α → β) (F : α × β → Option γ) :
    ∀ l : List α, (l.zip (l.map g)).filterMap F = l.filterMap fun a ↦ F (a, g a)
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
    rw [zip_map_filterMap g F l]

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

theorem bPrep_fst : (bPrep EF P Is).1 = Is.map fun I ↦ prepLde P.logBlowup I.air I.logN := rfl

theorem bPrep_snd : (bPrep EF P Is).2 =
    if (Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN).isEmpty then none
    else some (Committed.ofMats hashF compF
      (Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN)) := by
  show (if ((Is.map fun I ↦ prepLde P.logBlowup I.air I.logN).filterMap id).isEmpty then _
    else _) = _
  simp only [List.filterMap_map, Function.comp_def, id]
  rfl

theorem length_bChunks (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    (bChunks EF P Is ts ps).length = Is.length := by
  rw [bChunks, List.length_map, List.length_zip, List.length_zip, List.length_zip,
    length_bExts P Is ts hts, bPrep_fst, List.length_map, hps]
  simp only [Nat.min_self]

theorem getElem_bChunks (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) :
    (bChunks EF P Is ts ps)[i]'(by rw [length_bChunks EF P Is ts ps hts hps]; exact hi) =
      quotientChunks (specBackend EF) P Is[i].air Is[i].logN
        ((bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; exact hi))
        (prepLde P.logBlowup Is[i].air Is[i].logN) (ps[i]'(by rw [hps]; exact hi))
        (bAlpha EF P Is ts ps) := by
  simp only [bChunks, List.getElem_map, List.getElem_zip, bPrep_fst]

theorem bPcs_opened : (bPcs EF P Is ts ps).1.1 =
    (bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup) := by
  unfold bPcs
  rw [openPcs_run]
  dsimp only
  rw [List.map_map]
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  rfl

end Honest

theorem getD_of_lt {α : Type} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- Instance `i`'s opened values are `uni-stark`'s honest openings of its trace's extension and its
quotient chunks. -/
theorem instanceOpened_eq (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) :
    instanceOpened Is[i].air (bPcs EF P Is ts ps).1.1 i
        (((bChunks EF P Is ts ps).map List.length).getD i 0)
        (((bChunks EF P Is ts ps).map List.length).take i).sum
        ((Is.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1).take i).sum =
      honestOpened P.logBlowup Is[i].air Is[i].logN
        ((bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; exact hi))
        ((bChunks EF P Is ts ps)[i]'(by rw [length_bChunks EF P Is ts ps hts hps]; exact hi))
        (bZeta EF P Is ts ps) := by
  have hiE : i < (bExts P Is ts).length := by rw [length_bExts P Is ts hts]; exact hi
  have hiC : i < (bChunks EF P Is ts ps).length := by
    rw [length_bChunks EF P Is ts ps hts hps]; exact hi
  have hiZ : i < (Is.zip (bExts P Is ts)).length := by
    rw [List.length_zip, length_bExts P Is ts hts, Nat.min_self]; exact hi
  set A := Is[i].air with hA
  set zeta := bZeta EF P Is ts ps with hzeta
  set zn := bZetaNext EF P Is ts ps Is[i] with hzn
  set ext := (bExts P Is ts)[i] with hext
  set chunks := (bChunks EF P Is ts ps)[i] with hchunks
  set pext := ldeRef Is[i].logN P.logBlowup gen A.preprocessedWidth A.preprocessed with hpext
  rw [bPcs_opened]
  -- the trace's openings
  have hmain : (((bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup)).headD
      []).getD i [] = (tracePoints A zeta zn).map (Fri.openedAt P.logBlowup ext) := by
    simp only [bRounds, List.cons_append, List.map_cons, List.headD_cons]
    rw [getD_of_lt _ _ (by rw [List.length_map, List.length_map]; exact hiZ), List.getElem_map,
      List.getElem_map, List.getElem_zip]
    rfl
  -- the quotient chunks' openings
  have hchunk : ∀ c (hc : c < chunks.length),
      ((((bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup)).getD 1 []).getD
        ((((bChunks EF P Is ts ps).map List.length).take i).sum + c) []).headD #[] =
        Fri.openedAt P.logBlowup chunks[c] zeta := by
    intro c hc
    have hL : (((bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup)).getD 1 []) =
        ((bChunks EF P Is ts ps).map fun cs ↦ cs.map fun m ↦ [Fri.openedAt P.logBlowup m zeta]
          ).flatten := by
      simp only [bRounds, List.cons_append, List.map_cons, List.getD_cons_succ,
        List.getD_cons_zero, List.map_map, List.map_flatten]
      refine congrArg List.flatten (List.map_congr_left fun cs _ ↦ ?_)
      simp only [Function.comp_apply, List.map_map]
      rfl
    have hlen : ((bChunks EF P Is ts ps).map fun cs ↦ cs.map fun m ↦
        [Fri.openedAt P.logBlowup m zeta]).map List.length =
        (bChunks EF P Is ts ps).map List.length := by
      rw [List.map_map]
      exact List.map_congr_left fun cs _ ↦ List.length_map _
    have hget : ((bChunks EF P Is ts ps).map fun cs ↦ cs.map fun m ↦
        [Fri.openedAt P.logBlowup m zeta]).getD i [] =
        chunks.map fun m ↦ [Fri.openedAt P.logBlowup m zeta] := by
      rw [getD_of_lt _ _ (by rw [List.length_map]; exact hiC), List.getElem_map]
    rw [hL, ← hlen, getD_flatten_offset _ _ i c (by rw [List.length_map]; exact hiC) (by
      rw [hget, List.length_map]; exact hc), hget,
      getD_of_lt _ _ (by rw [List.length_map]; exact hc), List.getElem_map]
    rfl
  -- the preprocessed trace's openings
  have hprep : A.preprocessedWidth ≠ 0 →
      ((((bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup)).getD 2 []).getD
        ((Is.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1).take i).sum []) =
        (preprocessedPoints A zeta zn).map (Fri.openedAt P.logBlowup pext) := by
    intro hpw
    have hsome : prepLde P.logBlowup A Is[i].logN = some pext := by
      simp only [prepLde, hpw, ↓reduceIte, hpext]
    have hne : (Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN) ≠ [] := by
      intro h0
      have : pext ∈ Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN :=
        List.mem_filterMap.mpr ⟨Is[i], List.getElem_mem hi, hsome⟩
      rw [h0] at this
      exact List.not_mem_nil this
    have hround : ((bRounds EF P Is ts ps).map fun r ↦ r.2.map (openedOf P.logBlowup)).getD 2
        [] = (Is.filterMap fun I ↦ (prepLde P.logBlowup I.air I.logN).map fun e ↦
          (e, preprocessedPoints I.air zeta (bZetaNext EF P Is ts ps I))).map
            (openedOf P.logBlowup) := by
      simp only [bRounds, bPrepRound, bPrep_snd, List.isEmpty_iff, hne, ↓reduceIte,
        Option.map_some, Option.toList_some, List.cons_append, List.nil_append,
        List.map_cons, List.getD_cons_succ, List.getD_cons_zero, bPrep_fst]
      rw [zip_map_filterMap]
    have hcount : ((Is.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1).take i) =
        (Is.take i).map fun I ↦ if ((prepLde P.logBlowup I.air I.logN).map fun e ↦
          (e, preprocessedPoints I.air zeta (bZetaNext EF P Is ts ps I))).isSome then 1 else 0 := by
      rw [← List.map_take]
      refine List.map_congr_left fun I _ ↦ ?_
      by_cases h : I.air.preprocessedWidth = 0 <;> simp only [prepLde, h, ↓reduceIte,
        Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
        Bool.false_eq_true]
    rw [hround, hcount, show ([] : List (Array EF)) = openedOf P.logBlowup (⟨0, 0, #[]⟩, []) from
      rfl, getD_map_of, getD_filterMap_offset _ _ Is i hi (pext, preprocessedPoints A zeta zn)
        (by rw [hsome]; rfl)]
    rfl
  -- the fields
  have hcnt : ((bChunks EF P Is ts ps).map List.length).getD i 0 = chunks.length := by
    rw [getD_of_lt _ _ (by rw [List.length_map]; exact hiC), List.getElem_map]
  unfold instanceOpened honestOpened
  simp only [hmain, hcnt]
  congr 1
  · simp only [tracePoints]; split <;> rfl
  · simp only [tracePoints]; split <;> rfl
  · by_cases hpw : A.preprocessedWidth = 0
    · simp only [hpw, ↓reduceIte]
    · simp only [hpw, ↓reduceIte, hprep hpw, preprocessedPoints]
      split <;> rfl
  · by_cases hn : A.opensPreprocessedNext = true
    · have hpw : A.preprocessedWidth ≠ 0 := by
        simp only [Air.opensPreprocessedNext, Bool.and_eq_true, decide_eq_true_eq] at hn
        omega
      simp only [hn, ↓reduceIte, hprep hpw, preprocessedPoints, List.map_cons, List.map_nil,
        List.getD_cons_succ, List.getD_cons_zero]
      rfl
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
  · refine congrArg List.toArray (List.ext_getElem (by simp only [List.length_map,
      List.length_range]) fun c h1 h2 ↦ ?_)
    simp only [List.getElem_map, List.getElem_range]
    rw [List.length_map, List.length_range] at h1
    exact hchunk c h1

end Honest

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

theorem length_opened : (proveBatch EF P Is ts ps).opened.toList.length = Is.length := by
  rw [proveBatch_eq]
  simp only [List.length_map, List.length_zipIdx]

/-- Every instance's opened values are `uni-stark`'s honest openings. -/
theorem opened_getElem (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < (proveBatch EF P Is ts ps).opened.toList.length) :
    (proveBatch EF P Is ts ps).opened.toList[i] =
      honestOpened P.logBlowup (Is[i]'(by rwa [length_opened] at hi)).air
        (Is[i]'(by rwa [length_opened] at hi)).logN
        ((bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; rwa [length_opened] at hi))
        ((bChunks EF P Is ts ps)[i]'(by
          rw [length_bChunks EF P Is ts ps hts hps]; rwa [length_opened] at hi))
        (bZeta EF P Is ts ps) := by
  have hi' : i < Is.length := by rwa [length_opened] at hi
  rw [← instanceOpened_eq EF P Is ts ps hts hps i hi']
  simp only [proveBatch_eq, List.toList_toArray, List.getElem_map, List.getElem_zipIdx,
    Nat.zero_add]

/-- The common data is the root of the preprocessed traces' commitment. -/
theorem setupBatch_eq : setupBatch P Is = ⟨(bPrep EF P Is).2.map Committed.root⟩ := by
  rw [bPrep_snd]
  unfold setupBatch
  simp only [prepLde]
  split
  · rename_i h; simp only [h, ↓reduceIte, Option.map_none]
  · rename_i h; simp only [h, ↓reduceIte, Option.map_some, Bool.false_eq_true]

end Honest

/-! ### The verifier's rounds -/

theorem zip_filter_map {α β δ : Type} (p : α → Bool) (G : α × β → δ) (G' : α → δ) :
    ∀ (Is : List α) (Os : List β), Os.length = Is.length →
      (∀ i (h : i < Is.length) (h' : i < Os.length), p Is[i] = true →
        G (Is[i], Os[i]) = G' Is[i]) →
      ((Is.zip Os).filter (fun x ↦ p x.1)).map G = (Is.filter p).map G'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, [], h, _ => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | I :: Is, O :: Os, hl, hG => by
    have ih := zip_filter_map p G G' Is Os (by simpa only [List.length_cons,
      Nat.add_right_cancel_iff] using hl) fun i h h' hp ↦ hG (i + 1) (by
        simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) hp
    simp only [List.zip_cons_cons, List.filter_cons]
    by_cases hp : p I = true
    · simp only [hp, ↓reduceIte, List.map_cons, ih]
      exact congrArg₂ List.cons (hG 0 (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega) hp) rfl
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, ih]

theorem filterMap_eq_filter {α β : Type} (f : α → Option β) (p : α → Bool) (g : α → β)
    (h : ∀ a, f a = if p a then some (g a) else none) :
    ∀ l : List α, l.filterMap f = (l.filter p).map g
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, h a, List.filter_cons]
    by_cases hp : p a = true
    · simp only [hp, ↓reduceIte, List.map_cons, filterMap_eq_filter f p g h l]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, filterMap_eq_filter f p g h l]

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- The verifier's rounds of the honest proof are the honest rounds of the prover's openings. -/
theorem batchRounds_eq (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    batchRounds Is (setupBatch P Is) (proveBatch EF P Is ts ps) (bZeta EF P Is ts ps) =
      verifierRounds P.logBlowup (honestRounds P.logBlowup (bRounds EF P Is ts ps)) := by
  have hO := length_opened EF P Is ts ps
  have hE := length_bExts P Is ts hts
  have hC := length_bChunks EF P Is ts ps hts hps
  have hmc : (proveBatch EF P Is ts ps).mainCommit =
      (Committed.ofMats hashF compF (bExts P Is ts)).root := by rw [proveBatch_eq]
  have hqc : (proveBatch EF P Is ts ps).quotientCommit =
      (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root := by rw [proveBatch_eq]
  have hlog : ∀ i (hi : i < Is.length), Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) -
      P.logBlowup = Is[i].logN := fun i hi ↦ by
    rw [Nat.log2_two_pow, Nat.add_sub_cancel]
  unfold batchRounds
  rw [setupBatch_eq (EF := EF), bRounds, honestRounds, verifierRounds]
  simp only [List.map_append, List.map_cons, List.map_nil, hmc, hqc]
  congr 1
  · congr 2
    · refine List.ext_getElem (by simp only [List.length_map, List.length_zip, hO, hE]) ?_
      intro i h1 h2
      have hi : i < Is.length := by
        simp only [List.length_map, List.length_zip, hO, Nat.min_self] at h1; exact h1
      simp only [List.getElem_map, List.getElem_zip]
      rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hi)]
      simp only [getElem_bExts P Is ts hts i hi]
      show (_, _) = ((⟨1, Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) - P.logBlowup⟩ : Domain F), _)
      rw [hlog i hi]
      simp only [traceOpenings, tracePoints, honestOpened, openedOf]
      split <;> rfl
    · rw [List.flatMap_def, List.map_map, List.map_map, List.map_flatten]
      refine congrArg (Prod.mk _) ?_
      refine congrArg List.flatten (List.ext_getElem (by
        simp only [List.length_map, List.length_zip, hO, hC, Nat.min_self]) fun i h1 h2 ↦ ?_)
      have hi : i < Is.length := by
        simp only [List.length_map, List.length_zip, hO, Nat.min_self] at h1; exact h1
      simp only [List.getElem_map, List.getElem_zip]
      rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hi)]
      simp only [honestOpened, List.toList_toArray, List.map_map]
      refine List.map_congr_left fun m hm ↦ ?_
      rw [getElem_bChunks EF P Is ts ps hts hps i hi] at hm
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
      simp only [Function.comp_apply, openedOf, List.map_cons, List.map_nil, List.zip_cons_cons,
        List.zip_nil_left]
      show _ = ((⟨1, Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) - P.logBlowup⟩ : Domain F), _)
      rw [hlog i hi]
  · cases hpr : (bPrep EF P Is).2 with
    | none => simp only [Option.map_none, bPrepRound, hpr, Option.toList_none, List.map_nil]
    | some C =>
      simp only [Option.map_some, bPrepRound, hpr, Option.toList_some, List.map_cons,
        List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
      rw [bPrep_fst, zip_map_filterMap, filterMap_eq_filter _
        (fun I ↦ decide (0 < I.air.preprocessedWidth))
        (fun I ↦ (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed,
          preprocessedPoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I))) (fun I ↦ by
            by_cases h : I.air.preprocessedWidth = 0
            · simp only [prepLde, h, ↓reduceIte, Option.map_none, Nat.lt_irrefl, decide_false,
                Bool.false_eq_true]
            · simp only [prepLde, h, ↓reduceIte, Option.map_some, Nat.pos_of_ne_zero h,
                decide_true])]
      rw [List.map_map, List.map_map]
      refine zip_filter_map (fun I : Instance F ↦ decide (0 < I.air.preprocessedWidth)) _ _ Is _ hO
        fun i hi hi' hp ↦ ?_
      rw [opened_getElem EF P Is ts ps hts hps i hi']
      have hpw : Is[i].air.preprocessedWidth ≠ 0 := by
        simp only [decide_eq_true_eq] at hp; omega
      simp only [honestOpened, hpw, ↓reduceIte, Option.getD_some, Function.comp_apply, openedOf,
        preprocessedPoints]
      show _ = ((⟨1, Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) - P.logBlowup⟩ : Domain F), _)
      rw [hlog i hi]
      split <;> rfl

end Honest

/-! ### The honest rounds -/

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- A matrix of the quotient chunks is an extension of the trace domain's height. -/
theorem height_quotientChunks (A : Air F) (logN : Nat) (ext : Mat F) (pext : Option (Mat F))
    (p : List F) (alpha : EF) :
    ∀ m ∈ quotientChunks (specBackend EF) P A logN ext pext p alpha,
      m.height = 2 ^ (logN + P.logBlowup) := by
  intro m hm
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
  rfl

theorem quotientChunks_ne_nil (A : Air F) (logN : Nat) (ext : Mat F) (pext : Option (Mat F))
    (p : List F) (alpha : EF) : quotientChunks (specBackend EF) P A logN ext pext p alpha ≠ [] := by
  simp only [quotientChunks, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

/-- The prover opens honest rounds. -/
theorem honest_bRounds (hne : Is ≠ []) (hts : ts.length = Is.length)
    (hps : ps.length = Is.length)
    (hfit : ∀ i (hi : i < Is.length), Fits P Is[i].air Is[i].logN (ts[i]'(hts ▸ hi)))
    (hfin : ∀ I ∈ Is, P.logFinalPolyLen ≤ I.logN)
    (hz : Ext.OutsideBase (bZeta EF P Is ts ps)) :
    HonestRounds P (bRounds EF P Is ts ps) := by
  have hE := length_bExts P Is ts hts
  have hC := length_bChunks EF P Is ts ps hts hps
  have hzn : ∀ I ∈ Is, Ext.OutsideBase (bZetaNext EF P Is ts ps I) := fun I hI ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    exact Ext.outsideBase_mul_ofBase hz (BaseField.twoAdicGen_ne_zero _
      (by have := (hfit i hi).twoAdic; omega))
  have htp : ∀ I ∈ Is, tracePoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I) ≠ [] ∧
      ∀ z ∈ tracePoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I),
        Ext.OutsideBase z := fun I hI ↦ by
    simp only [tracePoints]
    split
    · refine ⟨List.cons_ne_nil _ _, fun z hz' ↦ ?_⟩
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hz
      · rw [List.mem_singleton.mp hz']; exact hzn I hI
    · exact ⟨List.cons_ne_nil _ _, fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz⟩
  have hpp : ∀ I ∈ Is, preprocessedPoints I.air (bZeta EF P Is ts ps)
      (bZetaNext EF P Is ts ps I) ≠ [] ∧ ∀ z ∈ preprocessedPoints I.air (bZeta EF P Is ts ps)
        (bZetaNext EF P Is ts ps I), Ext.OutsideBase z := fun I hI ↦ by
    simp only [preprocessedPoints]
    split
    · refine ⟨List.cons_ne_nil _ _, fun z hz' ↦ ?_⟩
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hz
      · rw [List.mem_singleton.mp hz']; exact hzn I hI
    · exact ⟨List.cons_ne_nil _ _, fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz⟩
  obtain ⟨I0, hI0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨i0, hi0, -⟩ := List.getElem_of_mem hI0
  -- the matrices of every round
  have hprepMats : ∀ x ∈ (Is.zip (bPrep EF P Is).1).filterMap (fun (I, pext) ↦
      pext.map fun e ↦ (e, preprocessedPoints I.air (bZeta EF P Is ts ps)
        (bZetaNext EF P Is ts ps I))), ∃ I ∈ Is,
        x = (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed,
          preprocessedPoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I)) := by
    intro x hx
    rw [bPrep_fst, zip_map_filterMap] at hx
    obtain ⟨I, hI, hx⟩ := List.mem_filterMap.mp hx
    refine ⟨I, hI, ?_⟩
    simp only [prepLde] at hx
    split at hx
    · simp only [Option.map_none, reduceCtorEq] at hx
    · simp only [Option.map_some, Option.some.injEq] at hx
      exact hx.symm
  have hprepR : ∀ r ∈ (bPrepRound EF P Is ts ps).toList, ∃ C, (bPrep EF P Is).2 = some C ∧
      r = (C, (Is.zip (bPrep EF P Is).1).filterMap fun (I, pext) ↦ pext.map fun e ↦
        (e, preprocessedPoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I))) := by
    intro r hr
    rw [Option.mem_toList, bPrepRound, Option.map_eq_some_iff] at hr
    obtain ⟨C, hC, rfl⟩ := hr
    exact ⟨C, hC, rfl⟩
  refine ⟨List.cons_ne_nil _ _, fun r hr ↦ ?_, fun r hr x hx ↦ ?_, fun r hr x hx ↦ ?_⟩
  all_goals
    simp only [bRounds, List.cons_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
  · refine ⟨?_, ?_⟩
    · simp only [ne_eq, List.map_eq_nil_iff, List.zip_eq_nil_iff, hne, false_or]
      intro h0; rw [h0] at hE; rw [← hE] at hi0; exact absurd hi0 (Nat.not_lt_zero _)
    · rw [List.map_map]
      simp only [Function.comp_def]
      exact congrArg _ (List.map_snd_zip (l₁ := Is) (l₂ := bExts P Is ts) (by rw [hE])).symm
  · refine ⟨?_, ?_⟩
    · simp only [ne_eq, List.map_eq_nil_iff, List.flatten_eq_nil_iff, not_forall]
      refine ⟨(bChunks EF P Is ts ps)[i0]'(by rw [hC]; exact hi0), List.getElem_mem _, ?_⟩
      rw [getElem_bChunks EF P Is ts ps hts hps i0 hi0]
      exact quotientChunks_ne_nil EF P _ _ _ _ _ _
    · rw [List.map_map]
      simp only [Function.comp_def, List.map_id']
  · obtain ⟨C, hpr, rfl⟩ := hprepR r hr
    · have hC' := hpr
      rw [bPrep_snd] at hC'
      split at hC'
      · exact absurd hC' (by simp only [reduceCtorEq, not_false_eq_true])
      · rename_i hne'
        rw [Option.some.injEq] at hC'
        refine ⟨?_, ?_⟩
        · rw [bPrep_fst, zip_map_filterMap]
          intro h0
          apply hne'
          rw [List.isEmpty_iff, List.filterMap_eq_nil_iff] at *
          intro I hI
          have := h0 I hI
          simpa only [Option.map_eq_none_iff] using this
        · dsimp only
          rw [← hC', bPrep_fst, zip_map_filterMap, List.map_filterMap]
          congr 1
          refine List.filterMap_congr fun I _ ↦ ?_
          cases prepLde P.logBlowup I.air I.logN <;> rfl
  · obtain ⟨⟨I, e⟩, hie, rfl⟩ := List.mem_map.mp hx
    exact htp I (List.of_mem_zip hie).1
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨List.cons_ne_nil _ _, fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz⟩
  · obtain ⟨C, hpr, rfl⟩ := hprepR r hr
    obtain ⟨I, hI, rfl⟩ := hprepMats x hx
    exact hpp I hI
  · obtain ⟨⟨I, e⟩, hie, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, hie'⟩ := List.getElem_of_mem hie
    have hiI : i < Is.length := by
      rw [List.length_zip, hE, Nat.min_self] at hi; exact hi
    rw [List.getElem_zip, Prod.mk.injEq] at hie'
    obtain ⟨rfl, rfl⟩ := hie'
    obtain ⟨ps', hl, -⟩ := trace_lde P Is[i].air Is[i].logN _ (hfit i hiI)
    refine ⟨Is[i].logN + P.logBlowup, ps', ?_, by have := hfin _ (List.getElem_mem hiI); omega⟩
    rw [getElem_bExts P Is ts hts i hiI]
    exact hl
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cs, hcs, hm⟩ := List.mem_flatten.mp hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
    have hiI : i < Is.length := by rw [hC] at hi; exact hi
    rw [getElem_bChunks EF P Is ts ps hts hps i hiI] at hm
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ps', hl, -⟩ := chunk_isLde (EF := EF) P Is[i].air Is[i].logN _
      (hfit i hiI).twoAdic (hfit i hiI).chunks c
    exact ⟨Is[i].logN + P.logBlowup, ps', hl, by have := hfin _ (List.getElem_mem hiI); omega⟩
  · obtain ⟨C, hpr, rfl⟩ := hprepR r hr
    obtain ⟨I, hI, rfl⟩ := hprepMats x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    obtain ⟨ps', hl, -⟩ := prep_lde P Is[i].air Is[i].logN _ (hfit i hi)
    exact ⟨Is[i].logN + P.logBlowup, ps', hl, by have := hfin _ (List.getElem_mem hi); omega⟩

end Honest

/-! ### The verifier -/

/-- The transcript part of `verifyBatch`. -/
def bVerifyRun (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) : M (poseidon2 F) (EF × EF) := do
  observeList (poseidon2 F) (batchSeedOf EF P Is common)
  observeExts (poseidon2 F) (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
  observeList (poseidon2 F) proof.mainCommit.toList
  observeList (poseidon2 F) pis.flatten
  observeList (poseidon2 F) ((common.preprocessed.map (·.toList)).getD [])
  let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  observeList (poseidon2 F) proof.quotientCommit.toList
  ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
  let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  ensure (Is.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0) "out-of-domain point in a trace domain"
  verifyPcs (poseidon2 F) P (batchRounds Is common proof zeta) proof.fri
  return (alpha, zeta)

/-- The constraint checks of `verifyBatch`, after the transcript. -/
def bVerifyCheck (Is : List (Instance F)) (proof : BatchProof F EF) (pis : List (List F))
    (x : (EF × EF) × Transcript F 24) : ExceptT String Id Unit :=
  unless (Is.zip (proof.opened.toList.zip pis)).all fun (I, o, p) ↦
      instanceCheck I o p x.1.2 x.1.1 do
    throw "out-of-domain evaluation mismatch"

theorem verifyBatch_eq (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) :
    verifyBatch P Is common proof pis = ExceptT.run (do
      let n := Is.length
      unless proof.opened.size == n && pis.length == n do
        throw "instance count"
      unless proof.degreeBits.toList == Is.map (·.logN) do
        throw "degree bits"
      unless Is.all fun I ↦ I.logN + I.air.logQuotientChunks I.logN ≤ twoAdicity F do
        throw "quotient domain"
      unless Is.all fun I ↦ I.air.periodicFits I.logN do
        throw "periodic columns"
      unless (Is.zip pis).all fun (I, p) ↦ p.length == I.air.numPublicValues do
        throw "public values"
      unless (Is.zip proof.opened.toList).all fun (I, o) ↦ openedShapeOk I.air o I.logN do
        throw "invalid proof shape"
      unless common.preprocessed.isSome == Is.any (0 < ·.air.preprocessedWidth) do
        throw "preprocessed commitment"
      unless P.oodPowBits != 0 || proof.oodWitness == 0 do
        throw "out-of-domain witness"
      (bVerifyRun P Is common proof pis).run Poseidon2.initTranscript >>=
        bVerifyCheck Is proof pis) := by
  delta verifyBatch verifyBatchWith bVerifyRun bVerifyCheck
  rfl

theorem observeExts_bind {β : Type} (xs : List EF) (f : Unit → M (poseidon2 F) β)
    (t : Transcript F 24) :
    (observeExts (poseidon2 F) xs >>= f) t = f () (t.observeExts xs) :=
  bind_ok (observeExts_run t xs)

/-- The verifier's transcript after the domain separator, the degree bits, the main commitment,
the public values and the preprocessed commitment. -/
def bVTA (P : Params) (Is : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) : Transcript F 24 :=
  ((((Poseidon2.initTranscript.observeList (batchSeedOf EF P Is common)).observeExts
    (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).observeList
      proof.mainCommit.toList).observeList
    pis.flatten).observeList ((common.preprocessed.map (·.toList)).getD [])

/-- The verifier's transcript after the quotient commitment. -/
def bVTC (P : Params) (Is : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) : Transcript F 24 :=
  (Transcript.sampleExtState EF (bVTA P Is common proof pis)).observeList
    proof.quotientCommit.toList

theorem bVerifyRun_run (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) :
    bVerifyRun P Is common proof pis Poseidon2.initTranscript = (do
      ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
      let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      ensure (Is.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
        "out-of-domain point in a trace domain"
      verifyPcs (poseidon2 F) P (batchRounds Is common proof zeta) proof.fri
      pure (((bVTA P Is common proof pis).sampleExtValue : EF), zeta))
        (bVTC P Is common proof pis) := by
  simp only [bVerifyRun, observeList_bind, observeExts_bind, sampleExt_bind]
  rfl

/-- The honest openings have the AIR's shape. -/
theorem openedShapeOk_honest (P : Params) (A : Air F) (logN : Nat) (trace : Array F)
    (pext : Option (Mat F)) (pis : List F) (alpha zeta : EF) :
    openedShapeOk A (honestOpened P.logBlowup A logN (ldeRef logN P.logBlowup gen A.width trace)
      (quotientChunks (specBackend EF) P A logN (ldeRef logN P.logBlowup gen A.width trace) pext
        pis alpha) zeta) logN = true := by
  have hs (m : Stark.Mat F) (z : EF) : (Fri.openedAt P.logBlowup m z).size = m.width := by
    rw [openedAt_eq, Array.size_ofFn]
  simp only [openedShapeOk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨hs _ zeta, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have hw : (ldeRef logN P.logBlowup gen A.width trace).width = A.width := rfl
    simp only [honestOpened, traceNextOk]
    cases hn : A.mainNextRow
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    · simp only [↓reduceIte, hs, hw, beq_self_eq_true, Bool.and_self]
  · simp only [honestOpened, quotientChunks, List.size_toArray, List.length_map, List.length_range]
  · rw [Array.all_eq_true]
    intro i hi
    simp only [honestOpened, quotientChunks, List.getElem_toArray, List.getElem_map, hs,
      beq_iff_eq]
    rfl
  · by_cases hpw : A.preprocessedWidth = 0
    · have hn : A.opensPreprocessedNext = false := by
        simp only [Air.opensPreprocessedNext, hpw, Nat.lt_irrefl, decide_false, Bool.false_and]
      simp only [honestOpened, hpw, hn, ↓reduceIte, beq_self_eq_true, Bool.false_eq_true]
    · have hw : (ldeRef logN P.logBlowup gen A.preprocessedWidth A.preprocessed).width =
          A.preprocessedWidth := rfl
      have h0 : 0 < A.preprocessedWidth := Nat.pos_of_ne_zero hpw
      simp only [honestOpened, hpw, ↓reduceIte]
      cases hn : A.opensPreprocessedNext <;>
        simp only [hs, hw, h0, beq_self_eq_true, Bool.and_true, Bool.not_false,
          decide_true, Bool.false_eq_true, ↓reduceIte]

/-! ### Completeness -/

/-- Batch completeness with every assumption spelled out; `batchCompleteness`
(`CompStark/BatchCompleteness.lean`) groups them. -/
theorem verifyBatch_proveBatch_of (EF : Type) [Challenge F EF] (P : Params)
    (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F)) (hne : Is ≠ [])
    (hts : ts.length = Is.length) (hps : ps.length = Is.length)
    (hfit : ∀ i (hi : i < Is.length), Fits P Is[i].air Is[i].logN (ts[i]'(hts ▸ hi)))
    (hvan : ∀ i (hi : i < Is.length), Is[i].air.ConstraintsVanish Is[i].logN (ts[i]'(hts ▸ hi))
      (ps[i]'(hps ▸ hi)))
    (hpis : ∀ i (hi : i < Is.length), (ps[i]'(hps ▸ hi)).length = Is[i].air.numPublicValues)
    (hdeg : ∀ I ∈ Is, I.air.DegreeFits I.logN) (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries)
    (hb : 0 < P.logBlowup) (hfin : ∀ I ∈ Is, P.logFinalPolyLen ≤ I.logN)
    (hgrind : (proveBatchTranscript EF P Is ts ps).grindFailed = false)
    (hz : Ext.OutsideBase (batchOutOfDomainPoint EF P Is ts ps)) :
    verifyBatch P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps = .ok () := by
  rw [batchOutOfDomainPoint_eq] at hz
  rw [proveBatchTranscript_eq] at hgrind
  have hO := length_opened EF P Is ts ps
  have hcommon := setupBatch_eq (EF := EF) P Is
  have hp := proveBatch_eq EF P Is ts ps
  -- the grinding flag and the duplexes
  have hgO : (bOod EF P Is ts ps).2.grindFailed = false := by
    have := flag_openPcs P (bRounds EF P Is ts ps) _ hgrind
    rwa [flag_sampleExt] at this
  have hdC : (bTC EF P Is ts ps).duplex = Poseidon2.duplex := by
    rw [bTC, duplex_observeList, duplex_sampleExt, bTA, duplex_observeList, duplex_observeList,
      duplex_observeList, duplex_observeExts, duplex_observeList]
    rfl
  have hd2 : (Transcript.sampleExtState EF (bOod EF P Is ts ps).2).duplex = Poseidon2.duplex := by
    rw [duplex_sampleExt, bOod, duplex_grind, hdC]
  -- the verifier's transcript is the prover's
  have hTA : bVTA P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps = bTA EF P Is ts ps := by
    rw [bVTA, bTA, hcommon, hp, Option.map_map]
    rfl
  have hTC : bVTC P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps = bTC EF P Is ts ps := by
    rw [bVTC, hTA, bTC, hp]
  have hcO : checkWitness (poseidon2 F) P.oodPowBits (bOod EF P Is ts ps).1
      (bTC EF P Is ts ps) = .ok (true, (bOod EF P Is ts ps).2) :=
    (checkWitness_run _ _ _ hdC).trans (congrArg Except.ok (checkWitness_grind _ _ hgO))
  have hfitI : ∀ I ∈ Is, I.logN + P.logBlowup ≤ twoAdicity F ∧
      I.air.logQuotientChunks I.logN ≤ P.logBlowup ∧ I.air.periodicFits I.logN = true := by
    intro I hI
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    exact ⟨(hfit i hi).twoAdic, (hfit i hi).chunks, (hfit i hi).periodic⟩
  have hdom : (Is.all fun I ↦ Ext.powTwo (bZeta EF P Is ts ps) I.logN - 1 != 0) = true := by
    rw [List.all_eq_true]
    intro I hI
    exact powTwo_ne_one hz (by have := (hfitI I hI).1; omega)
  have hpcs : verifyPcs (poseidon2 F) P
      (verifierRounds P.logBlowup (honestRounds P.logBlowup (bRounds EF P Is ts ps)))
      (bPcs EF P Is ts ps).1.2 (Transcript.sampleExtState EF (bOod EF P Is ts ps).2) =
      .ok ((), (bPcs EF P Is ts ps).2) :=
    verifyPcs_openPcs P (bRounds EF P Is ts ps) _ hd2
      (honest_bRounds EF P Is ts ps hne hts hps hfit hfin hz) hP hq hb hgrind
  have hrun : bVerifyRun P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps
      Poseidon2.initTranscript =
      .ok ((bAlpha EF P Is ts ps, bZeta EF P Is ts ps), (bPcs EF P Is ts ps).2) := by
    rw [bVerifyRun_run, hTC]
    have how : (proveBatch EF P Is ts ps).oodWitness = (bOod EF P Is ts ps).1 := by rw [hp]
    have hfri : (proveBatch EF P Is ts ps).fri = (bPcs EF P Is ts ps).1.2 := by rw [hp]
    rw [how, bind_ok hcO, ensure_true, pure_bind, bind_ok (sampleExt_run _)]
    have hzeta : ((bOod EF P Is ts ps).2.sampleExtValue : EF) = bZeta EF P Is ts ps := rfl
    rw [hzeta, hdom, ensure_true, pure_bind, batchRounds_eq EF P Is ts ps hts hps, hfri]
    rw [bind_ok hpcs, hTA]
    rfl
  -- the checks
  have hshape : ((Is.zip (proveBatch EF P Is ts ps).opened.toList).all fun x ↦
      openedShapeOk x.1.air x.2 x.1.logN) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by rw [List.length_zip, hO, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip]
    rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hiI),
      getElem_bChunks EF P Is ts ps hts hps i hiI, getElem_bExts P Is ts hts i hiI]
    exact openedShapeOk_honest P _ _ _ _ _ _ _
  have hcheck : ((Is.zip ((proveBatch EF P Is ts ps).opened.toList.zip ps)).all fun x ↦
      instanceCheck x.1 x.2.1 x.2.2 (bZeta EF P Is ts ps) (bAlpha EF P Is ts ps)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by
      rw [List.length_zip, List.length_zip, hO, hps, Nat.min_self, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip]
    rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hiI),
      getElem_bChunks EF P Is ts ps hts hps i hiI, getElem_bExts P Is ts hts i hiI]
    exact checkConstraints_honest P Is[i].air Is[i].logN _ _ _ _ (hfit i hiI) (hvan i hiI)
      (hdeg _ (List.getElem_mem hiI)) hz
  have hprepOk : ((setupBatch P Is).preprocessed.isSome ==
      Is.any (0 < ·.air.preprocessedWidth)) = true := by
    simp only [hcommon, beq_iff_eq, Option.isSome_map, bPrep_snd]
    by_cases h : ∃ I ∈ Is, I.air.preprocessedWidth ≠ 0
    · obtain ⟨I, hI, hpw⟩ := h
      have hne' : (Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff]
        intro h0
        have : ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed ∈
            Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN :=
          List.mem_filterMap.mpr ⟨I, hI, by simp only [prepLde, hpw, ↓reduceIte]⟩
        rw [h0] at this
        exact List.not_mem_nil this
      simp only [hne', Bool.false_eq_true, ↓reduceIte, Option.isSome_some]
      rw [eq_comm, List.any_eq_true]
      exact ⟨I, hI, decide_eq_true (Nat.pos_of_ne_zero hpw)⟩
    · have hall : ∀ I ∈ Is, I.air.preprocessedWidth = 0 := fun I hI ↦ by
        by_contra hc; exact h ⟨I, hI, hc⟩
      have he : (Is.filterMap fun I ↦ prepLde P.logBlowup I.air I.logN).isEmpty = true := by
        rw [List.isEmpty_iff, List.filterMap_eq_nil_iff]
        intro I hI
        simp only [prepLde, hall I hI, ↓reduceIte]
      simp only [he, ↓reduceIte, Option.isSome_none]
      rw [eq_comm, List.any_eq_false]
      intro I hI
      simp only [hall I hI, Nat.lt_irrefl, decide_false, Bool.false_eq_true, not_false_eq_true]
  have hcount : ((proveBatch EF P Is ts ps).opened.size == Is.length && ps.length == Is.length) =
      true := by
    rw [← Array.length_toList, hO, hps, beq_self_eq_true, Bool.and_self]
  have hdb : ((proveBatch EF P Is ts ps).degreeBits.toList == Is.map (·.logN)) = true := by
    rw [hp]; exact beq_self_eq_true _
  have hqd : (Is.all fun I ↦ I.logN + I.air.logQuotientChunks I.logN ≤ twoAdicity F) = true := by
    rw [List.all_eq_true]
    intro I hI
    have := hfitI I hI
    exact decide_eq_true (by omega)
  have hper : (Is.all fun I ↦ I.air.periodicFits I.logN) = true := by
    rw [List.all_eq_true]
    exact fun I hI ↦ (hfitI I hI).2.2
  have hpv : ((Is.zip ps).all fun x ↦ x.2.length == x.1.air.numPublicValues) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by rw [List.length_zip, hps, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip]
    rw [hpis i hiI, beq_self_eq_true]
  have hood : (P.oodPowBits != 0 || (proveBatch EF P Is ts ps).oodWitness == 0) = true := by
    rw [hp]; exact grind_canonical _ _
  rw [verifyBatch_eq]
  simp only [hcount, hdb, hqd, hper, hpv, hshape, hprepOk, hood, ↓reduceIte]
  have hrun' : StateT.run (bVerifyRun P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps)
      Poseidon2.initTranscript = pure ((bAlpha EF P Is ts ps, bZeta EF P Is ts ps),
        (bPcs EF P Is ts ps).2) := hrun
  rw [hrun', pure_bind]
  unfold bVerifyCheck
  simp only [hcheck, ↓reduceIte]
  rfl

end CompStark.Batch
