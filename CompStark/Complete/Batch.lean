/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Pcs
public import CompStark.Complete.LogUpQuotient

/-! # The specification prover's batch proofs verify

The batch-STARK layer of completeness. The verifier replays the prover's transcript: it observes
the same domain separator, degree bits, commitments and public values, checks the same grinding
witnesses, so it samples the same lookup challenges, `α` and `ζ`, and `ζ` off the base field is
off every trace domain. Its rounds are the honest rounds of the prover's openings
(`batchRounds_eq`), on which `verifyPcs` accepts `openPcs`'s proof (`verifyPcs_openPcs`); every
instance's opened values are its honest openings (`opened_getElem`, `permLocal_getElem`), so its
constraint check passes (`instanceCheck_honest`), and balanced buses give terminals summing to
zero (`terminals_sum_eq_zero`).
-/

@[expose] public section
namespace CompStark.Batch
open CompStark.Fri CompStark.Stark CompStark.Complete CompStark.Lookup

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
def bTA0 : Transcript F 24 :=
  ((((Poseidon2.initTranscript.observeList
    (batchSeedOf EF P Is ⟨(bPrep EF P Is).2.map Committed.root⟩)).observeExts
      (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).observeList
    (Committed.ofMats hashF compF (bExts P Is ts)).root.toList).observeList ps.flatten).observeList
    (((bPrep EF P Is).2.map fun c ↦ c.root.toList).getD [])

/-- The lookup phase's run: the grinding witness and the lookup challenges' pair, and the
transcript after them. -/
def bLP : (Option F × EF × EF) × Transcript F 24 :=
  (lookupPair (EF := EF) P Is).run (bTA0 EF P Is ts ps)

/-- Every instance's lookup challenges. -/
def bChs : List (List EF) :=
  challengeLayout (Is.map (·.lookups)) (bLP EF P Is ts ps).1.2.1 (bLP EF P Is ts ps).1.2.2

/-- The permutation traces and terminals. -/
def bPerms : List (Option (Mat F × EF)) :=
  permutationsWith (specBackend EF) P Is ts ps (bChs EF P Is ts ps)

/-- The permutation traces' extensions and commitment. -/
def bPermCP : List (Option (Mat F)) × Option (Committed F) :=
  commitPermutations (specBackend EF) Is (bPerms EF P Is ts ps)

/-- Every instance's terminal, if it has lookups. -/
def bTerms : List (Option EF) := (bPerms EF P Is ts ps).map (·.map (·.2))

/-- The transcript after the permutation commitment and the terminals. -/
def bTA : Transcript F 24 :=
  ((bLP EF P Is ts ps).2.observeList
    (((bPermCP EF P Is ts ps).2.map fun c ↦ c.root.toList).getD [])).observeExts
    ((bTerms EF P Is ts ps).filterMap id)

/-- The constraint-folding challenge. -/
def bAlpha : EF := ((bTA EF P Is ts ps).sampleExtValue : EF)

/-- Every instance's quotient chunks' extensions. -/
def bChunks : List (List (Mat F)) :=
  allQuotientChunks (specBackend EF) P Is (bExts P Is ts) (bPrep EF P Is).1
    (bPermCP EF P Is ts ps).1 ps (bChs EF P Is ts ps) (bTerms EF P Is ts ps) (bAlpha EF P Is ts ps)

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
      (⟨bExts P Is ts, Committed.ofMats hashF compF (bExts P Is ts), bChs EF P Is ts ps,
        (bPermCP EF P Is ts ps).1, (bPermCP EF P Is ts ps).2, bTerms EF P Is ts ps,
        (bLP EF P Is ts ps).1.1, bChunks EF P Is ts ps,
        Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten, bZeta EF P Is ts ps,
        (bOod EF P Is ts ps).1⟩, Transcript.sampleExtState EF (bOod EF P Is ts ps).2) := rfl

theorem batchOutOfDomainPoint_eq :
    batchOutOfDomainPoint EF P Is ts ps = bZeta EF P Is ts ps := rfl

theorem batchLookupChallenges_eq :
    batchLookupChallenges EF P Is ts ps = bChs EF P Is ts ps := rfl

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

/-- The permutation traces' round, if any. -/
def bPermRound : Option (OpenRound (specBackend EF)) :=
  (bPermCP EF P Is ts ps).2.map fun pc ↦ (pc, (Is.zip (bPermCP EF P Is ts ps).1).filterMap
    fun (I, r) ↦ r.map fun e ↦ (e, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps I]))

/-- The rounds the prover opens. -/
def bRounds : List (OpenRound (specBackend EF)) :=
  [(Committed.ofMats hashF compF (bExts P Is ts), (Is.zip (bExts P Is ts)).map fun (I, e) ↦
      (e, tracePoints I.air (bZeta EF P Is ts ps) (bZetaNext EF P Is ts ps I))),
    (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten,
      (bChunks EF P Is ts ps).flatten.map fun m ↦ (m, [bZeta EF P Is ts ps]))] ++
    (bPrepRound EF P Is ts ps).toList ++ (bPermRound EF P Is ts ps).toList

/-- The opening argument's run: the opened values, the FRI proof and the final transcript. -/
def bPcs : (List (List (List (Array EF))) × FriProof F EF) × Transcript F 24 :=
  (openPcs (specBackend EF) P (bRounds EF P Is ts ps)).run
    (Transcript.sampleExtState EF (bOod EF P Is ts ps).2)

/-- Instance `i`'s permutation openings at the `k`-th point: in the permutation round, after
those of the instances before it with lookups. -/
def bPermAt (i k : Nat) : Array EF :=
  let permCounts := Is.map fun I ↦ if I.lookups.isEmpty then 0 else 1
  if permCounts.getD i 0 = 0 then #[]
  else (((bPcs EF P Is ts ps).1.1.getD (if (bPrep EF P Is).2.isSome then 3 else 2) []).getD
    (permCounts.take i).sum []).getD k #[]

theorem proveBatch_eq : proveBatch EF P Is ts ps =
    { mainCommit := (Committed.ofMats hashF compF (bExts P Is ts)).root
      permutationCommit := (bPermCP EF P Is ts ps).2.map Committed.root
      quotientCommit := (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root
      opened := (Is.zipIdx.map fun (I, i) ↦ instanceOpened I.air (bPcs EF P Is ts ps).1.1 i
        (((bChunks EF P Is ts ps).map List.length).getD i 0)
        (((bChunks EF P Is ts ps).map List.length).take i).sum
        ((Is.map fun I ↦ if I.air.preprocessedWidth = 0 then 0 else 1).take i).sum).toArray
      permutationLocal := ((List.range Is.length).map (bPermAt EF P Is ts ps · 0)).toArray
      permutationNext := ((List.range Is.length).map (bPermAt EF P Is ts ps · 1)).toArray
      fri := (bPcs EF P Is ts ps).1.2
      lookupTerminals := (bTerms EF P Is ts ps).toArray
      degreeBits := (Is.map (·.logN)).toArray
      lookupWitness := (bLP EF P Is ts ps).1.1
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

/-- The specification's terminals are the permutation traces'. -/
theorem terminals_permutationsWith (chs : List (List EF)) :
    (permutationsWith (specBackend EF) P Is ts ps chs).map (·.map (·.2)) =
      (permutations Is ts ps chs).map (·.map (·.2)) := by
  simp only [permutationsWith, permutations, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  simp only [Function.comp_apply]
  split <;> rfl

theorem length_bChs : (bChs EF P Is ts ps).length = Is.length := by
  rw [bChs, length_challengeLayout, List.length_map]

theorem length_bPerms (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    (bPerms EF P Is ts ps).length = Is.length := by
  rw [bPerms, permutationsWith, List.length_map, List.length_zip, List.length_zip, List.length_zip,
    hts, hps, length_bChs]
  simp only [Nat.min_self]

theorem getElem_bPerms (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) :
    (bPerms EF P Is ts ps)[i]'(by rw [length_bPerms EF P Is ts ps hts hps]; exact hi) =
      if Is[i].lookups.isEmpty then none else some (permutationLdeOf P.logBlowup Is[i].air
        Is[i].lookups Is[i].logN (ts[i]'(by rw [hts]; exact hi)) (ps[i]'(by rw [hps]; exact hi))
        ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi))) := by
  simp only [bPerms, permutationsWith, List.getElem_map, List.getElem_zip]

theorem length_bPermExts (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    (bPermCP EF P Is ts ps).1.length = Is.length := by
  rw [bPermCP, commitPermutations, List.length_map, length_bPerms EF P Is ts ps hts hps]

theorem getElem_bPermExts (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) :
    (bPermCP EF P Is ts ps).1[i]'(by rw [length_bPermExts EF P Is ts ps hts hps]; exact hi) =
      permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hi)) (ps[i]'(by rw [hps]; exact hi))
        ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi)) := by
  simp only [bPermCP, commitPermutations, List.getElem_map]
  rw [getElem_bPerms EF P Is ts ps hts hps i hi]
  unfold permLde
  split <;> rfl

theorem length_bTerms (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    (bTerms EF P Is ts ps).length = Is.length := by
  rw [bTerms, List.length_map, length_bPerms EF P Is ts ps hts hps]

theorem length_bChunks (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    (bChunks EF P Is ts ps).length = Is.length := by
  rw [bChunks, allQuotientChunks, parMap_eq, List.length_map, List.length_zip, List.length_zip,
    List.length_zip, List.length_zip, List.length_zip, List.length_zip,
    length_bExts P Is ts hts, bPrep_fst, List.length_map, hps,
    length_bPermExts EF P Is ts ps hts hps,
    length_bChs, length_bTerms EF P Is ts ps hts hps]
  simp only [Nat.min_self]

theorem getElem_bChunks (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) :
    (bChunks EF P Is ts ps)[i]'(by rw [length_bChunks EF P Is ts ps hts hps]; exact hi) =
      honestChunks P Is[i] (ts[i]'(by rw [hts]; exact hi)) (ps[i]'(by rw [hps]; exact hi))
        ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi)) (bAlpha EF P Is ts ps) := by
  have e : (bChunks EF P Is ts ps)[i]'(by rw [length_bChunks EF P Is ts ps hts hps]; exact hi) =
      batchQuotientChunks (specBackend EF) P Is[i]
        ((bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; exact hi))
        (((bPrep EF P Is).1)[i]'(by rw [bPrep_fst, List.length_map]; exact hi))
        ((bPermCP EF P Is ts ps).1[i]'(by rw [length_bPermExts EF P Is ts ps hts hps]; exact hi))
        (ps[i]'(by rw [hps]; exact hi)) ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi))
        (((bTerms EF P Is ts ps)[i]'(by rw [length_bTerms EF P Is ts ps hts hps]; exact hi)).getD 0)
        (bAlpha EF P Is ts ps) := by
    simp only [bChunks, allQuotientChunks, parMap_eq, List.getElem_map, List.getElem_zip]
  rw [e, getElem_bExts P Is ts hts i hi, getElem_bPermExts EF P Is ts ps hts hps i hi]
  have hp : ((bPrep EF P Is).1)[i]'(by rw [bPrep_fst, List.length_map]; exact hi) =
      prepLde P.logBlowup Is[i].air Is[i].logN := by
    simp only [bPrep_fst, List.getElem_map]
  rw [hp]
  unfold honestChunks batchQuotientChunks batchQuotientValues
  congr 2
  simp only [bTerms, List.getElem_map]
  rw [getElem_bPerms EF P Is ts ps hts hps i hi]
  unfold permLde
  by_cases he : Is[i].lookups.isEmpty = true
  · simp only [he, ↓reduceIte]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some]
    rfl

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

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

theorem bPermCP_snd : (bPermCP EF P Is ts ps).2 = if hasLookups Is then
    some (Committed.ofMats hashF compF ((bPermCP EF P Is ts ps).1.filterMap id)) else none := rfl

/-- The permutation openings of an instance with lookups are its honest permutation trace's. -/
theorem bPermAt_eq (hts : ts.length = Is.length) (hps : ps.length = Is.length) (i : Nat)
    (hi : i < Is.length) (m : Mat F)
    (hm : permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hi)) (ps[i]'(by rw [hps]; exact hi))
      ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi)) = some m) :
    bPermAt EF P Is ts ps i 0 = Fri.openedAt P.logBlowup m (bZeta EF P Is ts ps) ∧
      bPermAt EF P Is ts ps i 1 = Fri.openedAt P.logBlowup m (bZetaNext EF P Is ts ps Is[i]) := by
  have he : Is[i].lookups.isEmpty = false := by
    unfold permLde at hm
    by_contra h
    simp only [Bool.not_eq_false] at h
    simp only [h, ↓reduceIte, reduceCtorEq] at hm
  have hl : hasLookups Is = true := List.any_eq_true.mpr ⟨Is[i], List.getElem_mem hi, by
    rw [he]; rfl⟩
  have hPl := length_bPermExts EF P Is ts ps hts hps
  set pe := (bPermCP EF P Is ts ps).1
  have hiz : i < (Is.zip pe).length := by rw [List.length_zip, hPl, Nat.min_self]; exact hi
  have hf : (fun x : Instance F × Option (Mat F) ↦ x.2.map fun e ↦
      (e, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps x.1])) (Is.zip pe)[i] =
      some (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps Is[i]]) := by
    simp only [List.getElem_zip]
    rw [getElem_bPermExts EF P Is ts ps hts hps i hi, hm]
    rfl
  have hround : (bPcs EF P Is ts ps).1.1.getD (if (bPrep EF P Is).2.isSome then 3 else 2) [] =
      ((Is.zip pe).filterMap fun x ↦ x.2.map fun e ↦
        (e, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps x.1])).map (openedOf P.logBlowup) := by
    rw [bPcs_opened]
    cases hp : (bPrep EF P Is).2 with
    | none =>
      simp only [bRounds, bPrepRound, bPermRound, hp, bPermCP_snd, hl, ↓reduceIte,
        Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        Option.isSome_none, Bool.false_eq_true, List.cons_append, List.nil_append,
        List.append_nil, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
      rfl
    | some _ =>
      simp only [bRounds, bPrepRound, bPermRound, hp, bPermCP_snd, hl, ↓reduceIte,
        Option.map_some, Option.toList_some, Option.isSome_some, List.cons_append,
        List.nil_append, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
      rfl
  have hcount : ((Is.map fun I ↦ if I.lookups.isEmpty then 0 else 1).take i).sum =
      (((Is.zip pe).take i).map fun x ↦ if (x.2.map fun e ↦
        (e, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps x.1])).isSome then 1 else 0).sum := by
    congr 1
    refine List.ext_getElem (by simp only [List.length_take, List.length_map, List.length_zip,
      hPl, Nat.min_self]) fun j h1 h2 ↦ ?_
    simp only [List.length_take, List.length_map] at h1
    have hj : j < Is.length := by omega
    simp only [List.getElem_take, List.getElem_map, List.getElem_zip, Option.isSome_map]
    rw [getElem_bPermExts EF P Is ts ps hts hps j hj]
    unfold permLde
    split <;> rfl
  have hcnt : (Is.map fun I ↦ if I.lookups.isEmpty then 0 else 1).getD i 0 = 1 := by
    rw [getD_of_lt _ _ (by rw [List.length_map]; exact hi), List.getElem_map, he]
    rfl
  have hget : ((bPcs EF P Is ts ps).1.1.getD (if (bPrep EF P Is).2.isSome then 3 else 2) []).getD
      ((Is.map fun I ↦ if I.lookups.isEmpty then 0 else 1).take i).sum [] =
      openedOf P.logBlowup (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps Is[i]]) := by
    rw [hround, hcount, show ([] : List (Array EF)) = openedOf P.logBlowup (⟨0, 0, #[]⟩, []) from
      rfl, getD_map_of, getD_filterMap_offset _ _ (Is.zip pe) i hiz _ hf]
  unfold bPermAt
  simp only [hcnt, Nat.one_ne_zero, ↓reduceIte, hget, openedOf, List.map_cons, List.map_nil]
  exact ⟨rfl, rfl⟩

/-- An instance without lookups has no permutation openings. -/
theorem bPermAt_empty (i k : Nat) (hi : i < Is.length) (he : Is[i].lookups.isEmpty = true) :
    bPermAt EF P Is ts ps i k = #[] := by
  have h0 : (Is.map fun I ↦ if I.lookups.isEmpty then 0 else 1).getD i 0 = 0 := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map, he]
    rfl
  unfold bPermAt
  simp only [h0, ↓reduceIte]

end Honest

theorem map_filterMap_zip_eq {α β γ δ ε : Type} (f : α × β → Option γ) (H : γ → ε)
    (p : α → Bool) (G : α × δ → ε) : ∀ (A : List α) (B : List β) (C : List δ),
    B.length = A.length → C.length = A.length →
    (∀ i (hi : i < A.length) (hB : i < B.length) (hC : i < C.length),
      (p A[i] = true → ∃ y, f (A[i], B[i]) = some y ∧ H y = G (A[i], C[i])) ∧
        (p A[i] = false → f (A[i], B[i]) = none)) →
    ((A.zip B).filterMap f).map H = ((A.zip C).filter fun x ↦ p x.1).map G
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, h, _, _ => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _ :: _, [], _, h, _ =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | a :: A, b :: B, c :: C, hB, hC, h => by
    have ih := map_filterMap_zip_eq f H p G A B C
      (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hB)
      (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hC)
      fun i hi hb hc ↦ h (i + 1) (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
    have h0 := h 0 (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_zero] at h0
    simp only [List.zip_cons_cons, List.filterMap_cons, List.filter_cons]
    cases hp : p a
    · rw [h0.2 hp]
      simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · obtain ⟨y, hy, hH⟩ := h0.1 hp
      rw [hy]
      simp only [↓reduceIte, List.map_cons, hH, ih]

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- The verifier's permutation round of a proof with the honest permutation commitment and
openings is the honest one. -/
theorem perm_rounds_eq (hts : ts.length = Is.length) (hps : ps.length = Is.length)
    (pf : BatchProof F EF)
    (hpc : pf.permutationCommit = (bPermCP EF P Is ts ps).2.map Committed.root)
    (hpl : pf.permutationLocal.toList = (List.range Is.length).map (bPermAt EF P Is ts ps · 0))
    (hpn : pf.permutationNext.toList = (List.range Is.length).map (bPermAt EF P Is ts ps · 1)) :
    (match pf.permutationCommit with
      | some root => [(root, ((Is.zip (pf.permutationLocal.toList.zip
          pf.permutationNext.toList)).filter (!·.1.lookups.isEmpty)).map
            fun (I, l, n) ↦ ((⟨1, I.logN⟩ : Domain F), [(bZeta EF P Is ts ps, l.toList),
              (bZeta EF P Is ts ps * Ext.ofBase (twoAdicGen I.logN), n.toList)]))]
      | none => []) =
      ((bPermRound EF P Is ts ps).toList.map fun r ↦
        (r.1, r.2.map fun x ↦ (x.1, x.2.zip (openedOf P.logBlowup x)))).map fun r ↦
        (r.1.root, r.2.map fun x ↦
          ((⟨1, Nat.log2 x.1.height - P.logBlowup⟩ : Domain F), x.2.map fun y ↦
            (y.1, y.2.toList))) := by
  rw [hpc, hpl, hpn]
  cases hC : (bPermCP EF P Is ts ps).2 with
  | none => simp only [bPermRound, hC, Option.map_none, Option.toList_none, List.map_nil]
  | some C =>
    simp only [bPermRound, hC, Option.map_some, Option.toList_some, List.map_cons, List.map_nil,
      List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    rw [List.map_map]
    refine (map_filterMap_zip_eq _ _ (fun I : Instance F ↦ !I.lookups.isEmpty) _ Is _ _
      (length_bPermExts EF P Is ts ps hts hps) (by
        rw [List.length_zip, List.length_map, List.length_map, List.length_range,
          Nat.min_self]) fun i hi hB hC ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩).symm
    · have he : Is[i].lookups.isEmpty = false := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hp; exact hp
      have hm := getElem_bPermExts EF P Is ts ps hts hps i hi
      obtain ⟨m, hm'⟩ : ∃ m, permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hi))
          (ps[i]'(by rw [hps]; exact hi))
          ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi)) = some m := by
        unfold permLde
        simp only [he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, exists_eq']
      obtain ⟨h0, h1⟩ := bPermAt_eq EF P Is ts ps hts hps i hi m hm'
      have hh : m.height = 2 ^ (Is[i].logN + P.logBlowup) := by
        unfold permLde at hm'
        simp only [he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hm'
        rw [← hm']; rfl
      refine ⟨(m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps Is[i]]), ?_, ?_⟩
      · simp only [hm, hm', Option.map_some]
      · simp only [Function.comp_apply, List.getElem_zip, List.getElem_map, List.getElem_range,
          openedOf, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left, h0, h1, hh,
          Nat.log2_two_pow, Nat.add_sub_cancel]
        rfl
    · have he : Is[i].lookups.isEmpty = true := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hp; exact hp
      simp only [getElem_bPermExts EF P Is ts ps hts hps i hi, permLde, he, ↓reduceIte,
        Option.map_none]

end Honest

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

/-- The verifier's rounds of a proof with the honest commitments and openings are the honest
rounds of the prover's openings. -/
theorem batchRounds_eq_of (hts : ts.length = Is.length) (hps : ps.length = Is.length)
    (pf : BatchProof F EF) (hO : pf.opened.toList.length = Is.length)
    (hmc : pf.mainCommit = (Committed.ofMats hashF compF (bExts P Is ts)).root)
    (hqc : pf.quotientCommit = (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root)
    (hpc : pf.permutationCommit = (bPermCP EF P Is ts ps).2.map Committed.root)
    (hpl : pf.permutationLocal.toList = (List.range Is.length).map (bPermAt EF P Is ts ps · 0))
    (hpn : pf.permutationNext.toList = (List.range Is.length).map (bPermAt EF P Is ts ps · 1))
    (hop : ∀ i (hi : i < pf.opened.toList.length), pf.opened.toList[i] =
      honestOpened P.logBlowup (Is[i]'(by rwa [hO] at hi)).air (Is[i]'(by rwa [hO] at hi)).logN
        ((bExts P Is ts)[i]'(by rw [length_bExts P Is ts hts]; rwa [hO] at hi))
        ((bChunks EF P Is ts ps)[i]'(by
          rw [length_bChunks EF P Is ts ps hts hps]; rwa [hO] at hi))
        (bZeta EF P Is ts ps)) :
    batchRounds Is (setupBatch P Is) pf (bZeta EF P Is ts ps) =
      verifierRounds P.logBlowup (honestRounds P.logBlowup (bRounds EF P Is ts ps)) := by
  have hE := length_bExts P Is ts hts
  have hC := length_bChunks EF P Is ts ps hts hps
  have hlog : ∀ i (hi : i < Is.length), Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) -
      P.logBlowup = Is[i].logN := fun i hi ↦ by
    rw [Nat.log2_two_pow, Nat.add_sub_cancel]
  unfold batchRounds
  dsimp only
  rw [setupBatch_eq (EF := EF), bRounds, honestRounds, verifierRounds, List.map_append,
    List.map_append]
  congr 1
  swap
  · exact perm_rounds_eq EF P Is ts ps hts hps pf hpc hpl hpn
  simp only [List.map_append, List.map_cons, List.map_nil, hmc, hqc]
  congr 1
  · congr 2
    · refine List.ext_getElem (by simp only [List.length_map, List.length_zip, hO, hE]) ?_
      intro i h1 h2
      have hi : i < Is.length := by
        simp only [List.length_map, List.length_zip, hO, Nat.min_self] at h1; exact h1
      simp only [List.getElem_map, List.getElem_zip]
      rw [hop i (by rw [hO]; exact hi)]
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
      rw [hop i (by rw [hO]; exact hi)]
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
      rw [hop i hi']
      have hpw : Is[i].air.preprocessedWidth ≠ 0 := by
        simp only [decide_eq_true_eq] at hp; omega
      simp only [honestOpened, hpw, ↓reduceIte, Option.getD_some, Function.comp_apply, openedOf,
        preprocessedPoints]
      show _ = ((⟨1, Nat.log2 (2 ^ (Is[i].logN + P.logBlowup)) - P.logBlowup⟩ : Domain F), _)
      rw [hlog i hi]
      split <;> rfl

/-- The verifier's rounds of the honest proof are the honest rounds of the prover's openings. -/
theorem batchRounds_eq (hts : ts.length = Is.length) (hps : ps.length = Is.length) :
    batchRounds Is (setupBatch P Is) (proveBatch EF P Is ts ps) (bZeta EF P Is ts ps) =
      verifierRounds P.logBlowup (honestRounds P.logBlowup (bRounds EF P Is ts ps)) :=
  batchRounds_eq_of EF P Is ts ps hts hps _ (length_opened EF P Is ts ps)
    (by rw [proveBatch_eq]) (by rw [proveBatch_eq]) (by rw [proveBatch_eq])
    (by rw [proveBatch_eq]) (by rw [proveBatch_eq]) (opened_getElem EF P Is ts ps hts hps)

end Honest

/-! ### The honest rounds -/

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- A chunk of an instance's quotient is an extension of the trace domain's height. -/
theorem mem_honestChunks (I : Instance F) (t : Array F) (p : List F) (chs : List EF) (alpha : EF)
    (m : Mat F) (hm : m ∈ honestChunks P I t p chs alpha) :
    ∃ c < 2 ^ I.logQuotientChunks, m = ldeRef I.logN P.logBlowup
      (gen * (gen * powF (twoAdicGen (I.logN + I.logQuotientChunks)) c)⁻¹) (Challenge.d EF)
      (chunkValues (batchQuotientValues (specBackend EF) I
        (ldeRef I.logN P.logBlowup gen I.air.width t) (prepLde P.logBlowup I.air I.logN)
        (permLde P.logBlowup I t p chs) p chs (permutationTrace I.air I.lookups I.logN t p chs).2
          alpha) (2 ^ I.logQuotientChunks) c (2 ^ I.logN)) := by
  unfold honestChunks batchQuotientChunks chunksOf at hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact ⟨c, List.mem_range.mp hc, rfl⟩

theorem honestChunks_ne_nil (I : Instance F) (t : Array F) (p : List F) (chs : List EF)
    (alpha : EF) : honestChunks P I t p chs alpha ≠ [] := by
  unfold honestChunks batchQuotientChunks chunksOf
  rw [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact (Nat.two_pow_pos _).ne'

/-- The matrices of the permutation round are the permutation traces' extensions. -/
theorem map_fst_filterMap_zip {ι μ β : Type} (pts : ι → β) : ∀ (l : List ι)
    (pe : List (Option μ)), pe.length = l.length →
    ((l.zip pe).filterMap fun (I, r) ↦ r.map fun e ↦ (e, pts I)).map (·.1) = pe.filterMap id
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, [], h => absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | I :: l, r :: pe, h => by
    have ih := map_fst_filterMap_zip pts l pe (by simpa only [List.length_cons,
      Nat.add_right_cancel_iff] using h)
    simp only [List.zip_cons_cons, List.filterMap_cons]
    cases r with
    | none => simpa only [Option.map_none, id] using ih
    | some e => simp only [Option.map_some, id, List.map_cons, ih]

/-- The prover opens honest rounds. -/
theorem honest_bRounds (hne : Is ≠ []) (hts : ts.length = Is.length)
    (hps : ps.length = Is.length)
    (hfit : ∀ i (hi : i < Is.length), Fits P Is[i].air Is[i].logN (ts[i]'(hts ▸ hi)))
    (hlc : ∀ I ∈ Is, I.logQuotientChunks ≤ P.logBlowup)
    (hfin : ∀ I ∈ Is, P.logFinalPolyLen ≤ I.logN)
    (hz : Ext.OutsideBase (bZeta EF P Is ts ps)) :
    HonestRounds P (bRounds EF P Is ts ps) := by
  have hE := length_bExts P Is ts hts
  have hC := length_bChunks EF P Is ts ps hts hps
  have hPl := length_bPermExts EF P Is ts ps hts hps
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
  have hpermR : ∀ r ∈ (bPermRound EF P Is ts ps).toList, ∃ C, (bPermCP EF P Is ts ps).2 = some C ∧
      r = (C, (Is.zip (bPermCP EF P Is ts ps).1).filterMap fun (I, e) ↦ e.map fun m ↦
        (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps I])) := by
    intro r hr
    rw [Option.mem_toList, bPermRound, Option.map_eq_some_iff] at hr
    obtain ⟨C, hC, rfl⟩ := hr
    exact ⟨C, hC, rfl⟩
  have hpermMats : ∀ x ∈ (Is.zip (bPermCP EF P Is ts ps).1).filterMap (fun (I, e) ↦
      e.map fun m ↦ (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps I])), ∃ i,
      ∃ hi : i < Is.length, ∃ m, permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hi))
        (ps[i]'(by rw [hps]; exact hi)) ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi))
        = some m ∧ x = (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps Is[i]]) := by
    intro x hx
    obtain ⟨y, hy, hx⟩ := List.mem_filterMap.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have hiI : i < Is.length := by rw [List.length_zip, hPl, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip] at hx
    rw [getElem_bPermExts EF P Is ts ps hts hps i hiI] at hx
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨i, hiI, m, hm, rfl⟩
  have hlde : ∀ i (hi : i < Is.length) (m : Mat F), permLde P.logBlowup Is[i]
      (ts[i]'(by rw [hts]; exact hi)) (ps[i]'(by rw [hps]; exact hi))
      ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hi)) = some m →
      ∃ h ps', CompStark.Mat.IsLde P.logBlowup h m ps' ∧ P.logBlowup + P.logFinalPolyLen ≤ h := by
    intro i hi m hm
    unfold permLde at hm
    split at hm
    · exact absurd hm (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [Option.some.injEq] at hm
      subst hm
      obtain ⟨ps', hl, -⟩ := matrix_lde P.logBlowup Is[i].logN _ _ (hfit i hi).twoAdic
      exact ⟨Is[i].logN + P.logBlowup, ps', hl, by have := hfin _ (List.getElem_mem hi); omega⟩
  refine ⟨List.cons_ne_nil _ _, fun r hr ↦ ?_, fun r hr x hx ↦ ?_, fun r hr x hx ↦ ?_⟩
  all_goals
    rw [bRounds, List.mem_append, List.mem_append, List.mem_cons, List.mem_cons] at hr
    rcases hr with ((rfl | rfl | hr) | hr) | hr
  -- commits
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
      exact honestChunks_ne_nil EF P _ _ _ _ _
    · rw [List.map_map]
      simp only [Function.comp_def, List.map_id']
  · exact absurd hr List.not_mem_nil
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
  · obtain ⟨C, hpc, rfl⟩ := hpermR r hr
    have hl : hasLookups Is = true := by
      rw [bPermCP_snd] at hpc
      by_contra h
      simp only [Bool.not_eq_true] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hpc
    have hmeq := map_fst_filterMap_zip (fun I ↦ [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps I])
      Is _ hPl
    refine ⟨?_, ?_⟩
    · obtain ⟨I, hI, hlk⟩ := List.any_eq_true.mp hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
      intro h0
      have : ((Is.zip (bPermCP EF P Is ts ps).1).filterMap fun (I, e) ↦ e.map fun m ↦
          (m, [bZeta EF P Is ts ps, bZetaNext EF P Is ts ps I])).map (·.1) = [] := by
        dsimp only at h0
        rw [h0]; rfl
      rw [hmeq, List.filterMap_eq_nil_iff] at this
      have h1 := this _ (List.getElem_mem (by rw [hPl]; exact hi))
      rw [getElem_bPermExts EF P Is ts ps hts hps i hi, permLde] at h1
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hlk
      simp only [hlk, Bool.false_eq_true, ↓reduceIte, id, reduceCtorEq] at h1
    · dsimp only
      rw [hmeq]
      rw [bPermCP_snd, ite_eq_left_of_eq_true _ _ (eq_true hl), Option.some.injEq] at hpc
      exact hpc.symm
  -- points
  · obtain ⟨⟨I, e⟩, hie, rfl⟩ := List.mem_map.mp hx
    exact htp I (List.of_mem_zip hie).1
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨List.cons_ne_nil _ _, fun z hz' ↦ (List.mem_singleton.mp hz') ▸ hz⟩
  · exact absurd hr List.not_mem_nil
  · obtain ⟨C, hpr, rfl⟩ := hprepR r hr
    obtain ⟨I, hI, rfl⟩ := hprepMats x hx
    exact hpp I hI
  · obtain ⟨C, hpc, rfl⟩ := hpermR r hr
    obtain ⟨i, hi, m, -, rfl⟩ := hpermMats x hx
    refine ⟨List.cons_ne_nil _ _, fun z hz' ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl
    · exact hz
    · exact hzn _ (List.getElem_mem hi)
  -- extensions
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
    obtain ⟨c, -, rfl⟩ := mem_honestChunks EF P _ _ _ _ _ m hm
    obtain ⟨ps', hl, -⟩ := chunk_isLde (EF := EF) P Is[i].logN _ _
      (hfit i hiI).twoAdic (hlc _ (List.getElem_mem hiI)) c
    exact ⟨Is[i].logN + P.logBlowup, ps', hl, by have := hfin _ (List.getElem_mem hiI); omega⟩
  · exact absurd hr List.not_mem_nil
  · obtain ⟨C, hpr, rfl⟩ := hprepR r hr
    obtain ⟨I, hI, rfl⟩ := hprepMats x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    obtain ⟨ps', hl, -⟩ := prep_lde P Is[i].air Is[i].logN _ (hfit i hi)
    exact ⟨Is[i].logN + P.logBlowup, ps', hl, by have := hfin _ (List.getElem_mem hi); omega⟩
  · obtain ⟨C, hpc, rfl⟩ := hpermR r hr
    obtain ⟨i, hi, m, hm, rfl⟩ := hpermMats x hx
    exact hlde i hi m hm

end Honest

/-! ### The verifier -/

/-- The transcript part of `verifyBatch`. -/
def bVerifyRun (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) : M (poseidon2 F) (EF × EF × EF × EF) := do
  observeList (poseidon2 F) (batchSeedOf EF P Is common)
  observeExts (poseidon2 F) (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))
  observeList (poseidon2 F) proof.mainCommit.toList
  observeList (poseidon2 F) pis.flatten
  observeList (poseidon2 F) ((common.preprocessed.map (·.toList)).getD [])
  let (lookupAlpha, lookupBeta) ← lookupPhase P Is proof
  let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  observeList (poseidon2 F) proof.quotientCommit.toList
  ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
  let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
  ensure (Is.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0) "out-of-domain point in a trace domain"
  verifyPcs (poseidon2 F) P (batchRounds Is common proof zeta) proof.fri
  return (lookupAlpha, lookupBeta, alpha, zeta)

/-- The constraint checks and the terminals' sum of `verifyBatch`, after the transcript. -/
def bVerifyCheck (Is : List (Instance F)) (proof : BatchProof F EF) (pis : List (List F))
    (x : (EF × EF × EF × EF) × Transcript F 24) : ExceptT String Id Unit := do
  unless (Is.zipIdx.zip (proof.opened.toList.zip pis)).all fun ((I, i), o, p) ↦
      instanceCheck I o p (proof.permutationLocal.getD i #[]) (proof.permutationNext.getD i #[])
        ((challengeLayout (Is.map (·.lookups)) x.1.1 x.1.2.1).getD i [])
        ((proof.lookupTerminals.getD i none).getD 0) x.1.2.2.2 x.1.2.2.1 do
    throw "out-of-domain evaluation mismatch"
  unless (proof.lookupTerminals.toList.filterMap id).foldl (· + ·) 0 == 0 do
    throw "lookup terminals do not sum to zero"

theorem verifyBatch_eq (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) :
    verifyBatch P Is common proof pis = ExceptT.run (do
      let n := Is.length
      unless proof.opened.size == n && pis.length == n && proof.permutationLocal.size == n &&
          proof.permutationNext.size == n && proof.lookupTerminals.size == n do
        throw "instance count"
      unless proof.degreeBits.toList == Is.map (·.logN) do
        throw "degree bits"
      unless Is.all fun I ↦ I.logN + I.logQuotientChunks ≤ twoAdicity F do
        throw "quotient domain"
      unless Is.all fun I ↦ I.air.periodicFits I.logN do
        throw "periodic columns"
      unless (Is.zip pis).all fun (I, p) ↦ p.length == I.air.numPublicValues do
        throw "public values"
      unless (Is.zip proof.opened.toList).all fun (I, o) ↦ openedShapeOk I o do
        throw "invalid proof shape"
      unless common.preprocessed.isSome == Is.any (0 < ·.air.preprocessedWidth) do
        throw "preprocessed commitment"
      unless lookupShapeOk P Is proof do
        throw "lookups"
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
def bVTA0 (P : Params) (Is : List (Instance F)) (common : Common F) (proof : BatchProof F EF)
    (pis : List (List F)) : Transcript F 24 :=
  ((((Poseidon2.initTranscript.observeList (batchSeedOf EF P Is common)).observeExts
    (Is.map fun I ↦ (Ext.ofBase (I.logN : F) : EF))).observeList
      proof.mainCommit.toList).observeList
    pis.flatten).observeList ((common.preprocessed.map (·.toList)).getD [])

theorem bVerifyRun_run (P : Params) (Is : List (Instance F)) (common : Common F)
    (proof : BatchProof F EF) (pis : List (List F)) :
    bVerifyRun P Is common proof pis Poseidon2.initTranscript = (do
      let (lookupAlpha, lookupBeta) ← lookupPhase P Is proof
      let alpha ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      observeList (poseidon2 F) proof.quotientCommit.toList
      ensure (← checkWitness (poseidon2 F) P.oodPowBits proof.oodWitness) "out-of-domain witness"
      let zeta ← (sampleExt (poseidon2 F) : M (poseidon2 F) EF)
      ensure (Is.all fun I ↦ Ext.powTwo zeta I.logN - 1 != 0)
        "out-of-domain point in a trace domain"
      verifyPcs (poseidon2 F) P (batchRounds Is common proof zeta) proof.fri
      pure (lookupAlpha, lookupBeta, alpha, zeta)) (bVTA0 P Is common proof pis) := by
  simp only [bVerifyRun, observeList_bind, observeExts_bind]
  rfl

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

theorem bLP_eq : bLP EF P Is ts ps = if hasLookups Is then
    ((some ((bTA0 EF P Is ts ps).grind P.lookupPowBits).1,
      (((bTA0 EF P Is ts ps).grind P.lookupPowBits).2.sampleExtValue : EF),
      ((Transcript.sampleExtState EF ((bTA0 EF P Is ts ps).grind P.lookupPowBits).2).sampleExtValue
        : EF)),
      Transcript.sampleExtState EF (Transcript.sampleExtState EF
        ((bTA0 EF P Is ts ps).grind P.lookupPowBits).2))
    else ((none, 0, 0), bTA0 EF P Is ts ps) := by
  unfold bLP lookupPair
  split <;> rfl

/-- The verifier's lookup phase on a proof with the honest lookup witness, permutation commitment
and terminals replays the prover's. -/
theorem lookupPhase_honest (proof : BatchProof F EF)
    (hw : proof.lookupWitness = (bLP EF P Is ts ps).1.1)
    (hpc : proof.permutationCommit = (bPermCP EF P Is ts ps).2.map Committed.root)
    (htm : proof.lookupTerminals.toList = bTerms EF P Is ts ps)
    (hd : (bTA0 EF P Is ts ps).duplex = Poseidon2.duplex)
    (hg : (bLP EF P Is ts ps).2.grindFailed = false) :
    lookupPhase (H := poseidon2 F) P Is proof (bTA0 EF P Is ts ps) =
      Except.ok (((bLP EF P Is ts ps).1.2.1, (bLP EF P Is ts ps).1.2.2), bTA EF P Is ts ps) := by
  have hroot : ((proof.permutationCommit.map (·.toList)).getD []) =
      (((bPermCP EF P Is ts ps).2.map fun c ↦ c.root.toList).getD []) := by
    rw [hpc, Option.map_map]; rfl
  unfold lookupPhase bTA
  by_cases hl : hasLookups Is = true
  · rw [bLP_eq, ite_eq_left_of_eq_true _ _ (eq_true hl)] at hw hg ⊢
    simp only [hl, ↓reduceIte]
    dsimp only at hw hg ⊢
    rw [flag_sampleExt, flag_sampleExt] at hg
    have hck := (checkWitness_run _ P.lookupPowBits
      (((bTA0 EF P Is ts ps).grind P.lookupPowBits).1) hd).trans
      (congrArg Except.ok (checkWitness_grind _ _ hg))
    rw [hw, Option.getD_some, bind_ok hck]
    simp only [ensure_true, pure_bind, sampleExt_bind, observeList_bind, observeExts_bind, hroot,
      htm]
    rfl
  · rw [bLP_eq, ite_eq_right_of_eq_false _ _ (eq_false hl)]
    simp only [hl, Bool.false_eq_true, ↓reduceIte, pure_bind, observeList_bind,
      observeExts_bind, hroot, htm]
    rfl

end Honest

/-- The honest openings have the instance's shape. -/
theorem openedShapeOk_honest (P : Params) (I : Instance F) (trace : Array F) (pis : List F)
    (chs : List EF) (alpha zeta : EF) :
    openedShapeOk I (honestOpened P.logBlowup I.air I.logN
      (ldeRef I.logN P.logBlowup gen I.air.width trace) (honestChunks P I trace pis chs alpha)
      zeta) = true := by
  have hs (m : Stark.Mat F) (z : EF) : (Fri.openedAt P.logBlowup m z).size = m.width := by
    rw [openedAt_eq, Array.size_ofFn]
  simp only [openedShapeOk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨hs _ zeta, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have hw : (ldeRef I.logN P.logBlowup gen I.air.width trace).width = I.air.width := rfl
    simp only [honestOpened, traceNextOk]
    cases hn : I.air.mainNextRow
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    · simp only [↓reduceIte, hs, hw, beq_self_eq_true, Bool.and_self]
  · simp only [honestOpened, honestChunks, batchQuotientChunks, chunksOf, List.size_toArray,
      List.length_map, List.length_range]
  · rw [Array.all_eq_true]
    intro i hi
    simp only [honestOpened, honestChunks, batchQuotientChunks, chunksOf, List.getElem_toArray,
      List.getElem_map, hs, beq_iff_eq]
    rfl
  · by_cases hpw : I.air.preprocessedWidth = 0
    · have hn : I.air.opensPreprocessedNext = false := by
        simp only [Air.opensPreprocessedNext, hpw, Nat.lt_irrefl, decide_false, Bool.false_and]
      simp only [honestOpened, hpw, hn, ↓reduceIte, beq_self_eq_true, Bool.false_eq_true]
    · have hw : (ldeRef I.logN P.logBlowup gen I.air.preprocessedWidth I.air.preprocessed).width =
          I.air.preprocessedWidth := rfl
      have h0 : 0 < I.air.preprocessedWidth := Nat.pos_of_ne_zero hpw
      simp only [honestOpened, hpw, ↓reduceIte]
      cases hn : I.air.opensPreprocessedNext <;>
        simp only [hs, hw, h0, beq_self_eq_true, Bool.and_true, Bool.not_false,
          decide_true, Bool.false_eq_true, ↓reduceIte]

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

/-- The honest proof passes the lookup checks before the transcript. -/
theorem lookupShapeOk_honest (hts : ts.length = Is.length) (hps : ps.length = Is.length)
    (hwidths : widthsOk (Is.flatMap (·.lookups)) = true)
    (hbound : heightBoundOk (CompPoly.CanonicalNat.bound F)
      (Is.map fun I ↦ (I.lookups, I.logN)) = true) :
    lookupShapeOk P Is (proveBatch EF P Is ts ps) = true := by
  have hp := proveBatch_eq EF P Is ts ps
  have hTl := length_bTerms EF P Is ts ps hts hps
  unfold lookupShapeOk
  simp only [Bool.and_eq_true, hwidths, hbound, true_and]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by
      simp only [List.length_zip, hp, List.toList_toArray, List.length_map, List.length_range,
        hTl, Nat.min_self] at hi
      exact hi
    simp only [List.getElem_zip, hp, List.toList_toArray, List.getElem_map, List.getElem_range]
    unfold permutationShapeOk
    have ht : (bTerms EF P Is ts ps)[i]'(by rw [hTl]; exact hiI) =
        if Is[i].lookups.isEmpty then none else some (permutationTrace Is[i].air Is[i].lookups
          Is[i].logN (ts[i]'(by rw [hts]; exact hiI)) (ps[i]'(by rw [hps]; exact hiI))
          ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hiI))).2 := by
      simp only [bTerms, List.getElem_map]
      rw [getElem_bPerms EF P Is ts ps hts hps i hiI]
      split <;> rfl
    rw [ht]
    by_cases he : Is[i].lookups.isEmpty = true
    · simp only [he, ↓reduceIte, bPermAt_empty EF P Is ts ps i _ hiI he, Array.size_empty,
        beq_self_eq_true, Option.isSome_none, Bool.not_true, Bool.and_self]
    · obtain ⟨m, hm⟩ : ∃ m, permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hiI))
          (ps[i]'(by rw [hps]; exact hiI))
          ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hiI)) = some m := by
        unfold permLde
        simp only [he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, exists_eq']
      obtain ⟨h0, h1⟩ := bPermAt_eq EF P Is ts ps hts hps i hiI m hm
      have hw : m.width = (Is[i].lookups.length + 1) * Challenge.d EF := by
        unfold permLde at hm
        simp only [he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hm
        rw [← hm]; rfl
      simp only [he, Bool.false_eq_true, ↓reduceIte, h0, h1, openedAt_eq, Array.size_ofFn, hw,
        beq_self_eq_true, Option.isSome_some, Bool.not_false, Bool.and_self]
  · rw [hp, Option.isSome_map, bPermCP_snd]
    split <;> rename_i h <;> simp only [h, Option.isSome_some, Option.isSome_none, beq_self_eq_true]
  · rw [hp, bLP_eq]
    by_cases hl : hasLookups Is = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)]
      simp only [hl, Bool.true_and]
      exact grind_canonical _ _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)]
      simp only [Bool.not_eq_true] at hl
      simp only [hl, Bool.not_false]

end Honest

/-! ### Completeness -/

section Honest
variable (EF) (P : Params) (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F))

theorem duplex_bLP : (bLP EF P Is ts ps).2.duplex = (bTA0 EF P Is ts ps).duplex := by
  rw [bLP_eq]
  split
  · rw [duplex_sampleExt, duplex_sampleExt, duplex_grind]
  · rfl

theorem flag_bLP (h : (bLP EF P Is ts ps).2.grindFailed = false) :
    (bTA0 EF P Is ts ps).grindFailed = false := by
  rw [bLP_eq] at h
  split at h
  · rw [flag_sampleExt, flag_sampleExt] at h
    exact flag_grind _ _ h
  · exact h

end Honest

/-- Batch completeness with every assumption spelled out; `batchCompleteness`
(`CompStark/BatchCompleteness.lean`) groups them. -/
theorem verifyBatch_proveBatch_of (EF : Type) [Challenge F EF] (P : Params)
    (Is : List (Instance F)) (ts : List (Array F)) (ps : List (List F)) (hne : Is ≠ [])
    (hts : ts.length = Is.length) (hps : ps.length = Is.length)
    (hfit : ∀ i (hi : i < Is.length), Fits P Is[i].air Is[i].logN (ts[i]'(hts ▸ hi)))
    (hvan : ∀ i (hi : i < Is.length), Is[i].air.ConstraintsVanish Is[i].logN (ts[i]'(hts ▸ hi))
      (ps[i]'(hps ▸ hi)))
    (hpis : ∀ i (hi : i < Is.length), (ps[i]'(hps ▸ hi)).length = Is[i].air.numPublicValues)
    (hlc : ∀ I ∈ Is, I.logQuotientChunks ≤ P.logBlowup)
    (hdeg : ∀ I ∈ Is, I.air.DegreeFitsAt I.logN I.logQuotientChunks)
    (hdegL : ∀ I ∈ Is, ∀ g ∈ I.air.lookupConstraints I.logN,
      g.degBound (2 ^ I.logN) (I.air.periodicDegree (2 ^ I.logN)) <
        2 ^ (I.logN + I.logQuotientChunks) + 2 ^ I.logN)
    (hls : ∀ I ∈ Is, ∀ l ∈ I.lookups,
      l.Fits I.air.width I.air.mainNextWidth I.air.preprocessedWidth I.air.preprocessedNextWidth)
    (hwidths : widthsOk (Is.flatMap (·.lookups)) = true)
    (hbound : heightBoundOk (CompPoly.CanonicalNat.bound F)
      (Is.map fun I ↦ (I.lookups, I.logN)) = true)
    (hbal : Balanced Is ts ps)
    (hpole : ∀ i (hi : i < Is.length), ∀ r < 2 ^ Is[i].logN, NoPoleAt Is[i].air Is[i].lookups
      Is[i].logN (ts[i]'(hts ▸ hi)) (ps[i]'(hps ▸ hi))
      ((batchLookupChallenges EF P Is ts ps).getD i []) r)
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hfin : ∀ I ∈ Is, P.logFinalPolyLen ≤ I.logN)
    (hgrind : (proveBatchTranscript EF P Is ts ps).grindFailed = false)
    (hz : Ext.OutsideBase (batchOutOfDomainPoint EF P Is ts ps)) :
    verifyBatch P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps = .ok () := by
  rw [batchOutOfDomainPoint_eq] at hz
  rw [proveBatchTranscript_eq] at hgrind
  rw [batchLookupChallenges_eq] at hpole
  have hO := length_opened EF P Is ts ps
  have hcommon := setupBatch_eq (EF := EF) P Is
  have hp := proveBatch_eq EF P Is ts ps
  have hTl := length_bTerms EF P Is ts ps hts hps
  -- the grinding flags and the duplexes
  have hgO : (bOod EF P Is ts ps).2.grindFailed = false := by
    have := flag_openPcs P (bRounds EF P Is ts ps) _ hgrind
    rwa [flag_sampleExt] at this
  have hgC : (bTC EF P Is ts ps).grindFailed = false := flag_grind _ _ hgO
  have hgL : (bLP EF P Is ts ps).2.grindFailed = false := by
    rw [bTC, flag_observeList, flag_sampleExt, bTA, flag_observeExts, flag_observeList] at hgC
    exact hgC
  have hd0 : (bTA0 EF P Is ts ps).duplex = Poseidon2.duplex := by
    rw [bTA0, duplex_observeList, duplex_observeList, duplex_observeList, duplex_observeExts,
      duplex_observeList]
    rfl
  have hdC : (bTC EF P Is ts ps).duplex = Poseidon2.duplex := by
    rw [bTC, duplex_observeList, duplex_sampleExt, bTA, duplex_observeExts, duplex_observeList,
      duplex_bLP, hd0]
  have hd2 : (Transcript.sampleExtState EF (bOod EF P Is ts ps).2).duplex = Poseidon2.duplex := by
    rw [duplex_sampleExt, bOod, duplex_grind, hdC]
  -- the verifier's transcript is the prover's
  have hTA0 : bVTA0 P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps =
      bTA0 EF P Is ts ps := by
    rw [bVTA0, bTA0, hcommon, hp, Option.map_map]
    rfl
  have hLP := lookupPhase_honest EF P Is ts ps (proveBatch EF P Is ts ps) (by rw [hp])
    (by rw [hp]) (by rw [hp, List.toList_toArray]) hd0 hgL
  have hcO : checkWitness (poseidon2 F) P.oodPowBits (bOod EF P Is ts ps).1
      (bTC EF P Is ts ps) = .ok (true, (bOod EF P Is ts ps).2) :=
    (checkWitness_run _ _ _ hdC).trans (congrArg Except.ok (checkWitness_grind _ _ hgO))
  have hfitI : ∀ I ∈ Is, I.logN + P.logBlowup ≤ twoAdicity F ∧ I.air.periodicFits I.logN = true :=
    by
    intro I hI
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hI
    exact ⟨(hfit i hi).twoAdic, (hfit i hi).periodic⟩
  have hdom : (Is.all fun I ↦ Ext.powTwo (bZeta EF P Is ts ps) I.logN - 1 != 0) = true := by
    rw [List.all_eq_true]
    intro I hI
    exact powTwo_ne_one hz (by have := (hfitI I hI).1; omega)
  have hpcs : verifyPcs (poseidon2 F) P
      (verifierRounds P.logBlowup (honestRounds P.logBlowup (bRounds EF P Is ts ps)))
      (bPcs EF P Is ts ps).1.2 (Transcript.sampleExtState EF (bOod EF P Is ts ps).2) =
      .ok ((), (bPcs EF P Is ts ps).2) :=
    verifyPcs_openPcs P (bRounds EF P Is ts ps) _ hd2
      (honest_bRounds EF P Is ts ps hne hts hps hfit hlc hfin hz) hP hq hb hgrind
  have hrun : bVerifyRun P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps
      Poseidon2.initTranscript =
      .ok (((bLP EF P Is ts ps).1.2.1, (bLP EF P Is ts ps).1.2.2, bAlpha EF P Is ts ps,
        bZeta EF P Is ts ps), (bPcs EF P Is ts ps).2) := by
    rw [bVerifyRun_run, hTA0, bind_ok hLP]
    dsimp only
    rw [bind_ok (sampleExt_run _)]
    have hqc : (proveBatch EF P Is ts ps).quotientCommit =
        (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root := by rw [hp]
    have how : (proveBatch EF P Is ts ps).oodWitness = (bOod EF P Is ts ps).1 := by rw [hp]
    have hfri : (proveBatch EF P Is ts ps).fri = (bPcs EF P Is ts ps).1.2 := by rw [hp]
    rw [observeList_bind, hqc, how]
    rw [show (Transcript.sampleExtState EF (bTA EF P Is ts ps)).observeList
      (Committed.ofMats hashF compF (bChunks EF P Is ts ps).flatten).root.toList =
        bTC EF P Is ts ps from rfl, bind_ok hcO, ensure_true, pure_bind, bind_ok (sampleExt_run _)]
    have hzeta : ((bOod EF P Is ts ps).2.sampleExtValue : EF) = bZeta EF P Is ts ps := rfl
    rw [hzeta, hdom, ensure_true, pure_bind, batchRounds_eq EF P Is ts ps hts hps, hfri,
      bind_ok hpcs]
    rfl
  -- the checks
  have hshape : ((Is.zip (proveBatch EF P Is ts ps).opened.toList).all fun x ↦
      openedShapeOk x.1 x.2) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by rw [List.length_zip, hO, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip]
    rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hiI),
      getElem_bChunks EF P Is ts ps hts hps i hiI, getElem_bExts P Is ts hts i hiI]
    exact openedShapeOk_honest P _ _ _ _ _ _
  have hcheck : ((Is.zipIdx.zip ((proveBatch EF P Is ts ps).opened.toList.zip ps)).all
      fun x ↦ instanceCheck x.1.1 x.2.1 x.2.2
        ((proveBatch EF P Is ts ps).permutationLocal.getD x.1.2 #[])
        ((proveBatch EF P Is ts ps).permutationNext.getD x.1.2 #[])
        ((bChs EF P Is ts ps).getD x.1.2 [])
        (((proveBatch EF P Is ts ps).lookupTerminals.getD x.1.2 none).getD 0)
        (bZeta EF P Is ts ps) (bAlpha EF P Is ts ps)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by
      rw [List.length_zip, List.length_zip, List.length_zipIdx, hO, hps, Nat.min_self,
        Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip, List.getElem_zipIdx, Nat.zero_add]
    rw [opened_getElem EF P Is ts ps hts hps i (by rw [hO]; exact hiI),
      getElem_bChunks EF P Is ts ps hts hps i hiI, getElem_bExts P Is ts hts i hiI]
    have hchs : (bChs EF P Is ts ps).getD i [] =
        (bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hiI) :=
      getD_of_lt _ _ (by rw [length_bChs]; exact hiI) _
    rw [hchs]
    refine instanceCheck_honest P Is[i] _ _ _ _ _ (hfit i hiI) (hlc _ (List.getElem_mem hiI))
      (hvan i hiI) (hdeg _ (List.getElem_mem hiI)) (hdegL _ (List.getElem_mem hiI))
      (hls _ (List.getElem_mem hiI)) (fun r hr ↦ ?_) hz _ _ _ fun m hm ↦ ?_
    · have := hpole i hiI r hr
      rwa [hchs] at this
    · have hm' : permLde P.logBlowup Is[i] (ts[i]'(by rw [hts]; exact hiI))
          (ps[i]'(by rw [hps]; exact hiI))
          ((bChs EF P Is ts ps)[i]'(by rw [length_bChs]; exact hiI)) = some m := hm
      obtain ⟨h0, h1⟩ := bPermAt_eq EF P Is ts ps hts hps i hiI m hm'
      have he : Is[i].lookups.isEmpty = false := by
        unfold permLde at hm'
        by_contra h
        simp only [Bool.not_eq_false] at h
        simp only [h, ↓reduceIte, reduceCtorEq] at hm'
      refine ⟨?_, ?_, ?_⟩
      · rw [hp, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_range hiI, Option.map_some, Option.getD_some, h0]
      · rw [hp, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_range hiI, Option.map_some, Option.getD_some, h1]
        rfl
      · rw [hp, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem (by rw [hTl]; exact hiI)]
        simp only [bTerms, List.getElem_map, Option.getD_some]
        rw [getElem_bPerms EF P Is ts ps hts hps i hiI]
        simp only [he, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some]
        rfl
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
  have hcount : ((proveBatch EF P Is ts ps).opened.size == Is.length &&
      ps.length == Is.length &&
      (proveBatch EF P Is ts ps).permutationLocal.size == Is.length &&
      (proveBatch EF P Is ts ps).permutationNext.size == Is.length &&
      (proveBatch EF P Is ts ps).lookupTerminals.size == Is.length) = true := by
    rw [← Array.length_toList, hO, hps]
    rw [hp]
    simp only [List.size_toArray, List.length_map, List.length_range, hTl, beq_self_eq_true,
      Bool.and_self]
  have hdb : ((proveBatch EF P Is ts ps).degreeBits.toList == Is.map (·.logN)) = true := by
    rw [hp]; exact beq_self_eq_true _
  have hqd : (Is.all fun I ↦ I.logN + I.logQuotientChunks ≤ twoAdicity F) = true := by
    rw [List.all_eq_true]
    intro I hI
    have := (hfitI I hI).1
    have := hlc I hI
    exact decide_eq_true (by omega)
  have hper : (Is.all fun I ↦ I.air.periodicFits I.logN) = true := by
    rw [List.all_eq_true]
    exact fun I hI ↦ (hfitI I hI).2
  have hpv : ((Is.zip ps).all fun x ↦ x.2.length == x.1.air.numPublicValues) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiI : i < Is.length := by rw [List.length_zip, hps, Nat.min_self] at hi; exact hi
    simp only [List.getElem_zip]
    rw [hpis i hiI, beq_self_eq_true]
  have hood : (P.oodPowBits != 0 || (proveBatch EF P Is ts ps).oodWitness == 0) = true := by
    rw [hp]; exact grind_canonical _ _
  have hlk := lookupShapeOk_honest EF P Is ts ps hts hps hwidths hbound
  have hterm : (((proveBatch EF P Is ts ps).lookupTerminals.toList.filterMap id).foldl (· + ·) 0
      == 0) = true := by
    rw [hp, List.toList_toArray, bTerms, bPerms, bChs, terminals_permutationsWith]
    exact beq_iff_eq.mpr (terminals_sum_eq_zero Is ts ps hts hps hbal _ _)
  rw [verifyBatch_eq]
  simp only [hcount, hdb, hqd, hper, hpv, hshape, hprepOk, hlk, hood, ↓reduceIte]
  have hrun' : StateT.run (bVerifyRun P Is (setupBatch P Is) (proveBatch EF P Is ts ps) ps)
      Poseidon2.initTranscript = pure (((bLP EF P Is ts ps).1.2.1, (bLP EF P Is ts ps).1.2.2,
        bAlpha EF P Is ts ps, bZeta EF P Is ts ps), (bPcs EF P Is ts ps).2) := hrun
  rw [hrun', pure_bind]
  unfold bVerifyCheck
  simp only [show challengeLayout (Is.map (·.lookups)) (bLP EF P Is ts ps).1.2.1
    (bLP EF P Is ts ps).1.2.2 = bChs EF P Is ts ps from rfl, hcheck, hterm, ↓reduceIte]
  rfl

end CompStark.Batch
