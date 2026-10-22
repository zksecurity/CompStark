/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Rounds

/-! # The extracted transcript is the prefix transcript of the schedule

* Congruences: the prefix transcript's fields depend only on the inputs and answers of their
  rounds and on what the cache extracts under the observed digests (`SameUnder`).
* `extract_eq_prefixTranscript`: on an accepted proof for `2 ^ logN` rows, the transcript F's
  `bcs` extracts from a run on an answer table is the prefix transcript of the proof's schedule
  (`inputs`) with the answers to its duplex calls. The decoders invert the observations, and the
  challenges are those of `challenges_idealOf`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- Two caches extract the same rows under `root`. -/
def SameUnder (cache cache' : Merkle.Cache F (Digest F)) (root : Digest F) : Prop :=
  ∀ k i, Merkle.extractRow cache k i root = Merkle.extractRow cache' k i root

/-- Two caches extract the same rows under every entry of the cap `cap`, and under the zero
digest an index past it reads. -/
def CapSameUnder (cache cache' : Merkle.Cache F (Digest F)) (cap : Cap F) : Prop :=
  ∀ j, SameUnder cache cache' (cap.toList.getD j 0)

variable (S : Iop.Setup EF)

/-! ### Congruences -/

section Congr
variable {cache cache' : Merkle.Cache F (Digest F)} {root : Cap F}

theorem committedColumn_congr (h : CapSameUnder cache cache' root) :
    committedColumn S cache root = committedColumn S cache' root := by
  funext j z
  unfold CapSameUnder SameUnder at h
  simp only [committedColumn, leafRow, Merkle.extractCapRow, h]

theorem friWordAt_congr (h : CapSameUnder cache cache' root) :
    friWordAt (EF := EF) cache root = friWordAt cache' root := by
  funext c m a z
  unfold CapSameUnder SameUnder at h
  simp only [friWordAt, leafRow, Merkle.extractCapRow, h]

theorem friOracles_congr (commits : List (Cap F)) (coeffs : Array EF)
    (h : ∀ i < S.lastFold + 1, CapSameUnder cache cache' (commits.getD i #[])) :
    friOracles S cache commits coeffs = friOracles S cache' commits coeffs := by
  funext j
  unfold friOracles
  split
  · rfl
  · rename_i hj
    rw [friWordAt_congr (h j (by omega))]

/-- Where fold round `i`'s commitment sits in its input: after FRI's domain separator in the
first fold round. -/
def friOffset (i : Nat) : Nat := if i = 0 then (friSeedS S).length else 0

theorem getD_commits (block : Nat → List F) (i : Nat) (hi : i < S.lastFold + 1) :
    ((List.range (S.lastFold + 1)).map fun i ↦
      capFrom (block (3 + i)) (if i = 0 then (friSeedS S).length else 0)
        (capSize S (friDepth S i))).getD i #[] =
      capFrom (block (3 + i)) (friOffset S i) (capSize S (friDepth S i)) := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hi),
    List.getElem_map, List.getElem_range]
  rfl

variable {block block' : Nat → List F} {sample sample' : Nat → Vector F S.streamLen}

theorem prefixTranscript_trace (hb : block 0 = block' 0)
    (h : CapSameUnder cache cache'
      (capFrom (block' 0) (starkSeedS S).length (capSize S S.logSize))) :
    (prefixTranscript S cache block sample).trace =
      (prefixTranscript S cache' block' sample').trace := by
  simp only [prefixTranscript, hb, committedColumn_congr S h]

theorem prefixTranscript_quotient (hb : block 1 = block' 1)
    (h : CapSameUnder cache cache' (capFrom (block' 1) 0 (capSize S S.logSize))) :
    (prefixTranscript S cache block sample).quotient =
      (prefixTranscript S cache' block' sample').quotient := by
  simp only [prefixTranscript, hb, committedColumn_congr S h]

theorem prefixTranscript_committedWord (f : Fin (S.lastFold + 1))
    (hb : block (3 + f.val) = block' (3 + f.val))
    (h : CapSameUnder cache cache'
      (capFrom (block' (3 + f.val)) (friOffset S f.val) (capSize S (friDepth S f.val)))) :
    committedWord S.schedule (prefixTranscript S cache block sample).fri f =
      committedWord S.schedule (prefixTranscript S cache' block' sample').fri f := by
  funext x
  refine (committedWord_friOracles S cache _ _ f x).trans ((congrFun ?_ _).trans
    (committedWord_friOracles S cache' _ _ f x).symm)
  rw [getD_commits S _ _ f.isLt, getD_commits S _ _ f.isLt, hb, friWordAt_congr h]

theorem prefixTranscript_betas (f : Fin (S.lastFold + 1))
    (hs : sample (3 + f.val) = sample' (3 + f.val)) :
    (prefixTranscript S cache block sample).betas f =
      (prefixTranscript S cache' block' sample').betas f := by
  simp only [prefixTranscript, betasAt, hs]

/-- The prefix transcript of all rounds depends on their inputs and answers, and on the rows
extracted under the observed digests. -/
theorem prefixTranscript_congr (hb : ∀ k ≤ 4 + S.lastFold, block k = block' k)
    (hs : ∀ k ≤ 3 + S.lastFold, sample k = sample' k)
    (htrace : CapSameUnder cache cache'
      (capFrom (block' 0) (starkSeedS S).length (capSize S S.logSize)))
    (hquot : CapSameUnder cache cache' (capFrom (block' 1) 0 (capSize S S.logSize)))
    (hfri : ∀ i < S.lastFold + 1, CapSameUnder cache cache'
      (capFrom (block' (3 + i)) (friOffset S i) (capSize S (friDepth S i)))) :
    prefixTranscript S cache block sample = prefixTranscript S cache' block' sample' := by
  rw [prefixTranscript_sample_congr S cache block hs]
  have hcommits : ((List.range (S.lastFold + 1)).map fun i ↦
      capFrom (block (3 + i)) (if i = 0 then (friSeedS S).length else 0)
        (capSize S (friDepth S i))) =
      (List.range (S.lastFold + 1)).map fun i ↦
        capFrom (block' (3 + i)) (if i = 0 then (friSeedS S).length else 0)
          (capSize S (friDepth S i)) :=
    List.map_congr_left fun i hi ↦ by
      rw [hb (3 + i) (by rw [List.mem_range] at hi; omega)]
  simp only [prefixTranscript, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
    hb (4 + S.lastFold) (le_refl _), hcommits, committedColumn_congr S htrace,
    committedColumn_congr S hquot]
  rw [friOracles_congr S _ _ fun i hi ↦ by rw [getD_commits S _ i hi]; exact hfri i hi]

end Congr

/-! ### The schedule of an accepted proof -/

section Schedule
variable (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)

theorem digestAt_toList (d : Digest F) : digestAt d.toList 0 = d := by
  simpa only [List.append_nil] using digestAt_append_zero d []

theorem inputs_getD_zero :
    (inputs S.params S.air vk pis proof).getD 0 [] =
      starkSeedOf EF S.params S.air proof.degreeBits ++ capElems proof.traceCommit ++
        preprocessedDigest vk ++ pis := by
  simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]

theorem inputs_getD_one : (inputs S.params S.air vk pis proof).getD 1 [] =
    capElems proof.quotientCommit ++ witnessInput S.params.oodPowBits proof.oodWitness := by
  simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

theorem inputs_getD_two : (inputs S.params S.air vk pis proof).getD 2 [] =
    DomainSeparator.pcsSeed F EF (pcsCounts proof.opened) S.params.batchPowBits ++
      coeffs (openedValues proof.opened) ++
      witnessInput S.params.batchPowBits proof.fri.batchWitness := by
  simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

/-- On a proof of `S`'s shape, the PCS's domain separator is `S`'s. -/
theorem pcsCounts_eq (htl : proof.opened.traceLocal.size = S.air.width)
    (htn : traceNextOk S.air proof.opened = true)
    (hqc : proof.opened.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ proof.opened.quotientChunks, ch.size = Challenge.d EF)
    (hshape : preprocessedShapeOk S.air vk proof.opened S.logN = true) :
    pcsCounts proof.opened = pcsCountsS S := by
  rw [pcsCounts, pcsCountsS, (prep_of_shapeOk hshape).2.2]
  simp only [htl, (traceNext_of_ok htn).2, List.cons_append, List.cons.injEq, List.nil_append,
    and_true, true_and]
  rw [List.eq_replicate_iff, List.length_map, Array.length_toList, hqc]
  refine ⟨rfl, fun b hb ↦ ?_⟩
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hb
  rw [hq4 ch (Array.mem_toList_iff.mp hch)]

theorem openings_eq (htl : proof.opened.traceLocal.size = S.air.width)
    (htn : traceNextOk S.air proof.opened = true)
    (hqc : proof.opened.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ proof.opened.quotientChunks, ch.size = Challenge.d EF)
    (hshape : preprocessedShapeOk S.air vk proof.opened S.logN = true) :
    openingsAt S (((inputs S.params S.air vk pis proof).getD 2 []).drop (pcsSeedS S).length) =
      openingsOf S proof.opened := by
  rw [inputs_getD_two, pcsCounts_eq S vk proof htl htn hqc hq4 hshape, ← pcsSeedS,
    List.append_assoc, List.drop_left]
  exact openingsAt_coeffs S _ _ htl (traceNext_of_ok htn).1 hqc hq4 (prep_of_shapeOk hshape).1
    (prep_of_shapeOk hshape).2.1

/-- On a proof for `2 ^ logN` rows, FRI's domain separator is `S`'s. -/
theorem friSeedOf_eq (hdb : proof.degreeBits = S.logN) :
    friSeedOf S.params proof = friSeedS S := by
  obtain ⟨hL, -, -, hsched⟩ := friHyps S none proof 0 hdb
  rw [friSeedOf, hsched, hL, friSeedS]

variable (answer : (q : Query F) → Answer S.streamLen q)
variable {vk proof pis}

/-- An accepted proof for `2 ^ logN` rows commits once per fold of `S`'s schedule. -/
theorem length_commits (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    proof.fri.commitWitnesses.size = proof.fri.commits.size ∧
      proof.fri.commits.size = S.lastFold + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok (idealOf answer)
    S.params S.air vk proof pis hok
  obtain ⟨-, hb, hh, hsched⟩ := friHyps S vk proof
    (zetaOf (idealOf answer) S.params S.air vk proof pis) hdb
  obtain ⟨-, -, hcs, hcw, -⟩ := verifyFri_ok (idealOf answer) S.params proof.fri _ _ _ hb hh _ _
    hfriOk
  have hsched' : foldSchedule S.params.maxLogArity
      (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize] =
      S.foldArities.map PNat.val := by
    obtain ⟨hL, -⟩ := friHyps S vk proof 0 hdb
    rw [← hsched, friSchedule, hL]
  rw [hsched', List.length_map, length_foldArities] at hcs hcw
  exact ⟨hcw.trans hcs.symm, hcs⟩

theorem length_zip_commits (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length = S.lastFold + 1 := by
  obtain ⟨hwit, hsize⟩ := length_commits S answer hdb hok
  rw [List.length_zip, Array.length_toList, Array.length_toList, hwit, Nat.min_self, hsize]

/-- An accepted proof for `2 ^ logN` rows has caps of the sizes of `S`'s trees. -/
theorem size_caps (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    proof.traceCommit.size = capSize S S.logSize ∧
      proof.quotientCommit.size = capSize S S.logSize ∧
      ∀ i (hi : i < proof.fri.commits.size), proof.fri.commits[i].size =
        capSize S (friDepth S i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok (idealOf answer)
    S.params S.air vk proof pis hok
  obtain ⟨hL, hb, hh, hsched⟩ := friHyps S vk proof
    (zetaOf (idealOf answer) S.params S.air vk proof pis) hdb
  obtain ⟨-, hfolds, hcs, -, -, -, hcrlen, hq⟩ := verifyFri_ok (idealOf answer) S.params
    proof.fri _ _ _ hb hh _ _ hfriOk
  have hsched' : foldSchedule S.params.maxLogArity
      (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize] =
      S.foldArities.map PNat.val := by
    rw [← hsched, friSchedule, hL]
  obtain ⟨hround, hfold⟩ := size_caps_of_queryOk _ _ _ _ _ _ _ _ _ _ _ _ _
    hcrlen (by rw [Array.length_toList]; exact hfolds) (hq 0 S.valid.queries)
  have hc : capSize S S.logSize = 2 ^ min S.params.capHeight S.logSize := rfl
  refine ⟨hround 0 (by simp only [openingRounds, List.cons_append, List.length_cons]; omega),
    hround 1 (by simp only [openingRounds, List.cons_append, List.length_cons]; omega),
    fun i hi ↦ ?_⟩
  have := hfold i (by rw [← hcs]; exact hi)
  rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact hi), Array.getElem_toList,
    hsched'] at this
  rw [this, friDepth]

theorem traceRoot_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    capFrom ((inputs S.params S.air vk pis proof).getD 0 []) (starkSeedS S).length
      (capSize S S.logSize) = proof.traceCommit := by
  rw [inputs_getD_zero, starkSeedS, hdb, List.append_assoc, ← (size_caps S answer hdb hok).1]
  exact capFrom_append _ _ _

theorem quotientRoot_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    capFrom ((inputs S.params S.air vk pis proof).getD 1 []) 0 (capSize S S.logSize) =
      proof.quotientCommit := by
  rw [inputs_getD_one, ← (size_caps S answer hdb hok).2.1]
  exact capFrom_append _ [] _

theorem foldRoot_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) (i : Nat)
    (hi : i < S.lastFold + 1) :
    capFrom ((inputs S.params S.air vk pis proof).getD (3 + i) []) (friOffset S i)
      (capSize S (friDepth S i)) =
      proof.fri.commits[i]'(by rw [(length_commits S answer hdb hok).2]; exact hi) := by
  have hz := length_zip_commits S answer hdb hok
  have hsz := (size_caps S answer hdb hok).2.2 i
    (by rw [(length_commits S answer hdb hok).2]; exact hi)
  rw [inputs_getD_fold _ _ _ _ _ i (by omega), friSeedOf_eq S proof hdb]
  have hpre : (friOffset S i) = (seedAt (friSeedS S) i).length := by
    simp only [friOffset, seedAt]
    split <;> rfl
  rw [hpre, List.getElem_zip, Array.getElem_toList, ← hsz]
  exact capFrom_append _ _ _

theorem commits_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    ((List.range (S.lastFold + 1)).map fun i ↦
      capFrom ((inputs S.params S.air vk pis proof).getD (3 + i) [])
        (if i = 0 then (friSeedS S).length else 0) (capSize S (friDepth S i))) =
      proof.fri.commits.toList := by
  have hsize := (length_commits S answer hdb hok).2
  refine List.ext_getElem (by rw [List.length_map, List.length_range, Array.length_toList,
    hsize]) fun i h₁ h₂ ↦ ?_
  rw [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range]
  exact (foldRoot_eq S answer hdb hok i h₁).trans (Array.getElem_toList _).symm

theorem finalPoly_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    finalPolyAt S ((inputs S.params S.air vk pis proof).getD (4 + S.lastFold) []) =
      proof.fri.finalPoly := by
  have hz := length_zip_commits S answer hdb hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok (idealOf answer)
    S.params S.air vk proof pis hok
  obtain ⟨-, hb, hh, -⟩ := friHyps S vk proof
    (zetaOf (idealOf answer) S.params S.air vk proof pis) hdb
  obtain ⟨-, -, -, -, hfp, -⟩ := verifyFri_ok (idealOf answer) S.params proof.fri _ _ _ hb hh _ _
    hfriOk
  have hlast := inputs_getD_last S.params S.air vk pis proof
  rw [hz, show 3 + (S.lastFold + 1) = 4 + S.lastFold by omega] at hlast
  rw [hlast, show seedAt (friSeedOf S.params proof) (S.lastFold + 1) = [] from rfl,
    List.nil_append]
  exact finalPolyAt_coeffs S _ _ hfp

/-- **The extracted transcript.** On an accepted proof for `2 ^ logN` rows, the transcript
extracted from a run on the answers `answer` is the prefix transcript of the proof's schedule
with the answers to its duplex calls. -/
theorem extract_eq_prefixTranscript (cache : Merkle.Cache F (Digest F))
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ()) :
    extract S cache (idealOf answer) vk proof pis =
      prefixTranscript S cache (fun k ↦ (inputs S.params S.air vk pis proof).getD k [])
        (fun k ↦ (answer (keyAt answer (inputs S.params S.air vk pis proof) k)).2) := by
  obtain ⟨htl, htn, hqc, hq4, hshape, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    verifyWith_ok (idealOf answer) S.params S.air vk proof pis hok
  obtain ⟨-, hfp⟩ := nonempty_of_verify S (idealOf answer) vk proof pis hdb hok
  have hz := length_zip_commits S answer hdb hok
  obtain ⟨hα, hζ, hbatch, -, hβ, -, -⟩ := challenges_idealOf answer S.params S.air vk proof pis
    (le_refl _) htn hshape hfp (size_quotientCommit_ne _ _ _ _ _ _ hok)
    (size_commits_ne _ _ _ _ _ _ _ hfriOk)
  have hbetas : foldChallenges S (betasOf (idealOf answer) S.params S.air vk proof pis) =
      betasAt S (fun k ↦ (answer (keyAt answer (inputs S.params S.air vk pis proof) k)).2) := by
    funext j
    simp only [foldChallenges, betasAt]
    rw [hβ j.val (by rw [hz]; exact j.isLt)]
  simp only [extract, prefixTranscript, traceRoot_eq S answer hdb hok,
    quotientRoot_eq S answer hdb hok,
    openings_eq S vk proof pis htl htn (by rw [hqc, hdb]) hq4 (hdb ▸ hshape), hα, hζ, hbatch,
    commits_eq S answer hdb hok, finalPoly_eq S answer hdb hok, hbetas]
  rfl

end Schedule

end CompStark.Ni
