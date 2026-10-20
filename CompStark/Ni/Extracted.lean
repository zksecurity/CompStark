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
open Polynomial Montgomery.Native32 Fri.Spec OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field
local notation "𝔽" => KoalaBear.Field

variable {EF : Type} [Challenge EF]

local notation "𝕂" => Challenge.Spec EF

/-- Two caches extract the same rows under `root`. -/
def SameUnder (cache cache' : Merkle.Cache F Digest) (root : Digest) : Prop :=
  ∀ k i, Merkle.extractRow cache k i root = Merkle.extractRow cache' k i root

variable (S : Iop.Setup EF)

/-! ### Congruences -/

section Congr
variable {cache cache' : Merkle.Cache F Digest} {root : Digest}

theorem committedColumn_congr (h : SameUnder cache cache' root) :
    committedColumn S cache root = committedColumn S cache' root := by
  funext j z
  unfold SameUnder at h
  simp only [committedColumn, leafRow, h]

theorem friWordAt_congr (h : SameUnder cache cache' root) :
    friWordAt (EF := EF) cache root = friWordAt cache' root := by
  funext m a z
  unfold SameUnder at h
  simp only [friWordAt, leafRow, h]

theorem friOracles_congr (commits : List Digest) (coeffs : Array EF)
    (h : ∀ i < S.lastFold + 1, SameUnder cache cache' (commits.getD i 0)) :
    friOracles S cache commits coeffs = friOracles S cache' commits coeffs := by
  funext j
  unfold friOracles
  split
  · rfl
  · rename_i hj
    rw [friWordAt_congr (h j (by omega))]

theorem getD_commits (block : Nat → List F) (i : Nat) (hi : i < S.lastFold + 1) :
    ((List.range (S.lastFold + 1)).map fun i ↦ digestAt (block (3 + i)) 0).getD i 0 =
      digestAt (block (3 + i)) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hi),
    List.getElem_map, List.getElem_range]

variable {block block' : Nat → List F} {sample sample' : Nat → Vector F S.streamLen}

theorem prefixTranscript_trace (hb : block 0 = block' 0)
    (h : SameUnder cache cache' (digestAt (block' 0) 3)) :
    (prefixTranscript S cache block sample).trace =
      (prefixTranscript S cache' block' sample').trace := by
  simp only [prefixTranscript, hb, committedColumn_congr S h]

theorem prefixTranscript_quotient (hb : block 1 = block' 1)
    (h : SameUnder cache cache' (digestAt (block' 1) 0)) :
    (prefixTranscript S cache block sample).quotient =
      (prefixTranscript S cache' block' sample').quotient := by
  simp only [prefixTranscript, hb, committedColumn_congr S h]

theorem prefixTranscript_committedWord (f : Fin (S.lastFold + 1))
    (hb : block (3 + f.val) = block' (3 + f.val))
    (h : SameUnder cache cache' (digestAt (block' (3 + f.val)) 0)) :
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
    (htrace : SameUnder cache cache' (digestAt (block' 0) 3))
    (hquot : SameUnder cache cache' (digestAt (block' 1) 0))
    (hfri : ∀ i < S.lastFold + 1, SameUnder cache cache' (digestAt (block' (3 + i)) 0)) :
    prefixTranscript S cache block sample = prefixTranscript S cache' block' sample' := by
  rw [prefixTranscript_sample_congr S cache block hs]
  have hcommits : ((List.range (S.lastFold + 1)).map fun i ↦ digestAt (block (3 + i)) 0) =
      (List.range (S.lastFold + 1)).map fun i ↦ digestAt (block' (3 + i)) 0 :=
    List.map_congr_left fun i hi ↦ by
      rw [hb (3 + i) (by rw [List.mem_range] at hi; omega)]
  simp only [prefixTranscript, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
    hb (4 + S.lastFold) (le_refl _), hcommits, committedColumn_congr S htrace,
    committedColumn_congr S hquot]
  rw [friOracles_congr S _ _ fun i hi ↦ by rw [getD_commits S _ i hi]; exact hfri i hi]

end Congr

/-! ### The schedule of an accepted proof -/

section Schedule
variable (proof : Proof EF) (pis : List F)

theorem digestAt_toList (d : Digest) : digestAt d.toList 0 = d := by
  simpa only [List.append_nil] using digestAt_append_zero d []

theorem inputs_getD_zero :
    (inputs S.params pis proof).getD 0 [] =
      [(proof.degreeBits : F), (proof.degreeBits : F), 0] ++ proof.traceCommit.toList ++ pis := by
  simp only [inputs, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    Option.getD_some]

theorem inputs_getD_one : (inputs S.params pis proof).getD 1 [] = proof.quotientCommit.toList := by
  simp only [inputs, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

theorem inputs_getD_two :
    (inputs S.params pis proof).getD 2 [] = coeffs (openedValues proof.opened) := by
  simp only [inputs, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

theorem traceRoot_eq : digestAt ((inputs S.params pis proof).getD 0 []) 3 = proof.traceCommit := by
  rw [inputs_getD_zero]
  exact digestAt_append _ [_, _, _] _

theorem quotientRoot_eq : digestAt ((inputs S.params pis proof).getD 1 []) 0 =
    proof.quotientCommit := by
  rw [inputs_getD_one, digestAt_toList]

variable (answer : (q : Query) → Answer S.streamLen q)
variable {proof pis}

/-- An accepted proof for `2 ^ logN` rows commits once per fold of `S`'s schedule. -/
theorem length_commits (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    proof.fri.commitWitnesses.size = proof.fri.commits.size ∧
      proof.fri.commits.size = S.lastFold + 1 := by
  obtain ⟨-, -, -, -, harity, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok (idealOf answer) S.params S.air
    proof pis hok
  rw [hdb] at harity
  obtain ⟨-, hb, hne, hh⟩ := friHyps S (idealOf answer) proof pis hdb harity
  obtain ⟨hqa, hwit, -, -, -, -⟩ := verifyFri_ok (idealOf answer) S.params proof.fri _ hb hne hh _ _
    hfriOk
  have harr : arities proof.fri = S.foldArities.map PNat.val := by
    rw [harity, foldArities_eq]; rfl
  have hq0 : 0 < proof.fri.queries.size := by
    by_contra h0
    have hnil : arities proof.fri = [] := by
      simp only [arities, Array.getElem?_eq_none (by omega : proof.fri.queries.size ≤ 0),
        Option.map_none, Option.getD_none]
    rw [harr, List.map_eq_nil_iff] at hnil
    exact Sound.Setup.foldArities_ne_nil S hnil
  obtain ⟨hsize, hmap⟩ := hqa _ (Array.getElem_mem_toList hq0)
  refine ⟨hwit, ?_⟩
  rw [← hsize, ← Array.length_toList, ← List.length_map (f := (·.logArity)), hmap, harr,
    List.length_map, length_foldArities]

theorem length_zip_commits (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length = S.lastFold + 1 := by
  obtain ⟨hwit, hsize⟩ := length_commits S answer hdb hok
  rw [List.length_zip, Array.length_toList, Array.length_toList, hwit, Nat.min_self, hsize]

theorem foldRoot_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) (i : Nat)
    (hi : i < S.lastFold + 1) :
    digestAt ((inputs S.params pis proof).getD (3 + i) []) 0 =
      proof.fri.commits[i]'(by rw [(length_commits S answer hdb hok).2]; exact hi) := by
  have hz := length_zip_commits S answer hdb hok
  rw [show 3 + i = 2 + 1 + i by omega, inputs_getD_fold _ _ _ i (by omega),
    digestAt_append_zero, List.getElem_zip, Array.getElem_toList]

theorem commits_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    ((List.range (S.lastFold + 1)).map fun i ↦
      digestAt ((inputs S.params pis proof).getD (3 + i) []) 0) = proof.fri.commits.toList := by
  have hsize := (length_commits S answer hdb hok).2
  refine List.ext_getElem (by rw [List.length_map, List.length_range, Array.length_toList,
    hsize]) fun i h₁ h₂ ↦ ?_
  rw [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range, foldRoot_eq S answer hdb hok i h₁,
    Array.getElem_toList]

theorem finalPoly_eq (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    finalPolyAt S ((inputs S.params pis proof).getD (4 + S.lastFold) []) = proof.fri.finalPoly := by
  have hz := length_zip_commits S answer hdb hok
  obtain ⟨-, -, -, -, harity, ⟨st, hfriOk⟩, -⟩ := verifyWith_ok (idealOf answer) S.params S.air
    proof pis hok
  rw [hdb] at harity
  obtain ⟨-, hb, hne, hh⟩ := friHyps S (idealOf answer) proof pis hdb harity
  obtain ⟨-, -, hfp, -⟩ := verifyFri_ok (idealOf answer) S.params proof.fri _ hb hne hh _ _
    hfriOk
  have hlast := inputs_getD_last S.params pis proof
  rw [hz, show 2 + 1 + (S.lastFold + 1) = 4 + S.lastFold by omega] at hlast
  rw [hlast, List.append_assoc]
  exact finalPolyAt_coeffs S _ _ hfp

/-- **The extracted transcript.** On an accepted proof for `2 ^ logN` rows, the transcript
extracted from a run on the answers `answer` is the prefix transcript of the proof's schedule
with the answers to its duplex calls. -/
theorem extract_eq_prefixTranscript (cache : Merkle.Cache F Digest)
    (hdb : proof.degreeBits = S.logN)
    (hok : verifyWith (idealOf answer) S.params S.air proof pis = .ok ()) :
    extract S cache (idealOf answer) proof pis =
      prefixTranscript S cache (fun k ↦ (inputs S.params pis proof).getD k [])
        (fun k ↦ (answer (keyAt answer (inputs S.params pis proof) k)).2) := by
  obtain ⟨htl, htn, hqc, hq4, -, -, -⟩ := verifyWith_ok (idealOf answer) S.params S.air proof pis
    hok
  obtain ⟨hopen, hfp⟩ := nonempty_of_verify S (idealOf answer) proof pis hdb hok
  have hz := length_zip_commits S answer hdb hok
  obtain ⟨hα, hζ, hbatch, -, hβ, -, -⟩ := challenges_idealOf answer S.params proof pis
    (le_refl _) hopen hfp
  have hbetas : foldChallenges S (betasOf (idealOf answer) S.params proof pis) =
      betasAt S (fun k ↦ (answer (keyAt answer (inputs S.params pis proof) k)).2) := by
    funext j
    simp only [foldChallenges, betasAt]
    rw [hβ j.val (by rw [hz]; exact j.isLt)]
  simp only [extract, prefixTranscript, traceRoot_eq, quotientRoot_eq, inputs_getD_two,
    openingsAt_coeffs S _ htl htn hqc hq4, hα, hζ, hbatch, commits_eq S answer hdb hok,
    finalPoly_eq S answer hdb hok, hbetas]
  rfl

end Schedule

end CompStark.Ni
