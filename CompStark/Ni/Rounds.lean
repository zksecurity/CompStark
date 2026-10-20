/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsChallenges

/-! # The rounds' bad events on duplex calls

In the random-oracle model a round of the interactive oracle proof is one duplex call. A fresh
call is bad (`RoundBad`) when the queries before it parse it (`parse`) as round `i` of a
transcript and its answer makes round `i` bad (`roundBadAt`, the events of `Sound/Rbr.lean`) for
the transcript read off the parsed prefix and the cache of the earlier hash queries
(`prefixTranscript`):

* the trace and quotient words are extracted under the digests the rounds `0` and `1` observe,
  the FRI oracles under those of the fold rounds, and the final polynomial is the one the query
  round observes;
* the openings are the extension elements the batching round observes;
* the challenges are read off the answers as the verifier reads them (`extAt`,
  `challengeOffset`), the folding challenges substituted to ArkLib's coset coordinate.

The decoders invert the verifier's observations (`digestAt_append`, `openingsAt_coeffs`,
`finalPolyAt_coeffs`), so on a proof's schedule the prefix transcript is the extracted one.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Montgomery.Native32 Fri.Spec OracleSpec OracleComp
open KoalaBear.Fast (Ext4)

local notation "F" => KoalaBear.Fast.Field
local notation "EF" => KoalaBear.Fast.Ext4
local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => Challenge.Spec KoalaBear.Fast.Ext4

/-! ### Decoding observations -/

/-- The digest of the eight elements of `xs` from `offset` on. -/
def digestAt (xs : List F) (offset : Nat) : Digest := Vector.ofFn fun k ↦ xs.getD (offset + k) 0

theorem digestAt_append (d : Digest) (pre rest : List F) :
    digestAt (pre ++ d.toList ++ rest) pre.length = d := by
  ext k hk
  rw [digestAt, Vector.getElem_ofFn, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (l₁ := d.toList) (by rw [Vector.length_toList]; exact hk),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]

theorem digestAt_append_zero (d : Digest) (rest : List F) : digestAt (d.toList ++ rest) 0 = d :=
  digestAt_append d [] rest

/-- The extension element of the four elements of `xs` from `4 k` on. -/
def extFrom (xs : List F) (k : Nat) : EF :=
  ⟨xs.getD (4 * k) 0, xs.getD (4 * k + 1) 0, xs.getD (4 * k + 2) 0, xs.getD (4 * k + 3) 0⟩

theorem extFrom_coeffs (rest : List F) :
    ∀ (l : List EF) (k : Nat) (hk : k < l.length), extFrom (coeffs l ++ rest) k = l[k]
  | x :: l, 0, _ => rfl
  | x :: l, k + 1, hk => by
    have ih := extFrom_coeffs rest l k (by simp only [List.length_cons] at hk; omega)
    simp only [extFrom, coeffs, List.flatMap_cons, List.append_assoc] at ih ⊢
    simp only [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega, List.cons_append,
      List.nil_append, List.getD_cons_succ, List.getElem_cons_succ]
    exact ih

/-- The openings of the extension elements in `xs`: the trace at `ζ`, at `ζ ω`, and the quotient
chunks' coordinates, in the order the verifier observes them. -/
noncomputable def openingsAt (S : Iop.Setup KoalaBear.Fast.Ext4) (xs : List F) : Openings S where
  traceAt j := Ext4.toSpec (extFrom xs j)
  traceNext j := Ext4.toSpec (extFrom xs (S.air.width + j))
  quotientAt c e := Ext4.toSpec (extFrom xs (2 * S.air.width + (4 * c.val + e.val)))

theorem getElem_flatMap_four {α : Type} (L : List (List α)) (hL : ∀ l ∈ L, l.length = 4)
    (c e : Nat) (hc : c < L.length) (he : e < 4) (h : 4 * c + e < (L.flatMap id).length) :
    (L.flatMap id)[4 * c + e] = L[c][e]'(by rw [hL _ (List.getElem_mem hc)]; exact he) := by
  induction L generalizing c with
  | nil => exact absurd hc (Nat.not_lt_zero _)
  | cons l L ih =>
    have hl : l.length = 4 := hL l List.mem_cons_self
    simp only [List.flatMap_cons, id] at h ⊢
    cases c with
    | zero =>
      rw [List.getElem_append_left (by rw [hl]; omega)]
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    | succ c =>
      rw [List.getElem_append_right (by rw [hl]; omega)]
      have := ih (fun l' hl' ↦ hL l' (List.mem_cons_of_mem _ hl')) c
        (by simp only [List.length_cons] at hc; omega)
        (by simp only [List.length_append, hl] at h; omega)
      simp only [hl, show 4 * (c + 1) + e - 4 = 4 * c + e by omega, this,
        List.getElem_cons_succ]

theorem openingsAt_coeffs (S : Iop.Setup KoalaBear.Fast.Ext4) (o : OpenedValues)
    (htl : o.traceLocal.size = S.air.width) (htn : o.traceNext.size = S.air.width)
    (hqc : o.quotientChunks.size = S.chunks) (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = 4) :
    openingsAt S (coeffs (openedValues o)) = openingsOf S o := by
  have hlen : (openedValues o).length = 2 * S.air.width + 4 * S.chunks := by
    simp only [openedValues, List.length_append, Array.length_toList, htl, htn,
      List.length_flatMap]
    rw [List.sum_eq_length_nsmul _ 4 (by
      intro n hn
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hn
      exact hq4 ch (Array.mem_toList_iff.mp hch)), List.length_map, Array.length_toList, hqc,
      smul_eq_mul]
    ring
  have hx (k : Nat) (hk : k < (openedValues o).length) :
      extFrom (coeffs (openedValues o)) k = (openedValues o)[k] := by
    simpa only [List.append_nil] using extFrom_coeffs [] (openedValues o) k hk
  cases hS : openingsOf S o with
  | mk ta tn qa =>
  have hta : ta = (openingsOf S o).traceAt := by rw [hS]
  have htn' : tn = (openingsOf S o).traceNext := by rw [hS]
  have hqa : qa = (openingsOf S o).quotientAt := by rw [hS]
  subst hta htn' hqa
  simp only [openingsAt, Openings.mk.injEq]
  refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_, funext fun c ↦ funext fun e ↦ ?_⟩
  · rw [hx j (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_left (by simp only [Array.length_toList, htl]; exact j.isLt),
      Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
    rfl
  · rw [hx _ (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_right (by simp only [Array.length_toList, htl]; omega),
      List.getElem_append_left (by simp only [Array.length_toList, htl, htn]; omega)]
    simp only [Array.length_toList, htl, Nat.add_sub_cancel_left, Array.getElem_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
    rfl
  · have hc : c.val < S.chunks := c.isLt
    have he : e.val < 4 := e.isLt
    rw [hx _ (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_right (by simp only [Array.length_toList, htl]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn]; omega)]
    have hL : ∀ l ∈ o.quotientChunks.toList.map (·.toList), l.length = 4 := by
      intro l hl
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hl
      rw [Array.length_toList]
      exact hq4 ch (Array.mem_toList_iff.mp hch)
    have hfm : o.quotientChunks.toList.flatMap (·.toList) =
        (o.quotientChunks.toList.map (·.toList)).flatMap id := by
      rw [List.flatMap_map]; rfl
    have hidx : 2 * S.air.width + (4 * c.val + e.val) - S.air.width - S.air.width =
        4 * c.val + e.val := by omega
    simp only [Array.length_toList, htl, htn, hfm]
    have := getElem_flatMap_four _ hL c.val e.val
      (by simp only [List.length_map, Array.length_toList, hqc]; exact hc) e.isLt
    simp only [List.getElem_map, Array.getElem_toList] at this
    simp only [hidx, this]
    have hc' : c.val < o.quotientChunks.size := by rw [hqc]; exact hc
    have hch : o.quotientChunks.getD c.val #[] = o.quotientChunks[c.val] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc', Option.getD_some]
    have he : e.val < o.quotientChunks[c.val].size := by
      rw [hq4 _ (Array.getElem_mem hc')]; exact e.isLt
    rw [hch, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he, Option.getD_some]

/-- The final polynomial's `2 ^ logFinalPolyLen` coefficients, from the extension elements in
`xs`. -/
def finalPolyAt (S : Iop.Setup KoalaBear.Fast.Ext4) (xs : List F) : Array EF :=
  Array.ofFn fun k : Fin (2 ^ S.params.logFinalPolyLen) ↦ extFrom xs k

theorem finalPolyAt_coeffs (S : Iop.Setup KoalaBear.Fast.Ext4) (coeffs' : Array EF) (rest : List F)
    (h : coeffs'.size = 2 ^ S.params.logFinalPolyLen) :
    finalPolyAt S (coeffs coeffs'.toList ++ rest) = coeffs' := by
  ext k hk₁ hk₂
  · simp only [finalPolyAt, Array.size_ofFn, h]
  · simp only [finalPolyAt, Array.getElem_ofFn]
    rw [extFrom_coeffs rest _ k (by rw [Array.length_toList]; exact hk₂), Array.getElem_toList]

/-! ### The transcript of a prefix -/

section Prefix
variable (S : Iop.Setup KoalaBear.Fast.Ext4)

/-- The digest observed in a duplex call's input, the one a commitment round binds: after the
three leading elements of the first round (initial capacity), first otherwise. -/
def boundDigest (cap : Digest) (input : List F) : Digest :=
  digestAt input (if cap = initCap then 3 else 0)

/-- The folding challenges of ArkLib's oracles, from the answers `sample` of the fold rounds:
`s_j β_j`, `s_j` the shift of word `j`'s domain. -/
noncomputable def betasAt (sample : Nat → Vector F S.streamLen) : FinalStatement 𝕂 S.lastFold :=
  fun j ↦ @lift EF _ gen ^ 2 ^ foldingPrefix S.schedule j.castSucc *
    extAt (sample (3 + j.val)) (challengeOffset S.params.commitPowBits)

/-- The transcript read off the inputs `block j` and answers `sample j` of the rounds `j` and
the hash queries `cache`: the words and FRI oracles extracted under the observed digests, the
observed openings and final polynomial, and the challenges of the answers. -/
noncomputable def prefixTranscript (cache : Merkle.Cache F Digest) (block : Nat → List F)
    (sample : Nat → Vector F S.streamLen) : Sound.Transcript S where
  trace j := committedColumn S cache (digestAt (block 0) 3) j
  alpha := extAt (sample 0) 0
  quotient c e := committedColumn S cache (digestAt (block 1) 0) (4 * c.val + e.val)
  zeta := extAt (sample 1) 0
  openings := openingsAt S (block 2)
  batch := extAt (sample 2) 0
  fri := friOracles S cache
    ((List.range (S.lastFold + 1)).map fun i ↦ digestAt (block (3 + i)) 0)
    (finalPolyAt S (block (4 + S.lastFold)))
  betas := betasAt S sample

/-- The prefix transcript reads the answers of the rounds before the query round only. -/
theorem prefixTranscript_sample_congr (cache : Merkle.Cache F Digest) (block : Nat → List F)
    {sample sample' : Nat → Vector F S.streamLen}
    (h : ∀ j, j ≤ 3 + S.lastFold → sample j = sample' j) :
    prefixTranscript S cache block sample = prefixTranscript S cache block sample' := by
  have hβ : betasAt S sample = betasAt S sample' := by
    funext j
    simp only [betasAt, h (3 + j.val) (by have := j.isLt; omega)]
  simp only [prefixTranscript, h 0 (by omega), h 1 (by omega), h 2 (by omega), hβ]

/-- The query round's grinding sample: the answer's first sample, `0` without grinding. -/
def powAt (u : Vector F S.streamLen) : 𝔽 :=
  if S.params.queryPowBits = 0 then 0 else FastField.toField (u.toList.getD 0 0)

/-- The query round's query samples, after the grinding sample. -/
def queriesAt (u : Vector F S.streamLen) (j : Fin S.params.numQueries) : 𝔽 :=
  FastField.toField (u.toList.getD (challengeOffset S.params.queryPowBits + j.val) 0)

variable (publicValues : List F) (δ δ' loss : NNReal)

/-- Round `i`'s bad event (`Sound/Rbr.lean`) on the transcript `t`, whose round `i` was answered
`u`: `α`, `ζ`, batching, fold `i - 3` with its grinding sample, and the queries. -/
def roundBadAt (i : Nat) (t : Sound.Transcript S) (u : Vector F S.streamLen) : Prop :=
  if i = 0 then AlphaBad S publicValues δ' t.trace t.alpha
  else if i = 1 then ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta
  else if i = 2 then BatchBad S δ δ' t.trace t.alpha t.quotient t.zeta t.openings t.batch
  else if h : i - 3 < S.lastFold + 1 then
    (S.params.commitPowBits ≠ 0 →
      (FastField.toField (u.toList.getD 0 0)).val % 2 ^ S.params.commitPowBits = 0) ∧
      FoldBad S δ loss ⟨i - 3, h⟩ t.fri (t.betas ⟨i - 3, h⟩)
  else if i = 4 + S.lastFold then QueryBad S δ loss t (powAt S u) (queriesAt S u)
  else False

/-- A duplex call is bad after the queries `pre` if `pre` parses it as round `i` and its answer
makes round `i` bad for the prefix transcript on `pre`'s hash queries. -/
def RoundBad (pre : QueryLog (spec S.streamLen)) :
    (t : Query) → Answer S.streamLen t → Prop
  | .duplex cap input, u => match parse pre (.duplex cap input) with
    | some (steps, _) =>
      roundBadAt S publicValues δ δ' loss steps.length
        (prefixTranscript S (logCache pre) (fun j ↦ (steps.map Prod.fst ++ [input]).getD j [])
          fun j ↦ (steps.map Prod.snd ++ [u.2]).getD j (Vector.replicate _ 0)) u.2
    | none => False
  | .leaf _, _ => False
  | .node .., _ => False

end Prefix

end CompStark.Ni
