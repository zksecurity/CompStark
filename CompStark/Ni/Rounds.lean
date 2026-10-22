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
  round observes, each after the domain separator the round observes first, if any;
* the openings are the extension elements the batching round observes after the PCS's domain
  separator;
* the challenges are read off the answers as the verifier reads them (`extAt`,
  `challengeOffset`), the folding challenges substituted to ArkLib's coset coordinate.

The decoders invert the verifier's observations (`digestAt_append`, `openingsAt_coeffs`,
`finalPolyAt_coeffs`), so on a proof's schedule the prefix transcript is the extracted one.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.Sound CompStark.Iop CompStark.RandomOracle
open Polynomial Fri.Spec OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### Decoding observations -/

/-- The digest of the eight elements of `xs` from `offset` on. -/
def digestAt (xs : List F) (offset : Nat) : Digest F := Vector.ofFn fun k ↦ xs.getD (offset + k) 0

theorem digestAt_append (d : Digest F) (pre rest : List F) :
    digestAt (pre ++ d.toList ++ rest) pre.length = d := by
  ext k hk
  rw [digestAt, Vector.getElem_ofFn, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (l₁ := d.toList) (by rw [Vector.length_toList]; exact hk),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]

theorem digestAt_append_zero (d : Digest F) (rest : List F) : digestAt (d.toList ++ rest) 0 = d :=
  digestAt_append d [] rest

/-- The extension element of the `d` elements of `xs` from `d k` on. -/
def extFrom (xs : List F) (k : Nat) : EF :=
  Challenge.ofCoeffs ((xs.drop (Challenge.d EF * k)).take (Challenge.d EF))

theorem extFrom_coeffs (rest : List F) :
    ∀ (l : List EF) (k : Nat) (hk : k < l.length), extFrom (coeffs l ++ rest) k = l[k]
  | x :: l, 0, _ => by
    rw [extFrom, Nat.mul_zero, List.drop_zero, coeffs, List.flatMap_cons, List.append_assoc,
      List.take_left' (Challenge.length_coeffs x), List.getElem_cons_zero]
    exact Challenge.ofCoeffs_coeffs x
  | x :: l, k + 1, hk => by
    have ih := extFrom_coeffs rest l k (by simp only [List.length_cons] at hk; omega)
    rw [extFrom, coeffs, List.flatMap_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm,
      ← List.drop_drop, List.drop_left' (Challenge.length_coeffs x), List.getElem_cons_succ, ← ih]
    rfl

/-- The openings of the extension elements in `xs`: the trace at `ζ` and, if opened, at `ζ ω`,
the quotient chunks' coordinates, and the preprocessed trace at `ζ` and, if opened, at `ζ ω`, in
the order the verifier observes them. -/
noncomputable def openingsAt (S : Iop.Setup EF) (xs : List F) : Openings S where
  traceAt j := Challenge.toSpec (extFrom (EF := EF) xs j)
  traceNext j := Challenge.toSpec (extFrom (EF := EF) xs (S.air.width + j))
  quotientAt c e := Challenge.toSpec (extFrom (EF := EF) xs
    (S.air.width + S.air.mainNextWidth + (Challenge.d EF * c.val + e.val)))
  preprocessedAt j := Challenge.toSpec (extFrom (EF := EF) xs
    (S.air.width + S.air.mainNextWidth + Challenge.d EF * S.chunks + j))
  preprocessedNext j := Challenge.toSpec (extFrom (EF := EF) xs
    (S.air.width + S.air.mainNextWidth + Challenge.d EF * S.chunks + S.air.preprocessedWidth + j))
  permAt _ _ := 0
  permNext _ _ := 0

theorem getElem_flatMap_of_length {α : Type} (w : Nat) (L : List (List α))
    (hL : ∀ l ∈ L, l.length = w) (c e : Nat) (hc : c < L.length) (he : e < w)
    (h : w * c + e < (L.flatMap id).length) :
    (L.flatMap id)[w * c + e] = L[c][e]'(by rw [hL _ (List.getElem_mem hc)]; exact he) := by
  induction L generalizing c with
  | nil => exact absurd hc (Nat.not_lt_zero _)
  | cons l L ih =>
    have hl : l.length = w := hL l List.mem_cons_self
    simp only [List.flatMap_cons, id] at h ⊢
    cases c with
    | zero =>
      rw [List.getElem_append_left (by rw [hl]; omega)]
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    | succ c =>
      rw [List.getElem_append_right (by rw [hl, Nat.mul_succ]; omega)]
      have := ih (fun l' hl' ↦ hL l' (List.mem_cons_of_mem _ hl')) c
        (by simp only [List.length_cons] at hc; omega)
        (by simp only [List.length_append, hl, Nat.mul_succ] at h; omega)
      simp only [hl, show w * (c + 1) + e - w = w * c + e by rw [Nat.mul_succ]; omega, this,
        List.getElem_cons_succ]

theorem openingsAt_coeffs (S : Iop.Setup EF) (o : OpenedValues EF) (rest : List F)
    (htl : o.traceLocal.size = S.air.width)
    (htn : (o.traceNext.getD #[]).size = S.air.mainNextWidth)
    (hqc : o.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF)
    (hpl : (o.preprocessedLocal.getD #[]).size = S.air.preprocessedWidth)
    (hpn : (o.preprocessedNext.getD #[]).size = S.air.preprocessedNextWidth) :
    openingsAt S (coeffs (openedValues o) ++ rest) = openingsOf S o := by
  have hq : (o.quotientChunks.toList.flatMap (·.toList)).length =
      Challenge.d EF * S.chunks := by
    rw [List.length_flatMap, List.sum_eq_length_nsmul _ (Challenge.d EF) (by
      intro n hn
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hn
      exact hq4 ch (Array.mem_toList_iff.mp hch)), List.length_map, Array.length_toList, hqc,
      smul_eq_mul, Nat.mul_comm]
  have hlen : (openedValues o).length = S.air.width + S.air.mainNextWidth +
      Challenge.d EF * S.chunks + S.air.preprocessedWidth + S.air.preprocessedNextWidth := by
    simp only [openedValues, List.length_append, Array.length_toList, htl, htn, hq, hpl, hpn]
  have hx (k : Nat) (hk : k < (openedValues o).length) :
      extFrom (coeffs (openedValues o) ++ rest) k = (openedValues o)[k] :=
    extFrom_coeffs rest (openedValues o) k hk
  cases hS : openingsOf S o with
  | mk ta tn qa pa pn ma mn =>
  have hta : ta = (openingsOf S o).traceAt := by rw [hS]
  have htn' : tn = (openingsOf S o).traceNext := by rw [hS]
  have hqa : qa = (openingsOf S o).quotientAt := by rw [hS]
  have hpa : pa = (openingsOf S o).preprocessedAt := by rw [hS]
  have hpn' : pn = (openingsOf S o).preprocessedNext := by rw [hS]
  have hma : ma = (openingsOf S o).permAt := by rw [hS]
  have hmn : mn = (openingsOf S o).permNext := by rw [hS]
  subst hta htn' hqa hpa hpn' hma hmn
  simp only [openingsAt, Openings.mk.injEq]
  refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_, funext fun c ↦ funext fun e ↦ ?_,
    funext fun j ↦ ?_, funext fun j ↦ ?_, funext fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
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
    have he : e.val < Challenge.d EF := e.isLt
    have hce : Challenge.d EF * c.val + e.val < Challenge.d EF * S.chunks :=
      (Nat.add_lt_add_left he _).trans_le (Nat.mul_le_mul_left _ hc)
    rw [hx _ (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_right (by simp only [Array.length_toList, htl]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn]; omega),
      List.getElem_append_left (by simp only [Array.length_toList, htl, htn, hq]; omega)]
    have hL : ∀ l ∈ o.quotientChunks.toList.map (·.toList), l.length = Challenge.d EF := by
      intro l hl
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hl
      rw [Array.length_toList]
      exact hq4 ch (Array.mem_toList_iff.mp hch)
    have hfm : o.quotientChunks.toList.flatMap (·.toList) =
        (o.quotientChunks.toList.map (·.toList)).flatMap id := by
      rw [List.flatMap_map]; rfl
    have hidx : S.air.width + S.air.mainNextWidth + (Challenge.d EF * c.val + e.val) -
        S.air.width - S.air.mainNextWidth =
        Challenge.d EF * c.val + e.val := by omega
    simp only [Array.length_toList, htl, htn, hfm]
    have := getElem_flatMap_of_length _ _ hL c.val e.val
      (by simp only [List.length_map, Array.length_toList, hqc]; exact hc) e.isLt
    simp only [List.getElem_map, Array.getElem_toList] at this
    simp only [hidx, this]
    have hc' : c.val < o.quotientChunks.size := by rw [hqc]; exact hc
    have hch : o.quotientChunks.getD c.val #[] = o.quotientChunks[c.val] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc', Option.getD_some]
    have he : e.val < o.quotientChunks[c.val].size := by
      rw [hq4 _ (Array.getElem_mem hc')]; exact e.isLt
    rw [hch, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he, Option.getD_some]
  · have hj := j.isLt
    rw [hx _ (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_right (by simp only [Array.length_toList, htl]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn, hq]; omega),
      List.getElem_append_left (by simp only [Array.length_toList, htl, htn, hq, hpl]; omega)]
    simp only [Array.length_toList, htl, htn, hq, Array.getElem_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hpl]; omega),
      Option.getD_some]
    congr 2
    omega
  · have hj := j.isLt
    rw [hx _ (by omega)]
    simp only [openingsOf, openedValues, List.append_assoc]
    rw [List.getElem_append_right (by simp only [Array.length_toList, htl]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn, hq]; omega),
      List.getElem_append_right (by simp only [Array.length_toList, htl, htn, hq, hpl]; omega)]
    simp only [Array.length_toList, htl, htn, hq, hpl, Array.getElem_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hpn]; omega),
      Option.getD_some]
    congr 2
    omega

/-- The final polynomial's `2 ^ logFinalPolyLen` coefficients, from the extension elements in
`xs`. -/
def finalPolyAt {lookups : List (Lookup F)} (S : Iop.Setup EF lookups) (xs : List F) :
    Array EF :=
  Array.ofFn fun k : Fin (2 ^ S.params.logFinalPolyLen) ↦ extFrom xs k

theorem finalPolyAt_coeffs {lookups : List (Lookup F)} (S : Iop.Setup EF lookups)
    (coeffs' : Array EF) (rest : List F)
    (h : coeffs'.size = 2 ^ S.params.logFinalPolyLen) :
    finalPolyAt S (coeffs coeffs'.toList ++ rest) = coeffs' := by
  ext k hk₁ hk₂
  · simp only [finalPolyAt, Array.size_ofFn, h]
  · simp only [finalPolyAt, Array.getElem_ofFn]
    rw [extFrom_coeffs rest _ k (by rw [Array.length_toList]; exact hk₂), Array.getElem_toList]

/-! ### The transcript of a prefix -/

section Prefix
variable (S : Iop.Setup EF)

/-- The STARK's domain separator on a proof for `S`. -/
def starkSeedS : List F := starkSeedOf EF S.params S.air S.logN

/-- The claimed evaluation counts of a proof for `S`. -/
def pcsCountsS : List (List (List Nat)) :=
  [[S.air.width :: if S.air.mainNextRow then [S.air.width] else []],
    List.replicate S.chunks [Challenge.d EF]] ++
    if S.air.preprocessedWidth = 0 then [] else
      [[S.air.preprocessedWidth ::
        if S.air.opensPreprocessedNext then [S.air.preprocessedWidth] else []]]

/-- The PCS's domain separator on a proof for `S`. -/
def pcsSeedS : List F := DomainSeparator.pcsSeed F EF (pcsCountsS S) S.params.batchPowBits

/-- FRI's domain separator on a proof for `S`. -/
def friSeedS : List F :=
  DomainSeparator.friSeed F EF (S.foldArities.map PNat.val) (2 ^ S.params.logFinalPolyLen)
    S.params.commitPowBits S.params.queryPowBits S.params.numQueries S.logSize
    S.params.logBlowup S.params.maxLogArity

/-- The digest observed in a duplex call's input, the one a commitment round binds: after the
STARK's domain separator in the first round (initial capacity), after FRI's in the first fold
round (an input of its length), first otherwise. -/
def boundDigest (cap : Digest F) (input : List F) : Digest F :=
  digestAt input (if cap = initCap then (starkSeedS S).length
    else if input.length = (friSeedS S).length + 8 + challengeOffset S.params.commitPowBits
      then (friSeedS S).length else 0)

/-- The folding challenges of ArkLib's oracles, from the answers `sample` of the fold rounds:
`s_j β_j`, `s_j` the shift of word `j`'s domain. -/
noncomputable def betasAt (sample : Nat → Vector F S.streamLen) : FinalStatement 𝕂 S.lastFold :=
  fun j ↦ lift gen ^ 2 ^ foldingPrefix S.schedule j.castSucc *
    extAt (sample (3 + j.val)) (challengeOffset S.params.commitPowBits)

/-- The transcript read off the inputs `block j` and answers `sample j` of the rounds `j` and
the hash queries `cache`: the words and FRI oracles extracted under the observed digests, the
observed openings and final polynomial, and the challenges of the answers. -/
noncomputable def prefixTranscript (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    (sample : Nat → Vector F S.streamLen) : Sound.Transcript S where
  trace j := committedColumn S cache (digestAt (block 0) (starkSeedS S).length) j
  alpha := extAt (sample 0) 0
  quotient c e := committedColumn S cache (digestAt (block 1) 0) (Challenge.d EF * c.val + e.val)
  zeta := extAt (sample 1) (challengeOffset S.params.oodPowBits)
  openings := openingsAt S ((block 2).drop (pcsSeedS S).length)
  batch := extAt (sample 2) (challengeOffset S.params.batchPowBits)
  fri := friOracles S cache
    ((List.range (S.lastFold + 1)).map fun i ↦
      digestAt (block (3 + i)) (if i = 0 then (friSeedS S).length else 0))
    (finalPolyAt S (block (4 + S.lastFold)))
  betas := betasAt S sample

/-- The prefix transcript reads the answers of the rounds before the query round only. -/
theorem prefixTranscript_sample_congr (cache : Merkle.Cache F (Digest F)) (block : Nat → List F)
    {sample sample' : Nat → Vector F S.streamLen}
    (h : ∀ j, j ≤ 3 + S.lastFold → sample j = sample' j) :
    prefixTranscript S cache block sample = prefixTranscript S cache block sample' := by
  have hβ : betasAt S sample = betasAt S sample' := by
    funext j
    simp only [betasAt, h (3 + j.val) (by have := j.isLt; omega)]
  simp only [prefixTranscript, h 0 (by omega), h 1 (by omega), h 2 (by omega), hβ]

/-- The query round's grinding sample: the answer's first sample, `0` without grinding. -/
def powAt (u : Vector F S.streamLen) : F :=
  if S.params.queryPowBits = 0 then 0 else (u.toList.getD 0 0)

/-- The query round's query samples, after the grinding sample. -/
def queriesAt (u : Vector F S.streamLen) (j : Fin S.params.numQueries) : F :=
  (u.toList.getD (challengeOffset S.params.queryPowBits + j.val) 0)

variable (publicValues : List F) (δ δ' loss : NNReal)

/-- Round `i`'s bad event (`Sound/Rbr.lean`) on the transcript `t`, whose round `i` was answered
`u`: `α`; `ζ`, batching and fold `i - 3`, each with its grinding sample, the answer's first; and
the queries. -/
def roundBadAt (i : Nat) (t : Sound.Transcript S) (u : Vector F S.streamLen) : Prop :=
  if i = 0 then AlphaBad S publicValues δ' t.trace t.alpha
  else if i = 1 then
    (S.params.oodPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat ((u.toList.getD 0 0)) % 2 ^ S.params.oodPowBits = 0) ∧
      ZetaBad S publicValues δ' t.trace t.alpha t.quotient t.zeta
  else if i = 2 then
    (S.params.batchPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat ((u.toList.getD 0 0)) % 2 ^ S.params.batchPowBits = 0) ∧
      BatchBad S δ δ' t.trace t.alpha t.quotient t.zeta t.openings t.batch
  else if h : i - 3 < S.lastFold + 1 then
    (S.params.commitPowBits ≠ 0 →
      CompPoly.CanonicalNat.toNat ((u.toList.getD 0 0)) % 2 ^ S.params.commitPowBits = 0) ∧
      FoldBad S δ loss ⟨i - 3, h⟩ t.fri (t.betas ⟨i - 3, h⟩)
  else if i = 4 + S.lastFold then QueryBad S δ loss t (powAt S u) (queriesAt S u)
  else False

/-- A duplex call is bad after the queries `pre` if `pre` parses it as round `i` and its answer
makes round `i` bad for the prefix transcript on `pre`'s hash queries. -/
def RoundBad (pre : QueryLog (spec F S.streamLen)) :
    (t : Query F) → Answer S.streamLen t → Prop
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
