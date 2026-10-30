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

* the trace and quotient words are extracted under the caps the rounds `0` and `1` observe, the
  FRI oracles under those of the fold rounds, and the final polynomial is the one the query
  round observes, each after the domain separator the round observes first, if any;
* the openings are the extension elements the batching round observes after the PCS's domain
  separator;
* the challenges are read off the answers as the verifier reads them (`extAt`,
  `challengeOffset`), the folding challenges substituted to ArkLib's coset coordinate.

The decoders invert the verifier's observations (`capFrom_append`, `openingsAt_coeffs`,
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

/-- The cap of the `n` digests of `xs` from `offset` on. -/
def capFrom (xs : List F) (offset n : Nat) : Cap F :=
  Array.ofFn fun j : Fin n ↦ digestAt xs (offset + 8 * j.val)

/-- The zero digest is the initial capacity. -/
theorem zero_eq_initCap : (0 : Digest F) = initCap := by
  ext i hi
  simp only [initCap, Vector.getElem_replicate, Vector.getElem_zero]

/-- An entry of a cap read off `xs` is a digest of the wider cap read there, or, past the cap,
the zero digest, the initial capacity. -/
theorem getD_capFrom_mem (xs : List F) (offset n N : Nat) (hn : n ≤ N) (j : Nat) :
    (capFrom xs offset n).toList.getD j 0 ∈ (capFrom xs offset N).toList ∨
      (capFrom xs offset n).toList.getD j 0 = initCap := by
  have hlen : ∀ m, (capFrom xs offset m).toList.length = m := fun m ↦ by
    simp only [capFrom, Array.length_toList, Array.size_ofFn]
  by_cases hj : j < n
  · left
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj), List.mem_iff_getElem]
    refine ⟨j, by rw [hlen]; omega, ?_⟩
    simp only [capFrom, Array.getElem_toList, Array.getElem_ofFn]
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega),
      Option.getD_none, zero_eq_initCap]

theorem capFrom_append (c : Cap F) (pre rest : List F) :
    capFrom (pre ++ capElems c ++ rest) pre.length c.size = c := by
  refine Array.ext (by simp only [capFrom, Array.size_ofFn]) fun j h1 h2 ↦ ?_
  simp only [capFrom, Array.getElem_ofFn]
  have hj : j < c.toList.length := by rw [Array.length_toList]; exact h2
  have hsplit : capElems c = (c.toList.take j).flatMap Vector.toList ++ c[j].toList ++
      (c.toList.drop (j + 1)).flatMap Vector.toList := by
    conv_lhs => rw [capElems, ← List.take_append_drop j c.toList]
    rw [List.flatMap_append, List.drop_eq_getElem_cons hj, List.flatMap_cons,
      Array.getElem_toList]
    simp only [List.append_assoc]
  have hl : (pre ++ (c.toList.take j).flatMap Vector.toList).length = pre.length + 8 * j := by
    rw [List.length_append, length_flatMap_digests, List.length_take, Nat.min_eq_left hj.le]
  rw [hsplit, show pre ++ ((c.toList.take j).flatMap Vector.toList ++ c[j].toList ++
      (c.toList.drop (j + 1)).flatMap Vector.toList) ++ rest =
      (pre ++ (c.toList.take j).flatMap Vector.toList) ++ c[j].toList ++
        ((c.toList.drop (j + 1)).flatMap Vector.toList ++ rest) by
    simp only [List.append_assoc], ← hl, digestAt_append]

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
variable (S : Iop.Setup EF) [S.Folds]

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

/-- The `n` digests of `xs` that end `off` elements before its end, last first: those of a cap
observed just before a grinding witness of `off` elements, whatever comes before the cap. -/
def capBack (xs : List F) (off n : Nat) : List (Digest F) :=
  (List.range n).map fun j ↦ digestAt xs (xs.length - off - 8 * (j + 1))

/-- A cap observed just before `w` is read off the end of the input. -/
theorem capFrom_mem_capBack (pre w : List F) (c : Cap F) (N : Nat) (hc : c.size ≤ N) (j : Nat)
    (hj : j < c.size) :
    (capFrom (pre ++ capElems c ++ w) pre.length c.size).toList.getD j 0 ∈
      capBack (pre ++ capElems c ++ w) w.length N := by
  have hlen : (pre ++ capElems c ++ w).length = pre.length + 8 * c.size + w.length := by
    rw [List.length_append, List.length_append, capElems, length_flatMap_digests,
      Array.length_toList]
    rfl
  rw [List.getD_eq_getElem _ _
    (by simp only [capFrom, Array.length_toList, Array.size_ofFn]; exact hj)]
  simp only [capFrom, Array.getElem_toList, Array.getElem_ofFn, capBack, List.mem_map,
    List.mem_range]
  refine ⟨c.size - 1 - j, by omega, ?_⟩
  rw [hlen]
  congr 1
  omega

/-- The digests a duplex call's input binds (`boundDigests`), for FRI parameters `P` and a STARK
domain separator of `seedLen` elements. -/
def boundDigestsOf (P : Fri.Params) (seedLen : Nat) (cap : Digest F) (input : List F) :
    List (Digest F) :=
  if cap = initCap then (capFrom input seedLen (2 ^ P.capHeight)).toList
  else (capFrom input 0 (2 ^ P.capHeight)).toList ++
    capBack input (challengeOffset P.commitPowBits) (2 ^ P.capHeight)

theorem length_boundDigestsOf_le (P : Fri.Params) (seedLen : Nat) (cap : Digest F)
    (input : List F) : (boundDigestsOf P seedLen cap input).length ≤ 2 ^ (P.capHeight + 1) := by
  unfold boundDigestsOf capBack
  split <;> simp only [Array.length_toList, capFrom, Array.size_ofFn, List.length_append,
    List.length_map, List.length_range, Nat.pow_succ] <;> omega

/-- The digests observed in a duplex call's input, those a commitment round binds: the
`2 ^ capHeight` digests of a cap that is at most as wide, after the STARK's domain separator in
the first round (initial capacity); otherwise those at the start of the input, as the quotient
commitment and FRI's later commitments open their rounds, and those ending before the commit-phase
grinding witness, as FRI's first commitment ends its round after FRI's domain separator. -/
def boundDigests (cap : Digest F) (input : List F) : List (Digest F) :=
  boundDigestsOf S.params (starkSeedS S).length cap input

omit [S.Folds] in
theorem length_boundDigests_le (cap : Digest F) (input : List F) :
    (boundDigests S cap input).length ≤ 2 ^ (S.params.capHeight + 1) :=
  length_boundDigestsOf_le _ _ _ _

/-- The number of entries of the cap of a tree of `2 ^ m` leaves. -/
abbrev capSize (m : Nat) : Nat := 2 ^ min S.params.capHeight m

/-- The levels below fold `i`'s commitment: the extended trace's, less the arities of the folds
up to `i`. -/
def friDepth (i : Nat) : Nat := S.logSize - ((S.foldArities.map PNat.val).take (i + 1)).sum

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
  trace j := committedColumn S cache
    (capFrom (block 0) (starkSeedS S).length (capSize S S.logSize)) j
  alpha := extAt (sample 0) 0
  quotient c e := committedColumn S cache (capFrom (block 1) 0 (capSize S S.logSize))
    (Challenge.d EF * c.val + e.val)
  zeta := extAt (sample 1) (challengeOffset S.params.oodPowBits)
  openings := openingsAt S ((block 2).drop (pcsSeedS S).length)
  batch := extAt (sample 2) (challengeOffset S.params.batchPowBits)
  fri := friOracles S cache
    ((List.range (S.lastFold + 1)).map fun i ↦
      capFrom (block (3 + i)) (if i = 0 then (friSeedS S).length else 0)
        (capSize S (friDepth S i)))
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

/-- A duplex call is bad after the queries `pre` if `pre` parses it as round `i` of a transcript
whose first round observes `S`'s domain separator first, and its answer makes round `i` bad for
the prefix transcript on `pre`'s hash queries. -/
def RoundBad (pre : QueryLog (spec F S.streamLen)) :
    (t : Query F) → Answer S.streamLen t → Prop
  | .duplex cap input, u => match parse pre (.duplex cap input) with
    | some (steps, _) =>
      starkSeedS S <+: (steps.map Prod.fst ++ [input]).getD 0 [] ∧
      roundBadAt S publicValues δ δ' loss steps.length
        (prefixTranscript S (logCache pre) (fun j ↦ (steps.map Prod.fst ++ [input]).getD j [])
          fun j ↦ (steps.map Prod.snd ++ [u.2]).getD j (Vector.replicate _ 0)) u.2
    | none => False
  | .leaf _, _ => False
  | .node .., _ => False

end Prefix

end CompStark.Ni
