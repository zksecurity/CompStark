/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.StarkParse
public import CompStark.Fs.StarkFiatShamir
public import CompStark.Ni.QueryBound
public import CompStark.Ni.Setup

/-! # Openings at the filled snapshots

The BCS compiler's selection fills each block's snapshot move with the hash answers logged before
the block's duplex query (`Bcs.fill`). The STARK's commitments open to the same words there as on
all the logged hash answers, so the path a filled selection opens to is the one opened on the
final hash cache:

* `OpensStable`, `openedPath_fill`: generically, when every commitment opens alike on its block's
  snapshot `snapAt (s, b)` (`b` the block's real input, at any chain state `s`) and on the
  snapshot move before it, filling the snapshot moves keeps the opened path;
* `extractCapRow_snapshotAt_of_bound`: without `HashBad`, the rows extracted under a cap bound by
  a duplex input `x` are the same at the snapshot at `(s, x)` as on the whole log, whether or not
  the log holds that key (and the trace, quotient and FRI words read off them);
* `Statement.capOffsets`: the offsets at which Plonky3's verifier absorbs caps, the trace's after
  the STARK's domain separator, FRI's first after FRI's, every other at the block's start;
* `Statement.opensStable_parse`: the messages read off a proof with every snapshot move the log's
  hash cache satisfy `OpensStable`, so the filled selection opens on the final cache;
* `Statement.layout_fills`: every squeezing block of the STARK's layout absorbs some element;
* `Setup.capSizes_of_verifyWith`, `size_commit_preprocessedKeyWith`: an accepted proof's caps and
  the verifying key's have at most `2 ^ capHeight` digests, FRI's at most `twoAdicity F` caps,
  which bounds the digests a fresh `dstar` must avoid; `one_le_hashBadError` makes the bound
  trivial when there are too few digests.
-/

@[expose] public section

namespace CompStark.Fs
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section Generic

variable {F Snap C S O : Type} [DecidableEq Snap] [SampleableType C]

/-- Every commitment along the messages opens, on the snapshot `snapAt (s, b)` of its block's
real input `b` at any chain state `s`, to what it opens on the snapshot move before it (`T` inside
a block). -/
def OpensStable (snapAt : S × List F → Snap) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → (pending tail : List F) →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    Prop
  | _, .done, _, _, _, _, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, pending, tail, msgs =>
      OpensStable snapAt (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false msgs.1
        (pending ++ lay.1 msgs.2.1) tail msgs.2.2
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, pending, tail, msgs =>
      OpensStable snapAt (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false T
        (pending ++ lay.1 msgs.1) tail msgs.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, _, pending, tail, msgs =>
      (∀ s b, blockInput next dec lay.2 false (pending ++ lay.1.observe msgs.2.1) tail msgs.2.2 =
          some b → lay.1.open (snapAt (s, b)) msgs.2.1 = lay.1.open msgs.1 msgs.2.1) ∧
        OpensStable snapAt next dec lay.2 false msgs.1 (pending ++ lay.1.observe msgs.2.1) tail
          msgs.2.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, T, pending, tail, msgs =>
      (∀ s b, blockInput next dec lay.2 false (pending ++ lay.1.observe msgs.1) tail msgs.2 =
          some b → lay.1.open (snapAt (s, b)) msgs.1 = lay.1.open T msgs.1) ∧
        OpensStable snapAt next dec lay.2 false T (pending ++ lay.1.observe msgs.1) tail msgs.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, pending, tail, msgs =>
      if lay.1 = 0 then
        OpensStable snapAt next dec.2 lay.2.2 (lay.1 != 0) msgs.1 (pending ++ lay.2.1 msgs.2.1)
          tail msgs.2.2.2
      else OpensStable snapAt next dec.2 lay.2.2 (lay.1 != 0) msgs.1 [] [] msgs.2.2.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, pending, tail, msgs =>
      if lay.1 = 0 then
        OpensStable snapAt next dec.2 lay.2.2 (lay.1 != 0) T (pending ++ lay.2.1 msgs.1) tail
          msgs.2.2
      else OpensStable snapAt next dec.2 lay.2.2 (lay.1 != 0) T [] [] msgs.2.2

/-- A snapshot move `T` before an oracle node, as inside a block. -/
theorem opensStable_wrap_oracle (snapAt : S × List F → Snap) {M : Type} [DecidableEq M]
    {interface : OracleInterface.{0, 0} M} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle M _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (start : Bool) (T T₀ : Snap) (pending tail : List F)
    (msgs : Messages PUnit (decoded C (snapCoin (.oracle next) dec lay false)
      (snapDecoder (.oracle next) dec lay false)))
    (h : OpensStable snapAt (.oracle next) dec lay false T pending tail msgs)
    (hT : start = false → T₀ = T) :
    OpensStable snapAt (.oracle next) dec lay start T₀ pending tail (wrapMsgs T start msgs) := by
  cases start
  · rw [hT rfl]
    exact h
  · exact h

/-- A snapshot move `T` before a sender node, as inside a block. -/
theorem opensStable_wrap_sender (snapAt : S × List F → Snap) {Moves : Type}
    {inst : DecidableEq Moves} {rest : Moves → Protocol.{0}}
    (next : (m : Moves) → PublicCoin (rest m))
    (dec : Decoder C (@PublicCoin.sender Moves inst rest next))
    (lay : Layout F Snap (@PublicCoin.sender Moves inst rest next) dec) (start : Bool)
    (T T₀ : Snap) (pending tail : List F)
    (msgs : Messages PUnit (decoded C (snapCoin (@PublicCoin.sender Moves inst rest next) dec lay
      false) (snapDecoder (@PublicCoin.sender Moves inst rest next) dec lay false)))
    (h : OpensStable snapAt (@PublicCoin.sender Moves inst rest next) dec lay false T pending tail
      msgs)
    (hT : start = false → T₀ = T) :
    OpensStable snapAt (@PublicCoin.sender Moves inst rest next) dec lay start T₀ pending tail
      (wrapMsgs T start msgs) := by
  cases start
  · rw [hT rfl]
    exact h
  · exact h

/-- **Openings at the filled snapshots.** Filling the snapshot moves of messages whose
commitments open alike on their blocks' snapshots keeps the opened path. -/
theorem openedPath_fill (coins : List F × List (List F) → ℕ → C) (snapAt : S × List F → Snap)
    (answerAt : S × List F → S × O) : ∀ {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder C coin) (lay : Layout F Snap coin dec) (start : Bool) (s : S) (T₁ T₂ : Snap)
    (pending tail : List F) (acc : List (List F))
    (msgs : Messages PUnit (decoded C (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start))),
    OpensStable snapAt coin dec lay start T₂ pending tail msgs →
    (start = false → T₁ = (blockInput coin dec lay start pending tail msgs).elim T₂
      fun b => snapAt (s, b)) →
    openedPath coins coin dec lay start T₁ pending tail acc
        (setSnaps coin dec lay start
          (fillSnaps snapAt answerAt coin dec lay start s pending tail msgs) msgs) =
      openedPath coins coin dec lay start T₂ pending tail acc msgs
  | _, .done, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, s, T₁, T₂, pending, tail, acc, msgs, h,
      _ => by
    have ih := openedPath_fill coins snapAt answerAt (next msgs.2.1) (dec msgs.2.1)
      (lay.2 msgs.2.1) false s _ msgs.1 (pending ++ lay.1 msgs.2.1) tail acc msgs.2.2 h
      (fun _ => rfl)
    simp only [setSnaps, fillSnaps, openedPath, List.headD_cons, List.tail_cons]
    rw [ih]
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, s, T₁, T₂, pending, tail, acc, msgs, h,
      hT => by
    have ih := openedPath_fill coins snapAt answerAt (next msgs.1) (dec msgs.1)
      (lay.2 msgs.1) false s T₁ T₂ (pending ++ lay.1 msgs.1) tail acc msgs.2 h (fun _ => hT rfl)
    simp only [setSnaps, fillSnaps, openedPath]
    rw [ih]
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, s, T₁, T₂, pending, tail, acc, msgs, h,
      _ => by
    have ih := openedPath_fill coins snapAt answerAt next dec lay.2 false s _ msgs.1
      (pending ++ lay.1.observe msgs.2.1) tail acc msgs.2.2 h.2 (fun _ => rfl)
    simp only [setSnaps, fillSnaps, openedPath, List.headD_cons, List.tail_cons]
    rw [ih]
    congr 2
    funext r
    congr 1
    cases hb : blockInput next dec lay.2 false (pending ++ lay.1.observe msgs.2.1) tail msgs.2.2
    · rfl
    · exact h.1 s _ hb
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, s, T₁, T₂, pending, tail, acc, msgs, h,
      hT => by
    have ih := openedPath_fill coins snapAt answerAt next dec lay.2 false s T₁ T₂
      (pending ++ lay.1.observe msgs.1) tail acc msgs.2 h.2 (fun _ => hT rfl)
    simp only [setSnaps, fillSnaps, openedPath]
    rw [ih]
    congr 2
    funext r
    congr 1
    rw [hT rfl]
    change lay.1.open ((blockInput next dec lay.2 false (pending ++ lay.1.observe msgs.1) tail
      msgs.2).elim T₂ fun b => snapAt (s, b)) msgs.1 = _
    cases hb : blockInput next dec lay.2 false (pending ++ lay.1.observe msgs.1) tail msgs.2
    · rfl
    · exact h.1 s _ hb
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, s, T₁, T₂, pending, tail, acc, msgs, h,
      _ => by
    by_cases h0 : lay.1 = 0
    · have ih := openedPath_fill coins snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0) s
        ((blockInput next dec.2 lay.2.2 (lay.1 != 0) (pending ++ lay.2.1 msgs.2.1) tail
          msgs.2.2.2).elim msgs.1 fun b => snapAt (s, b)) msgs.1
        (pending ++ lay.2.1 msgs.2.1) tail acc msgs.2.2.2
        (by simpa only [OpensStable, h0, ↓reduceIte] using h) (fun _ => rfl)
      simp only [setSnaps, fillSnaps, openedPath, List.headD_cons, List.tail_cons, h0,
        ↓reduceIte]
      rw [ih]
    · have ih := openedPath_fill coins snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0)
        (chainState answerAt s
          ((pending ++ tail ++ lay.2.1 msgs.2.1) :: List.replicate (lay.1 - 1) []))
        (some (pending ++ tail ++ lay.2.1 msgs.2.1) |>.elim msgs.1 fun b => snapAt (s, b))
        msgs.1 [] [] (List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ lay.2.1 msgs.2.1) :: acc)
        msgs.2.2.2 (by simpa only [OpensStable, h0, ↓reduceIte] using h)
        (fun hf => absurd hf (by simp [h0]))
      simp only [setSnaps, fillSnaps, openedPath, List.headD_cons, List.tail_cons, h0,
        ↓reduceIte]
      rw [ih]
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, s, T₁, T₂, pending, tail, acc, msgs, h,
      hT => by
    by_cases h0 : lay.1 = 0
    · have ih := openedPath_fill coins snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0) s T₁ T₂
        (pending ++ lay.2.1 msgs.1) tail acc msgs.2.2
        (by simpa only [OpensStable, h0, ↓reduceIte] using h) (fun _ => by
          rw [hT rfl]
          simp only [blockInput, h0, ↓reduceIte])
      simp only [setSnaps, fillSnaps, openedPath, h0, ↓reduceIte]
      rw [ih]
    · have ih := openedPath_fill coins snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0)
        (chainState answerAt s
          ((pending ++ tail ++ lay.2.1 msgs.1) :: List.replicate (lay.1 - 1) [])) T₁ T₂ [] []
        (List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ lay.2.1 msgs.1) :: acc)
        msgs.2.2 (by simpa only [OpensStable, h0, ↓reduceIte] using h)
        (fun hf => absurd hf (by simp [h0]))
      simp only [setSnaps, fillSnaps, openedPath, h0, ↓reduceIte]
      rw [ih]

end Generic

/-! ### Stable extraction at any duplex input -/

section Stable
open CompStark.Stark CompStark.RandomOracle OracleSpec

variable {F : Type} [BaseField F] {K : ℕ} {offs : List ℕ} {capLen : ℕ}

omit [BaseField F] in
/-- A list whose elements all satisfy `p` is its own longest prefix satisfying `p`. -/
theorem takeWhile_of_forall {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.takeWhile p = l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.takeWhile_cons_of_pos (h x List.mem_cons_self),
      takeWhile_of_forall fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The snapshot at a chain key the log does not hold is the log's whole hash cache. -/
theorem snapshotAt_of_cacheOf_eq_none {L : QueryLog (sumSpec F K)} {q : Digest F × List F}
    (h : Bcs.cacheOf L (.inl q) = none) : Bcs.snapshotAt L q = Bcs.hashCacheOf L := by
  unfold Bcs.snapshotAt
  rw [takeWhile_of_forall]
  intro e he
  have hn := cacheOf_eq_none_iff.mp h
  simp only [ne_eq, decide_eq_true_eq]
  intro hq
  exact hn (hq ▸ List.mem_map_of_mem (f := Sigma.fst) he)

/-- **Stable extraction at any duplex input.** Without `HashBad`, the row extracted under a cap
whose digests the duplex input `x` binds is the same from the snapshot at `(s, x)` and from all
the logged hash answers, whether or not the log holds the key. -/
theorem extractCapRow_snapshotAt_of_bound {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : List (Digest F)}
    (hcap : ∀ d ∈ cap, d ∈ boundDigests offs capLen x) (k h i : ℕ) :
    Merkle.extractCapRow (merkleCache (Bcs.snapshotAt L (s, x))) k h i cap =
      Merkle.extractCapRow (merkleCache (Bcs.hashCacheOf L)) k h i cap := by
  cases hc : Bcs.cacheOf L (.inl (s, x)) with
  | none => rw [snapshotAt_of_cacheOf_eq_none hc]
  | some a => exact extractCapRow_snapshotAt hL (mem_of_cacheOf hc) hcap k h i

variable {EF : Type} [Challenge F EF]

/-- `extractCapRow_snapshotAt_of_bound` for the extracted leaves under a cap. -/
theorem leafRow_snapshotAt_of_bound {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : Cap F}
    (hcap : ∀ d ∈ cap.toList, d ∈ boundDigests offs capLen x) (k h i : ℕ) :
    Ni.leafRow (merkleCache (Bcs.snapshotAt L (s, x))) k h i cap =
      Ni.leafRow (merkleCache (Bcs.hashCacheOf L)) k h i cap := by
  unfold Ni.leafRow
  rw [extractCapRow_snapshotAt_of_bound hL s x hcap]

/-- `extractCapRow_snapshotAt_of_bound` for the trace message under a cap. -/
theorem traceMessageOf_snapshotAt_of_bound (S : Iop.Setup EF) {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : Cap F}
    (hcap : ∀ d ∈ cap.toList, d ∈ boundDigests offs capLen x) :
    S.traceMessageOf (merkleCache (Bcs.snapshotAt L (s, x))) cap =
      S.traceMessageOf (merkleCache (Bcs.hashCacheOf L)) cap := by
  funext jx
  simp only [Iop.Setup.traceMessageOf, Ni.committedColumn, leafRow_snapshotAt_of_bound hL s x hcap]

/-- `extractCapRow_snapshotAt_of_bound` for the quotient message under a cap. -/
theorem quotientMessageOf_snapshotAt_of_bound (S : Iop.Setup EF) {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : Cap F}
    (hcap : ∀ d ∈ cap.toList, d ∈ boundDigests offs capLen x) :
    S.quotientMessageOf (merkleCache (Bcs.snapshotAt L (s, x))) cap =
      S.quotientMessageOf (merkleCache (Bcs.hashCacheOf L)) cap := by
  funext cex
  simp only [Iop.Setup.quotientMessageOf, Ni.committedColumn,
    leafRow_snapshotAt_of_bound hL s x hcap]

/-- `extractCapRow_snapshotAt_of_bound` for a FRI layer's word under a cap. -/
theorem friWordOf_snapshotAt_of_bound {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : Cap F}
    (hcap : ∀ d ∈ cap.toList, d ∈ boundDigests offs capLen x) (capHeight m k : ℕ) :
    Iop.friWordOf (EF := EF) (merkleCache (Bcs.snapshotAt L (s, x))) capHeight cap m k =
      Iop.friWordOf (merkleCache (Bcs.hashCacheOf L)) capHeight cap m k := by
  funext z
  simp only [Iop.friWordOf, Ni.friWordAt, leafRow_snapshotAt_of_bound hL s x hcap]

end Stable

end CompStark.Fs

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF]

/-- FRI's domain separator at the trace length `2 ^ n`. -/
def friSeedAt (n : ℕ) : List F :=
  DomainSeparator.friSeed F EF (Fri.foldSchedule C.params.maxLogArity
    (C.params.logBlowup + C.params.logFinalPolyLen) (n + C.params.logBlowup)
    [n + C.params.logBlowup]) (2 ^ C.params.logFinalPolyLen) C.params.commitPowBits
    C.params.queryPowBits C.params.numQueries (n + C.params.logBlowup) C.params.logBlowup
    C.params.maxLogArity

/-- The offsets at which the duplex inputs of Plonky3's verifier carry Merkle caps: the trace's
after the STARK's domain separator, the quotient's and every later FRI commitment's at the block's
start, and FRI's first after FRI's domain separator, at every length up to the two-adicity. -/
def capOffsets : List ℕ :=
  (starkSeedOf EF C.params C.air 0).length :: 0 ::
    (List.range (twoAdicity F + 1)).map fun n ↦ (C.friSeedAt EF n).length

theorem length_capOffsets : (C.capOffsets EF).length = twoAdicity F + 3 := by
  simp only [capOffsets, List.length_cons, List.length_map, List.length_range]

variable {C EF}

theorem friSeed_setup (n : C.Length) : (C.setup EF n).friSeed = C.friSeedAt EF n.1 := rfl

/-- FRI's domain separator at an admitted length is observed at one of the cap offsets. -/
theorem length_friSeed_mem_capOffsets (n : C.Length) :
    (C.setup EF n).friSeed.length ∈ C.capOffsets EF := by
  have := n.2.sound.twoAdic
  rw [friSeed_setup]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨n.1, List.mem_range.mpr (by omega), rfl⟩))

/-- The STARK's domain separator at an admitted length is observed at the first cap offset. -/
theorem length_starkSeed_mem_capOffsets (n : ℕ) :
    (starkSeedOf EF C.params C.air n).length ∈ C.capOffsets EF := by
  rw [DomainSeparator.length_starkSeedOf EF _ _ n 0]
  exact List.mem_cons_self

theorem zero_mem_capOffsets : 0 ∈ C.capOffsets EF :=
  List.mem_cons_of_mem _ List.mem_cons_self

end CompStark.Iop.Statement

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section FriStable
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable {K m : ℕ} {top d t : ℕ} {P : Fri.Params} {L : QueryLog (sumSpec F K)} {offs : List ℕ}
  (finalPoly : Array EF) (queryWitness : F)

/-- FRI's commitments read off a proof open alike at their blocks' snapshots: the first after
`seed` at an offset of `offs`, the later ones at the block's start. -/
theorem opensStable_parseFri (hK : 0 < K) (hL : ¬ HashBad offs (2 ^ P.capHeight) L)
    (h0 : 0 ∈ offs) : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) (start : Bool) (seed : List F)
    (cws : List (Cap F × F)) (msgs) (pending tail : List F),
    parseFri K m top d t P (Bcs.hashCacheOf L) finalPoly queryWitness s start seed cws =
      some msgs → (pending ++ seed).length ∈ offs →
    OpensStable (Bcs.snapshotAt L) (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder K m top d t P.commitPowBits P.queryPowBits s)
      (friLayout K m top d t P.commitPowBits P.queryPowBits P.capHeight s seed) start
      (Bcs.hashCacheOf L) pending tail msgs
  | _, .final, start, seed, [], msgs, pending, tail, hp, _ => by
    obtain rfl := Option.some.inj hp
    refine opensStable_wrap_sender _ _ _ _ _ _ _ _ _ _ ?_ fun _ => rfl
    change ite _ True True
    split <;> trivial
  | _, .final, _, _, _ :: _, _, _, _, hp, _ => by simp [parseFri] at hp
  | _, .fold .., _, _, [], _, _, _, hp, _ => by simp [parseFri] at hp
  | n, .fold k _ _ rest, start, seed, cw :: cws, msgs, pending, tail, hp, hoff => by
    simp only [parseFri] at hp
    obtain ⟨c, hc, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hsq : squeezesFor K (extSamples (EF := EF) P.commitPowBits) ≠ 0 :=
      squeezesFor_ne_zero hK (by
        have : 0 < Challenge.d EF := (Challenge.params EF).d_pos
        simp only [extSamples]
        omega)
    have ih := opensStable_parseFri hK hL h0 rest
      (squeezesFor K (extSamples (EF := EF) P.commitPowBits) != 0) [] cws r [] [] hr
      (by simpa only [List.append_nil, List.length_nil] using h0)
    refine opensStable_wrap_oracle _ _ _ _ _ _ _ _ _ _ ⟨fun s b hb => ?_, ?_⟩ fun _ => rfl
    · change (if _ = 0 then _ else some _) = some b at hb
      split at hb
      · exact absurd ‹_› hsq
      obtain rfl := Option.some.inj hb
      refine friWordOf_snapshotAt_of_bound hL s _ (fun x hx => ?_) _ _ _
      have hlen : c.toArray.toList.length ≤ 2 ^ P.capHeight := by
        rw [Array.length_toList, Vector.size_toArray]
        exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
      have := mem_boundDigests_of_cap (pending ++ seed) (tail ++ extWitnessElems (EF := EF)
        P.commitPowBits
        (extWitnessOf (K := K) (m := m) P.commitPowBits cw.2)) _ hoff hlen hx
      change x ∈ boundDigests offs (2 ^ P.capHeight) (pending ++ (seed ++ capOfElems c) ++
        tail ++ extWitnessElems (EF := EF) P.commitPowBits
          (extWitnessOf (K := K) (m := m) P.commitPowBits cw.2))
      simpa only [capOfElems, capElems, List.append_assoc] using this
    · change ite _ _ _
      split
      · exact absurd ‹_› hsq
      · exact ih

variable (K m top t P) in
/-- Every challenge of FRI's layout that squeezes has observations since the last squeeze, when
the final polynomial has coefficients. -/
theorem friLayout_fills (hd : 0 < d) : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) (seed : List F)
    (filled : Prop), Layout.Fills (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder K m top d t P.commitPowBits P.queryPowBits s)
      (friLayout K m top d t P.commitPowBits P.queryPowBits P.capHeight s seed) filled
  | _, .final, _, _ => fun c ↦
      ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (extsElems_ne_nil hd c))),
        fun _ ↦ trivial⟩
  | _, .fold _ _ _ rest, _, _ => fun c ↦
      ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil c))),
        fun _ ↦ friLayout_fills hd rest [] _⟩

end FriStable

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fs OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

/-- An extension draw squeezes, with samples of positive size. -/
theorem squeezesFor_extSamples_ne_zero (hK : 0 < K) (bits : ℕ) :
    squeezesFor K (extSamples (EF := EF) bits) ≠ 0 :=
  squeezesFor_ne_zero hK (by
    have : 0 < Challenge.d EF := (Challenge.params EF).d_pos
    simp only [extSamples]
    omega)

variable (K m) in
/-- Every challenge of the STARK's layout that squeezes has observations since the last
squeeze. -/
theorem layout_fills (S : Setup EF) (filled : Prop) :
    Layout.Fills S.publicCoin (S.decoder K m) (S.layout K m) filled := by
  have hpcs : S.pcsSeed (F := F) ≠ [] := by
    simp only [pcsSeed, DomainSeparator.pcsSeed, DomainSeparator.toElems]
    exact List.cons_ne_nil _ _
  exact fun tc ↦
    ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil tc))),
      fun _ qc ↦ ⟨fun _ _ ↦ Or.inl (Or.inr
          (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil qc))),
        fun _ _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_left_ne_nil hpcs _)),
          fun _ ↦ friLayout_fills K m _ _ S.params (Nat.two_pow_pos _) _ _ _⟩⟩⟩

/-- **The STARK's commitments open alike at their blocks' snapshots**, on messages read off a
proof with every snapshot move the log's hash cache, without `HashBad`: the trace's cap after
`pending`, at an offset of `offs`, the quotient's at the block's start, and FRI's. -/
theorem opensStable_parse (S : Setup EF) (hK : 0 < K) {offs : List ℕ}
    {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs (2 ^ S.params.capHeight) L)
    (h0 : 0 ∈ offs) (hfri : S.friSeed.length ∈ offs) (pending tail : List F)
    (hpend : pending.length ∈ offs) (proof : Proof F EF) (msgs)
    (hp : S.parse K m (Bcs.hashCacheOf L) proof = some msgs) :
    OpensStable (Bcs.snapshotAt L) S.publicCoin (S.decoder K m) (S.layout K m) false
      (Bcs.hashCacheOf L) pending tail msgs := by
  have hlen (h k : ℕ) (c : CapOf F h k) : c.toArray.toList.length ≤ 2 ^ h := by
    rw [Array.length_toList, Vector.size_toArray]
    exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  simp only [parse] at hp
  obtain ⟨tc, htc, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨qc, hqc, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨fri, hfr, rfl⟩ := Option.map_eq_some_iff.mp hp
  refine ⟨fun s b hb => ?_, ?_⟩
  · change (if _ = 0 then _ else some _) = some b at hb
    split at hb
    · exact absurd ‹_› (squeezesFor_extSamples_ne_zero hK 0)
    obtain rfl := Option.some.inj hb
    refine traceMessageOf_snapshotAt_of_bound S hL s _ (fun x hx => ?_)
    have := mem_boundDigests_of_cap (pending ++ []) (tail ++ extWitnessElems (EF := EF) 0
      (extWitnessOf (K := K) (m := m) 0 0)) _ (by simpa only [List.append_nil] using hpend)
      (hlen _ _ tc) hx
    change x ∈ boundDigests offs (2 ^ S.params.capHeight) (pending ++ ([] ++ capOfElems tc) ++
      tail ++ extWitnessElems (EF := EF) 0 (extWitnessOf (K := K) (m := m) 0 0))
    simpa only [capOfElems, capElems, List.append_assoc] using this
  · change ite _ _ _
    split
    · exact absurd ‹_› (squeezesFor_extSamples_ne_zero hK 0)
    refine opensStable_wrap_oracle _ _ _ _ _ _ _ _ _ _ ⟨fun s b hb => ?_, ?_⟩ fun _ => rfl
    · change (if _ = 0 then _ else some _) = some b at hb
      split at hb
      · exact absurd ‹_› (squeezesFor_extSamples_ne_zero hK _)
      obtain rfl := Option.some.inj hb
      refine quotientMessageOf_snapshotAt_of_bound S hL s _ (fun x hx => ?_)
      have := mem_boundDigests_of_cap ([] ++ []) ([] ++ extWitnessElems (EF := EF)
        S.params.oodPowBits (extWitnessOf (K := K) (m := m) S.params.oodPowBits proof.oodWitness))
        _ h0 (hlen _ _ qc) hx
      change x ∈ boundDigests offs (2 ^ S.params.capHeight) ([] ++ ([] ++ capOfElems qc) ++
        [] ++ extWitnessElems (EF := EF) S.params.oodPowBits
          (extWitnessOf (K := K) (m := m) S.params.oodPowBits proof.oodWitness))
      simpa only [capOfElems, capElems, List.append_assoc] using this
    · change ite _ _ _
      split
      · exact absurd ‹_› (squeezesFor_extSamples_ne_zero hK _)
      refine opensStable_wrap_sender _ _ _ _ _ _ _ _ _ _ ?_ fun _ => rfl
      change ite _ _ _
      split
      · exact absurd ‹_› (squeezesFor_extSamples_ne_zero hK _)
      exact opensStable_parseFri _ _ hK hL h0 _ _ _ _ _ [] [] hfr
        (by simpa only [List.nil_append] using hfri)

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {C : Statement F} {EF : Type} [Challenge F EF] {K : ℕ}

variable (C EF) in
/-- Every challenge of the statement's layout that squeezes has observations since the last
squeeze. -/
theorem layout_fills (K m : ℕ) :
    Layout.Fills (C.publicCoin EF) (C.decoder EF K m) (C.layout EF K m) False :=
  fun n ↦ (C.setup EF n).layout_fills K m _

/-- **The statement's commitments open alike at their blocks' snapshots.** Without `HashBad` at
the cap offsets, the messages read off a proof with every snapshot move the log's hash cache open
every commitment, on the snapshot of its block's input, as on the log's hash cache. -/
theorem opensStable_parse (hK : 0 < K) (L : QueryLog (sumSpec F K))
    (hL : ¬ HashBad (C.capOffsets EF) (2 ^ C.params.capHeight) L) (n : C.Length)
    (proof : Proof F EF) (msgs) (hp : C.parse EF K (Bcs.hashCacheOf L) n proof = some msgs)
    (T : (merkleSpec F).QueryCache) (tail : List F) :
    OpensStable (Bcs.snapshotAt L) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
      (C.layout EF K (C.coinCount EF K)) true T [] tail msgs := by
  unfold parse at hp
  obtain ⟨smsgs, hs, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact (C.setup EF n).opensStable_parse (m := C.coinCount EF K) hK hL zero_mem_capOffsets
    (length_friSeed_mem_capOffsets n) ([] ++ starkSeedOf EF C.params C.air n.1) tail
    (by simpa only [List.nil_append] using length_starkSeed_mem_capOffsets n.1) proof smsgs hs

end CompStark.Iop.Statement

/-! ### Sizes of an accepted proof's commitments -/

namespace CompStark.Fs
open CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

omit [BaseField F] in
/-- Commitments fitting a schedule are one per fold, each of at most `2 ^ h` digests. -/
theorem capsFit_sizes (h : ℕ) : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n)
    (cws : List (Cap F × F)), CapsFit F h s cws → ∀ cw ∈ cws, cw.1.size ≤ 2 ^ h
  | _, .final, [], _, _, hcw => absurd hcw List.not_mem_nil
  | _, .final, _ :: _, hf, _, _ => hf.elim
  | _, .fold .., [], hf, _, _ => hf.elim
  | n, .fold k _ _ rest, c :: cws, hf, cw, hcw => by
    rcases List.mem_cons.mp hcw with rfl | hcw
    · rw [hf.1]
      exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
    · exact capsFit_sizes h rest cws hf.2 cw hcw

/-- A schedule folds as many times as it has arities. -/
theorem length_scheduleArities : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n),
    (Iop.scheduleArities s).length = s.numFolds
  | _, .final => rfl
  | _, .fold _ _ _ rest => by
    simp only [Iop.scheduleArities, List.length_cons, length_scheduleArities rest,
      Fri.Interaction.Schedule.numFolds]

/-- A verifying key's cap has at most `2 ^ capHeight` digests. -/
theorem size_commit_preprocessedKeyWith (H : Primitives F Id) (P : Fri.Params) (A : Air F)
    (n : ℕ) (k : PreprocessedKey F) (hk : preprocessedKeyWith H P A n = some k) :
    k.commit.size ≤ 2 ^ P.capHeight := by
  unfold preprocessedKeyWith at hk
  split at hk
  · exact absurd hk (by simp)
  · change some ⟨A.preprocessedWidth, n, merkleCapWith H _ (n + P.logBlowup) P.capHeight⟩ =
      some k at hk
    obtain rfl := Option.some.inj hk
    rw [Ni.merkleCapWith_id, List.size_toArray, List.length_map, List.length_range]
    exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)

/-- The bound on digest clashes is at least one when the digests are at most as many as a
log of `q ≥ 2` entries and `m capLen` more can name. -/
theorem one_le_hashBadError (F : Type) (capLen m q : ℕ) (hq : 2 ≤ q)
    (h : Nat.card F ^ 8 ≤ 1 + (2 + m * capLen) * q + m * capLen) :
    1 ≤ hashBadError F capLen m q := by
  have hn : Nat.card F ^ 8 ≤ (2 + m * capLen) * q ^ 2 := by
    have h1 : (2 + m * capLen) * q + (2 + m * capLen) * q ≤ (2 + m * capLen) * q ^ 2 := by
      rw [← Nat.mul_add, pow_two]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : 1 + m * capLen < (2 + m * capLen) * q := by nlinarith
    omega
  unfold hashBadError
  rcases Nat.eq_zero_or_pos (Nat.card F) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [ENNReal.div_zero]
    · exact le_top
    · have : (0 : ℕ) < (2 + m * capLen) * q ^ 2 := by positivity
      exact_mod_cast this.ne'
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hn

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fs CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- **An accepted proof's commitments are small**: the trace's and the quotient's caps of at
most `2 ^ capHeight` digests, at most `twoAdicity F` FRI commitments, each with at most
`2 ^ capHeight` digests. -/
theorem capSizes_of_verifyWith (S : Setup EF) (H : Primitives F Id)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN) (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    proof.traceCommit.size ≤ 2 ^ S.params.capHeight ∧
      proof.quotientCommit.size ≤ 2 ^ S.params.capHeight ∧
      proof.fri.commits.size ≤ twoAdicity F ∧
      ∀ c ∈ proof.fri.commits, c.size ≤ 2 ^ S.params.capHeight := by
  obtain ⟨hround, hfit⟩ := S.caps_of_verifyWith H vk proof pis hdb h
  have htr := hround 0 (by simp [openingRounds])
  have hqu := hround 1 (by simp [openingRounds])
  simp only [openingRounds, List.cons_append, List.getElem_cons_zero,
    List.getElem_cons_succ] at htr hqu
  have hle : 2 ^ min S.params.capHeight (S.logN + S.params.logBlowup) ≤
      2 ^ S.params.capHeight := Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    Ni.verifyWith_ok H S.params S.air vk proof pis h
  have hL : Ni.friLogMax S.params proof = S.logSize := by
    simp only [Ni.friLogMax, hdb, Iop.Setup.logSize]
  have hh : ∀ x ∈ openingRounds S.air vk proof (Ni.zetaOf H S.params S.air vk proof pis),
      ∀ dp ∈ x.2, dp.1.logSize + S.params.logBlowup = S.logSize := by
    intro x hx dp hdp
    rw [← hL]
    simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      rfl
    · unfold preprocessedRound at hx
      split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        rw [List.mem_singleton] at hdp
        rw [hdp]
      · exact absurd hx List.not_mem_nil
  obtain ⟨-, -, hcs, hcws, -, -, -, -⟩ :=
    Ni.verifyFri_ok H S.params proof.fri _ _ _ hh _ _ hfriOk
  have har : Iop.scheduleArities (S.friSchedule []) = foldSchedule S.params.maxLogArity
      (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize] := by
    rw [friSchedule, Iop.arities_plonky3, Nat.add_comm S.params.logBlowup]
  have hcount : proof.fri.commits.size = (S.friSchedule []).numFolds := by
    rw [← length_scheduleArities, har]
    exact hcs
  refine ⟨htr ▸ hle, hqu ▸ hle, hcount ▸ S.numFolds_friSchedule_le [], fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (Array.mem_toList_iff.mpr hc)
  have hi' : i < proof.fri.commitWitnesses.toList.length := by
    rw [Array.length_toList] at hi ⊢
    omega
  have hmem : (proof.fri.commits.toList[i], proof.fri.commitWitnesses.toList[i]) ∈
      proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList := by
    have hz : i < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length := by
      rw [List.length_zip]
      omega
    rw [← List.getElem_zip (h := hz)]
    exact List.getElem_mem _
  exact capsFit_sizes _ _ _ hfit _ hmem

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement

variable {F : Type} [BaseField F]

/-- The setup and the verifier make at least two oracle calls. -/
theorem two_le_verifierQueries (C : Statement F) (EF : Type) [Challenge F EF] :
    2 ≤ C.verifierQueries EF := by
  have h := Ni.le_foldr_max ((List.range (twoAdicity F + 1)).map
    (verifierCallsAt EF C.params C.air)) (verifierCallsAt EF C.params C.air 0)
    (List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩)
  have h3 : 3 ≤ verifierCallsAt EF C.params C.air 0 := by
    unfold verifierCallsAt
    dsimp only
    omega
  unfold verifierQueries verifierCallsMax
  omega

end CompStark.Iop.Statement
