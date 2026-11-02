/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.BatchParse
public import CompStark.Fs.StarkStable
public import CompStark.Fs.DomainSeparator
public import ToMathlib.Data.ByteArray

/-! # The batch's openings at the filled snapshots

As for the STARK (`StarkStable.lean`): the batch STARK's commitments open to the same words at
their blocks' snapshots as on all the logged hash answers, so the path a filled selection opens to
is the one opened on the final hash cache.

* `prefix_blockInput`: a block's input extends what was observed before it in the block;
* `matColumnCap_snapshotAt_of_bound`, `Batch.Setup.traceMessageOf_snapshotAt` (and the permutation
  and quotient messages): without `HashBad`, the columns of mixed heights read under a cap bound by
  a duplex input are the same at the snapshot of that input as on the whole log;
* `Batch.Statement.capOffsets`: the offsets at which Plonky3's batch verifier absorbs caps, the
  main tree's after the batch's domain separator and the degree bits, FRI's first after FRI's
  domain separator (`DomainSeparator.length_friSeed`: of a length fixed by the number of folds),
  every other at the block's start;
* `Batch.Statement.opensStable_parse`: the messages read off a proof with every snapshot move the
  log's hash cache satisfy `OpensStable`;
* `Batch.Statement.layout_fills`: every squeezing block of the batch's layout absorbs some element.
-/

@[expose] public section

namespace CompStark.Fs
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section Generic

variable {F Snap C S : Type} [DecidableEq Snap] [SampleableType C]

/-- A block's input extends the elements observed before it in the block. -/
theorem prefix_blockInput : ∀ {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder C coin) (lay : Layout F Snap coin dec) (start : Bool) (pending tail : List F)
    (msgs : Messages PUnit (decoded C (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start))) (b : List F),
    blockInput coin dec lay start pending tail msgs = some b → ∃ r, b = pending ++ r
  | _, .done, _, _, _, _, _, _, _, h => by cases h
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, pending, tail, msgs, b, h => by
    obtain ⟨r, rfl⟩ := prefix_blockInput (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false
      (pending ++ lay.1 msgs.2.1) tail msgs.2.2 b h
    exact ⟨_, List.append_assoc _ _ _⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, pending, tail, msgs, b, h => by
    obtain ⟨r, rfl⟩ := prefix_blockInput (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false
      (pending ++ lay.1 msgs.1) tail msgs.2 b h
    exact ⟨_, List.append_assoc _ _ _⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, pending, tail, msgs, b, h => by
    obtain ⟨r, rfl⟩ := prefix_blockInput next dec lay.2 false
      (pending ++ lay.1.observe msgs.2.1) tail msgs.2.2 b h
    exact ⟨_, List.append_assoc _ _ _⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, pending, tail, msgs, b, h => by
    obtain ⟨r, rfl⟩ := prefix_blockInput next dec lay.2 false
      (pending ++ lay.1.observe msgs.1) tail msgs.2 b h
    exact ⟨_, List.append_assoc _ _ _⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, pending, tail, msgs, b, h => by
    simp only [blockInput] at h
    split at h
    · obtain ⟨r, rfl⟩ := prefix_blockInput next dec.2 lay.2.2 _ _ tail msgs.2.2.2 b h
      exact ⟨_, List.append_assoc _ _ _⟩
    · obtain rfl := Option.some.inj h
      exact ⟨_, List.append_assoc _ _ _⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, pending, tail, msgs, b, h => by
    simp only [blockInput] at h
    split at h
    · obtain ⟨r, rfl⟩ := prefix_blockInput next dec.2 lay.2.2 _ _ tail msgs.2.2 b h
      exact ⟨_, List.append_assoc _ _ _⟩
    · obtain rfl := Option.some.inj h
      exact ⟨_, List.append_assoc _ _ _⟩

/-- `OpensStable` at an oracle node inside a block, from the commitment's openings at the
snapshots of the inputs extending what the block observed before it and after it. -/
theorem opensStable_oracle_of (snapAt : S × List F → Snap) {M : Type} [DecidableEq M]
    {interface : OracleInterface.{0, 0} M} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle M _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (T : Snap) (pending tail : List F)
    (msgs : Messages PUnit (decoded C (snapCoin (.oracle next) dec lay false)
      (snapDecoder (.oracle next) dec lay false)))
    (h₁ : ∀ s r, lay.1.open (snapAt (s, pending ++ lay.1.observe msgs.1 ++ r)) msgs.1 =
      lay.1.open T msgs.1)
    (h₂ : OpensStable snapAt next dec lay.2 false T (pending ++ lay.1.observe msgs.1) tail
      msgs.2) :
    OpensStable snapAt (.oracle next) dec lay false T pending tail msgs := by
  refine ⟨fun s b hb => ?_, h₂⟩
  obtain ⟨r, rfl⟩ := prefix_blockInput _ _ _ _ _ _ _ b hb
  exact h₁ s r

end Generic

section Stable
open CompStark.Stark CompStark.RandomOracle OracleSpec

variable {F : Type} [BaseField F] {K : ℕ} {offs : List ℕ} {capLen : ℕ}

/-- **Stable columns of mixed heights at any duplex input.** Without `HashBad`, a column read
under a cap whose digests the duplex input `x` binds is the same from the snapshot at `(s, x)` and
from all the logged hash answers, whether or not the log holds the key. -/
theorem matColumnCap_snapshotAt_of_bound {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) (s : Digest F) (x : List F) {cap : List (Digest F)}
    (hcap : ∀ d ∈ cap, d ∈ boundDigests offs capLen x) (capHeight top : ℕ) (hs ws : List ℕ)
    (t j m r : ℕ) :
    Merkle.matColumnCap (merkleCache (Bcs.snapshotAt L (s, x))) cap capHeight top hs ws t j m r =
      Merkle.matColumnCap (merkleCache (Bcs.hashCacheOf L)) cap capHeight top hs ws t j m r := by
  cases hc : Bcs.cacheOf L (.inl (s, x)) with
  | none => rw [snapshotAt_of_cacheOf_eq_none hc]
  | some a => exact matColumnCap_snapshotAt hL (mem_of_cacheOf hc) hcap capHeight top hs ws t j m r

end Stable

end CompStark.Fs

/-! ### FRI's domain separator -/

namespace CompStark.DomainSeparator

theorem length_keccak (s : String) : (keccak s).toList.length = 32 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  change (keccak s).size = 32
  simp only [keccak, VCVio.Algorithms.Keccak.keccak256, VCVio.Algorithms.Keccak.squeeze_size]

/-- The seed bytes have one length for every pattern, for labels of as many numbers. -/
theorem length_seedBytes_steps (version : Nat) (name : String) {steps steps' : List Step}
    {inst inst' : List Nat} (h : inst.length = inst'.length) :
    (seedBytes version name steps inst).length = (seedBytes version name steps' inst').length := by
  simp only [seedBytes, List.length_append, length_label, h, length_bigEndian, length_keccak]

variable (F : Type) [BaseField F] (EF : Type) [Challenge F EF]

/-- FRI's domain separator has one length for every schedule of as many folds, whatever the
query indices' size. -/
theorem length_friSeed {arities arities' : List Nat} (h : arities.length = arities'.length)
    (finalLen commitBits queryBits numQueries indexBits indexBits' logBlowup maxLogArity : Nat) :
    (friSeed F EF arities finalLen commitBits queryBits numQueries indexBits logBlowup
        maxLogArity).length =
      (friSeed F EF arities' finalLen commitBits queryBits numQueries indexBits' logBlowup
        maxLogArity).length := by
  unfold friSeed
  exact length_toElems F (length_seedBytes_steps _ _ (by simp only [List.length_cons, h]))

end CompStark.DomainSeparator

/-! ### Stable messages of the batch -/

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fs CompStark.Fs CompStark.RandomOracle OracleSpec
open Interaction.Oracle.Security

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : ℕ} {offs : List ℕ}
  {capLen : ℕ} (S : Setup EF) {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
  (s : Digest F) (x : List F) {cap : Cap F}
  (hcap : ∀ d ∈ cap.toList, d ∈ boundDigests offs capLen x)

include hL hcap

/-- The trace message read under a bound cap is the same at the snapshot and on the log. -/
theorem traceMessageOf_snapshotAt :
    S.traceMessageOf (merkleCache (Bcs.snapshotAt L (s, x))) cap =
      S.traceMessageOf (merkleCache (Bcs.hashCacheOf L)) cap := by
  funext ijx
  simp only [traceMessageOf, matColumnCap_snapshotAt_of_bound hL s x hcap]

/-- The permutation message read under a bound cap is the same at the snapshot and on the log. -/
theorem permMessageOf_snapshotAt :
    S.permMessageOf (merkleCache (Bcs.snapshotAt L (s, x))) cap =
      S.permMessageOf (merkleCache (Bcs.hashCacheOf L)) cap := by
  funext icex
  simp only [permMessageOf, matColumnCap_snapshotAt_of_bound hL s x hcap]

/-- The quotient message read under a bound cap is the same at the snapshot and on the log. -/
theorem quotientMessageOf_snapshotAt :
    S.quotientMessageOf (merkleCache (Bcs.snapshotAt L (s, x))) cap =
      S.quotientMessageOf (merkleCache (Bcs.hashCacheOf L)) cap := by
  funext icex
  simp only [quotientMessageOf, matColumnCap_snapshotAt_of_bound hL s x hcap]

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Setup
open CompStark.Stark CompStark.Fs CompStark.Fs CompStark.RandomOracle OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ} (S : Setup EF)

omit [BaseField F] in
/-- A cap of the batch's trees has at most `2 ^ h` digests. -/
theorem length_capOf_le (h k : ℕ) (c : CapOf F h k) : c.toArray.toList.length ≤ 2 ^ h := by
  rw [Array.length_toList, Vector.size_toArray]
  exact Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)

/-- The permutation commitment opens alike at the snapshot of its block's input and on the log:
with lookups its cap, absorbed at an offset of `offs`, is bound; without lookups it has none. -/
theorem permCommit_open_snapshotAt {offs : List ℕ} {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs (2 ^ S.params.capHeight) L) (s : Digest F) :
    ∀ (b : Bool) (pc : (S.permCommit b).Com) (pre r : List F), (b = true → pre.length ∈ offs) →
      (S.permCommit b).open (Bcs.snapshotAt L (s, pre ++ (S.permCommit b).observe pc ++ r)) pc =
        (S.permCommit b).open (Bcs.hashCacheOf L) pc
  | true, pc, pre, r, hpre => by
    refine S.permMessageOf_snapshotAt hL s _ fun d hd => ?_
    have := mem_boundDigests_of_cap pre r _ (hpre rfl) (length_capOf_le _ _ pc) hd
    change d ∈ boundDigests offs _ (pre ++ ([] ++ capOfElems pc) ++ r)
    simpa only [capOfElems, capElems, List.nil_append] using this
  | false, _, _, _, _ => S.permMessageOf_snapshotAt hL s _ fun _ hd => absurd hd List.not_mem_nil

/-- With lookups, the lookup challenges squeeze. -/
theorem lookupSqueezes_true_ne_zero (hK : 0 < K) :
    lookupSqueezes (EF := EF) K true S.params.lookupPowBits ≠ 0 :=
  squeezesFor_ne_zero hK (by
    have : 0 < Challenge.d EF := (Challenge.params EF).d_pos
    simp only [pairSamples]
    omega)

/-- **The batch's commitments open alike at their blocks' snapshots**, on messages read off a
proof with every snapshot move the log's hash cache, without `HashBad`: the main cap after
`pending`, at an offset of `offs`, the permutation and quotient caps at their blocks' starts, and
FRI's. -/
theorem opensStable_parse (hK : 0 < K) {offs : List ℕ} {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs (2 ^ S.params.capHeight) L) (h0 : 0 ∈ offs)
    (hfri : (friSeedB S).length ∈ offs) (pending tail : List F) (hpend : pending.length ∈ offs)
    (proof : CompStark.Batch.BatchProof F EF) (msgs)
    (hp : S.parse K m (Bcs.hashCacheOf L) proof = some msgs) :
    OpensStable (Bcs.snapshotAt L) S.publicCoin (S.decoder K m) (S.layout K m) false
      (Bcs.hashCacheOf L) pending tail msgs := by
  unfold parse at hp
  obtain ⟨tc, -, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨pc, -, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨qc, -, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨fri, hfr, rfl⟩ := Option.map_eq_some_iff.mp hp
  refine opensStable_oracle_of _ _ _ _ _ _ _ _ (fun s r => ?_) ?_
  · change S.traceMessageOf (merkleCache (Bcs.snapshotAt L (s, pending ++ ([] ++ capOfElems tc) ++
      r))) tc.toArray = S.traceMessageOf (merkleCache (Bcs.hashCacheOf L)) tc.toArray
    refine S.traceMessageOf_snapshotAt hL s _ fun d hd => ?_
    have := mem_boundDigests_of_cap pending r _ hpend (length_capOf_le _ _ tc) hd
    simpa only [capOfElems, capElems, List.nil_append] using this
  have hno : lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0 →
      S.hasLookups = false := fun h => by
    cases hb : S.hasLookups
    · rfl
    · rw [hb] at h
      exact absurd h (S.lookupSqueezes_true_ne_zero hK)
  change ite _ _ _
  split
  all_goals
    refine opensStable_wrap_oracle _ _ _ _ _ _ _ _ _ _ ?_ fun _ => rfl
    refine opensStable_oracle_of _ _ _ _ _ _ _ _ (fun s r => ?_) ?_
    · refine S.permCommit_open_snapshotAt hL s S.hasLookups pc _ r ?_
      first
        | exact fun hb => absurd hb (by rw [hno ‹_›]; decide)
        | exact fun _ => h0
    change ite _ _ _
    split
    · exact absurd ‹_› (Iop.Setup.squeezesFor_extSamples_ne_zero hK 0)
    refine opensStable_wrap_oracle _ _ _ _ _ _ _ _ _ _ ?_ fun _ => rfl
    refine opensStable_oracle_of _ _ _ _ _ _ _ _ (fun s r => ?_) ?_
    · change S.quotientMessageOf (merkleCache (Bcs.snapshotAt L (s, [] ++ ([] ++ capOfElems qc) ++
        r))) qc.toArray = S.quotientMessageOf (merkleCache (Bcs.hashCacheOf L)) qc.toArray
      refine S.quotientMessageOf_snapshotAt hL s _ fun d hd => ?_
      have := mem_boundDigests_of_cap [] r _ h0 (length_capOf_le _ _ qc) hd
      simpa only [capOfElems, capElems, List.nil_append] using this
    change ite _ _ _
    split
    · exact absurd ‹_› (Iop.Setup.squeezesFor_extSamples_ne_zero hK _)
    refine opensStable_wrap_sender _ _ _ _ _ _ _ _ _ _ ?_ fun _ => rfl
    change ite _ _ _
    split
    · exact absurd ‹_› (Iop.Setup.squeezesFor_extSamples_ne_zero hK _)
    exact opensStable_parseFri _ _ hK hL h0 _ _ _ _ _ [] [] hfr
      (by simpa only [List.nil_append] using hfri)

/-- The permutation commitment is observed when the lookup challenges squeeze. -/
theorem permCommit_observe_ne_nil :
    ∀ (b : Bool) (pc : (S.permCommit b).Com),
      lookupSqueezes (EF := EF) K b S.params.lookupPowBits ≠ 0 → (S.permCommit b).observe pc ≠ []
  | true, pc, _ => List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil pc)
  | false, _, h => absurd rfl h

variable (K m) in
/-- Every challenge of the batch's layout that squeezes has observations since the last
squeeze. -/
theorem layout_fills (filled : Prop) :
    Layout.Fills S.publicCoin (S.decoder K m) (S.layout K m) filled := by
  have hpcs : pcsSeedB (F := F) S ≠ [] := by
    simp only [pcsSeedB, DomainSeparator.pcsSeed, DomainSeparator.toElems]
    exact List.cons_ne_nil _ _
  intro tc
  refine ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil tc))),
    fun _ pc τ ↦ ⟨fun _ _ ↦ ?_, fun _ qc ↦
      ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil qc))),
        fun _ _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_left_ne_nil hpcs _)),
          fun _ ↦ friLayout_fills K m _ _ S.params (Nat.two_pow_pos _) _ _ _⟩⟩⟩⟩
  by_cases h : lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0
  · refine Or.inl (Or.inl (Or.inl ?_))
    change if lookupSqueezes (EF := EF) K S.hasLookups S.params.lookupPowBits = 0 then _ else _
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (capOfElems_ne_nil tc)))
  · exact Or.inl (Or.inl (Or.inr (S.permCommit_observe_ne_nil _ pc h)))

/-- FRI's schedule on the batch folds by the batch's arities. -/
theorem scheduleArities_friSchedule :
    Iop.scheduleArities (S.domainSetup.friSchedule S.friHeights) = S.friArities := by
  rw [Iop.Setup.friSchedule, arities_plonky3_heights, Nat.add_comm S.params.logFinalPolyLen]
  rfl

/-- The batch folds at most `twoAdicity F` times. -/
theorem length_friArities_le : S.friArities.length ≤ twoAdicity F := by
  rw [← S.scheduleArities_friSchedule, length_scheduleArities]
  exact Iop.Setup.numFolds_friSchedule_le _ _

end CompStark.Iop.Batch.Setup

namespace CompStark.Iop.Batch.Statement
open CompStark.Stark CompStark.Fs CompStark.Fs OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF]

/-- FRI's domain separator for a schedule of `a` folds, of the length of every schedule of `a`
folds (`DomainSeparator.length_friSeed`). -/
def friSeedFolds (a : ℕ) : List F :=
  DomainSeparator.friSeed F EF (List.replicate a 0) (2 ^ C.params.logFinalPolyLen)
    C.params.commitPowBits C.params.queryPowBits C.params.numQueries 0 C.params.logBlowup
    C.params.maxLogArity

/-- The offsets at which the duplex inputs of Plonky3's batch verifier carry Merkle caps: the main
tree's after the batch's domain separator and the degree bits, FRI's first after FRI's domain
separator, of up to `twoAdicity F` folds, and every other at the block's start. -/
def capOffsets : List ℕ :=
  ((C.batchSeed EF).length + C.k * Challenge.d EF) :: 0 ::
    (List.range (twoAdicity F + 1)).map fun a ↦ (C.friSeedFolds EF a).length

theorem length_capOffsets : (C.capOffsets EF).length = twoAdicity F + 3 := by
  simp only [capOffsets, List.length_cons, List.length_map, List.length_range]

variable {C EF}

theorem zero_mem_capOffsets : 0 ∈ C.capOffsets EF :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- The batch's domain separator and the degree bits end at the first cap offset. -/
theorem length_seed_mem_capOffsets (n : C.Length) :
    ([] ++ (C.batchSeed EF ++ C.lengthElems EF n)).length ∈ C.capOffsets EF := by
  rw [List.nil_append, List.length_append, lengthElems, length_extsElems]
  exact List.mem_cons_self

/-- FRI's domain separator at admitted lengths ends at one of the cap offsets. -/
theorem length_friSeedB_mem_capOffsets (n : C.Length) :
    (friSeedB (C.setup EF n)).length ∈ C.capOffsets EF := by
  have hle := (C.setup EF n).length_friArities_le
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le hle), ?_⟩))
  exact DomainSeparator.length_friSeed F EF (List.length_replicate ..) _ _ _ _ _ _ _ _

variable {K : ℕ}

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
    (proof : CompStark.Batch.BatchProof F EF) (msgs)
    (hp : C.parse EF K (Bcs.hashCacheOf L) n proof = some msgs)
    (T : (merkleSpec F).QueryCache) (tail : List F) :
    OpensStable (Bcs.snapshotAt L) (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
      (C.layout EF K (C.coinCount EF K)) true T [] tail msgs := by
  unfold parse at hp
  obtain ⟨smsgs, hs, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact (C.setup EF n).opensStable_parse (m := C.coinCount EF K) hK hL zero_mem_capOffsets
    (length_friSeedB_mem_capOffsets n) _ tail (length_seed_mem_capOffsets n) proof smsgs hs

end CompStark.Iop.Batch.Statement
