import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.PackedKoalaBear
import CompStark.BabyBear.Poseidon2
import CompStark.Merkle.Packed
import CompStark.Merkle.Tree
import CompStark.Stark.Prover
import CompStark.KoalaBear.Fast
import CompStark.Mont32.Json
import CompStark.Batch.Prover
import CompStark.Stark.Fingerprint
import CompStarkFixtures.Keccak
import CompStarkFixtures.KeccakKernel
import CompStark.Keccak.Hash
import CompStarkFixtures.KeccakMerkle
import CompStark.Sumcheck.PackedFold
import CompStark.Sumcheck.WordProductProofs
import CompStarkFixtures.Pcs
import CompStark.Pcs.InductionDot
import CompStark.Pcs.SparseInduction
import CompStark.Pcs.CompactInduction
import CompStark.Pcs.ChallengeFold
import CompStark.Pcs.DirectSums

/-! # CompStark micro-benchmarks

`CompStarkBench poseidon2-spec LOG_N`: the width-16 specification on the Montgomery field, on
`2 ^ LOG_N` chained states; prints the median nanoseconds per permutation of seven runs.
`CompStarkBench babybear-perm LOG_N`: BabyBear's packed permutations of widths 16 and 24 on
`2 ^ LOG_N` states, and its width-16 specification on one state.
`CompStarkBench phases-lookup`: the wall time of every phase of a batch proof of
`lookupBatch 18 16`.
-/

open CompStark.Poseidon2
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write encodeFields)

def timeNs {α : Type} (f : Unit → IO α) : IO (Nat × α) := do
  let t0 ← IO.monoNanosNow
  let r ← f ()
  let t1 ← IO.monoNanosNow
  return (t1 - t0, r)

/-- Median nanoseconds of `samples` calls of `f` on inputs `0, 1, …`, after 200 ms of warmup:
idle cores take a few hundred milliseconds to reach full clock. -/
def timeMedian (samples : Nat) (f : Nat → UInt64) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut k := 0
  let mut sink : UInt64 := 0
  while (← IO.monoNanosNow) - t0 < 200000000 do
    sink := sink + f k
    k := k + 1
  let mut out := #[]
  for _ in [0:samples] do
    let t ← IO.monoNanosNow
    sink := sink + f k
    let t' ← IO.monoNanosNow
    out := out.push (t' - t)
    k := k + 1
  if sink == 12345 then IO.println ""
  return (out.qsort (· < ·))[samples / 2]!


/-- The Fibonacci trace of `n` rows from `(0, 1)` and its public values. -/
def fibInstance (n : Nat) : Array KoalaBear.Fast.Field × List KoalaBear.Fast.Field :=
  let (t, _, r) := (List.range n).foldl
    (fun ((t, l, r) : Array KoalaBear.Fast.Field × KoalaBear.Fast.Field × KoalaBear.Fast.Field) _ ↦
      (t.push l |>.push r, r, l + r)) (#[], 0, 1)
  (t, [0, 1, t.getD (2 * n - 1) r])

/-- The trace of `n` rows of `wide w` from `xⱼ = j`. -/
def wideTrace (w n : Nat) : Array KoalaBear.Fast.Field := Id.run do
  let mut out := Array.emptyWithCapacity (w * n)
  let mut row : Array KoalaBear.Fast.Field := Array.ofFn (n := w) fun j ↦ (j.val : _)
  for _ in [0:n] do
    out := out ++ row
    row := Array.ofFn (n := w) fun j ↦
      let x := row.getD j 0
      x * x * x + row.getD ((j.val + 1) % w) 0
  return out

/-- The Fibonacci numbers `F_0, …, F_n`. -/
def fibs (n : Nat) : Array KoalaBear.Fast.Field :=
  ((List.range n).foldl (fun ((a, b, out) : KoalaBear.Fast.Field × KoalaBear.Fast.Field ×
    Array KoalaBear.Fast.Field) _ ↦ (b, a + b, out.push b)) (0, 1, #[0])).2.2

/-- Plonky3's `mul_trace` of `batch-stark/tests/simple.rs`: `rows` rows of `mulAir reps`. -/
def mulTrace (rows reps : Nat) : Array KoalaBear.Fast.Field :=
  let w := 3 * reps + 1
  let f := fibs rows
  Array.ofFn (n := rows * w) fun k ↦
    let i := k.val / w
    let j := k.val % w
    if j + 1 = w then (if i + 1 = rows then 0 else f.getD (i + 1) 0)
    else if j % 3 = 0 then f.getD i 0
    else if j % 3 = 1 then f.getD (i + 1) 0
    else f.getD i 0 * f.getD (i + 1) 0

/-- The batch `lookup-bench` of `compstark-bench` at `lookupBatch 18 16`: `mulAirLookups 8` on
`2 ^ logN` rows with local lookups and sending on the bus `MulFib`, `fibonacciLookups` receiving
eight times on `2 ^ logN` rows, and `mulAirLookups 8` with local lookups on `2 ^ logSmall` rows;
with traces and public values. -/
def lookupBatch (logN logSmall : Nat) : List (CompStark.Batch.Instance KoalaBear.Fast.Field) ×
    List (Array KoalaBear.Fast.Field) × List (List KoalaBear.Fast.Field) :=
  let n := 2 ^ logN
  let f := fibs n
  ([.ofAir (CompStark.Stark.mulAirLookups 8 true (List.replicate 8 "MulFib")) logN,
      .ofAir (CompStark.Stark.fibonacciLookups logN "MulFib" 8) logN,
      .ofAir (CompStark.Stark.mulAirLookups 8 true []) logSmall],
    [mulTrace n 8, Array.ofFn (n := 2 * n) fun j ↦ f.getD (j.val / 2 + j.val % 2) 0,
      mulTrace (2 ^ logSmall) 8],
    [[], [0, 1, f.getD n 0], []])

open CompStark CompStark.Stark CompStark.Fri in
/-- `phases (quartic|quintic) LOG_N`: the wall time of each phase of the fast prover on `wide 64`,
`2 ^ LOG_N` rows, blowup 2, over KoalaBear's quartic or quintic extension. -/
def phases {EF : Type} [Challenge KoalaBear.Fast.Field EF] (logN : Nat)
    (B : Backend KoalaBear.Fast.Field EF 24) : IO UInt32 := do
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0, 0⟩
  let A := wide 64
  let trace := wideTrace 64 (2 ^ logN)
  let t ← IO.monoMsNow
  let lde := B.lde logN 1 gen 64 trace
  let t1 ← IO.monoMsNow
  IO.println s!"trace lde {t1 - t} ms"
  let tc := B.commit [lde]
  IO.println s!"trace commit {(← IO.monoMsNow) - t1} ms {((B.cap tc 0).getD 0 0)[0].val}"
  let t3 ← IO.monoMsNow
  let alpha : EF := Challenge.ofCoeffs [5, 7, 11, 13]
  let qs ← IO.lazyPure fun _ ↦ B.quotient A [] logN 1 lde none alpha
  let t4 ← IO.monoMsNow
  IO.println s!"quotient {t4 - t3} ms"
  let chunks := B.chunks 1 logN 1 qs
  let t5 ← IO.monoMsNow
  IO.println s!"quotient chunks lde {t5 - t4} ms {chunks.length}"
  let qc := B.commit chunks
  let t6 ← IO.monoMsNow
  IO.println s!"quotient commit {t6 - t5} ms {((B.cap qc 0).getD 0 0)[0].val}"
  let zeta : EF := Challenge.ofCoeffs [17, 19, 23, 29]
  let rounds : List (OpenRound B) :=
    [(tc, [(lde, [zeta, zeta * zeta])]), (qc, chunks.map fun m ↦ (m, [zeta]))]
  let t6 ← IO.monoMsNow
  let (opened, reduce) := B.openings 1 (rounds.map (·.2))
  let t7 ← IO.monoMsNow
  IO.println s!"opened values {t7 - t6} ms {opened.length}"
  let red := reduce alpha
  let t8 ← IO.monoMsNow
  IO.println s!"reduce {t8 - t7} ms {red.length}"
  let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (logN + 1)
    [logN + 1]
  let (cp, _) := (commitPhase B P arities (red.map (·.2))).run B.transcript
  let t9 ← IO.monoMsNow
  IO.println s!"commit phase {t9 - t8} ms {cp.commits.size}"
  let ((o, f), _) := (openPcs B P rounds).run B.transcript
  IO.println s!"openPcs {(← IO.monoMsNow) - t9} ms {o.length} {f.folds.size}"
  let t10 ← IO.monoMsNow
  let w := B.transcript.grinder B.transcript.state 16
  IO.println s!"grind 16 bits {(← IO.monoMsNow) - t10} ms, \
    witness {Montgomery.Native32.FastField.toNat w}"
  return 0

/-- Run `f` and print its wall time and a summary of its result. -/
def timed {α : Type} (label : String) (f : Unit → α) (summary : α → String) : IO α := do
  let t ← IO.monoMsNow
  let r ← IO.lazyPure f
  IO.println s!"{label} {(← IO.monoMsNow) - t} ms {summary r}"
  return r

open CompStark CompStark.Stark CompStark.Fri in
/-- The wall time of each phase of the fast batch prover on the benchmark's three `wide 64`
tables of `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows, blowup 2, 100 queries. -/
def phasesBatch : IO UInt32 := do
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0, 0⟩
  let logNs := [20, 19, 16]
  let instances : List (Batch.Instance KoalaBear.Fast.Field) :=
    logNs.map fun logN ↦ .ofAir (wide 64) logN
  let B := CompStark.KoalaBear.backendFor [] P.logBlowup (Batch.shapes instances)
  for k in [0:2] do
    let traces := logNs.map fun logN ↦ (wideTrace 64 (2 ^ logN)).set! 0 (k : _)
    let exts ← timed "trace lde" (fun _ ↦ (instances.zip traces).map fun (I, t) ↦
      B.lde I.logN 1 BaseField.gen 64 t) fun e ↦ s!"{(e.map (·.height)).sum}"
    let mainC ← timed "trace commit" (fun _ ↦ B.commit exts)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, k⟩
    let qs ← timed "quotient" (fun _ ↦ (instances.zip exts).map fun (I, e) ↦
      B.quotient I.air [] I.logN I.logQuotientChunks e none alpha) fun _ ↦ ""
    let chunks ← timed "quotient chunks lde" (fun _ ↦ (instances.zip qs).map fun (I, q) ↦
      B.chunks P.logBlowup I.logN I.logQuotientChunks q) fun c ↦ s!"{(c.map (·.length)).sum}"
    let quotC ← timed "quotient commit" (fun _ ↦ B.commit chunks.flatten)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let zeta : _root_.KoalaBear.Fast.Ext4 := ⟨17, 19, 23, k⟩
    let rounds : List (OpenRound B) :=
      [(mainC, (instances.zip exts).map fun (I, e) ↦
          (e, [zeta, zeta * Ext.ofBase (twoAdicGen I.logN)])),
        (quotC, chunks.flatten.map fun m ↦ (m, [zeta]))]
    let (opened, reduce) ← timed "opened values" (fun _ ↦ B.openings 1 (rounds.map (·.2)))
      fun o ↦ s!"{o.1.length}"
    let red ← timed "reduce" (fun _ ↦ reduce alpha) fun r ↦ s!"{r.length}"
    let heights := red.map fun (h, _) ↦ h
    let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (heights.headD 0)
      heights
    let _ ← timed "commit phase" (fun _ ↦ (commitPhase B P arities (red.map (·.2))).run
      B.transcript) fun cp ↦ s!"{cp.1.commits.size}"
    let _ ← timed "openPcs" (fun _ ↦ (openPcs B P rounds).run B.transcript)
      fun r ↦ s!"{r.1.2.folds.size}"
    let _ ← timed "whole proof" (fun _ ↦ Batch.proveBatchWith B P instances
      (traces.map fun t ↦ #[encodeFields t]) (logNs.map fun _ ↦ [])) fun pf ↦
        s!"{pf.oodWitness.val}"
  return 0

open CompStark CompStark.Stark CompStark.Fri CompStark.Batch in
/-- The wall time of each phase of the fast batch prover on `lookupBatch 18 16`, blowup 2, 100
queries, from fixed challenges: the phases of `batchCommitAndSample`, the openings and FRI
(`openPcs`), then a whole proof. -/
def phasesLookup : IO UInt32 := do
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0, 0⟩
  let (instances, traces, pis) := lookupBatch 18 16
  let B := CompStark.KoalaBear.backendFor [] P.logBlowup (Batch.shapes instances)
  for k in [0:2] do
    let words := traces.map fun t ↦ #[encodeFields (t.set! 0 (k : _))]
    let exts ← timed "trace lde" (fun _ ↦ (instances.zip words).map fun (I, t) ↦
      B.ldeTrace I.logN P.logBlowup BaseField.gen I.air.width t)
      fun e ↦ s!"{(e.map (·.height)).sum}"
    let mainC ← timed "trace commit" (fun _ ↦ B.commit exts)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let chs := Lookup.challengeLayout (instances.map (·.lookups))
      (⟨3, 1, 4, k⟩ : _root_.KoalaBear.Fast.Ext4) ⟨1, 5, 9, 2⟩
    let perms ← timed "permutation trace and lde"
      (fun _ ↦ permutationsWith B P instances words pis chs)
      fun ps ↦ s!"{(ps.filterMap id).length}"
    let (permExts, permC) ← timed "permutation commit"
      (fun _ ↦ commitPermutations B instances perms)
      fun c ↦ s!"{(c.2.map fun c ↦ ((B.cap c 0).getD 0 0)[0].val)}"
    let terminals := perms.map (·.map (·.2))
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, k⟩
    let qvs ← timed "quotient values" (fun _ ↦ ((instances.zip exts).zip ((permExts.zip pis).zip
      (chs.zip terminals))).map fun ((I, e), (r, p), c, t) ↦
        batchQuotientValues B I e none r p c (t.getD 0) alpha) fun q ↦ s!"{q.length}"
    let chunks ← timed "quotient chunks lde" (fun _ ↦ (instances.zip qvs).map fun (I, q) ↦
      B.chunks P.logBlowup I.logN I.logQuotientChunks q) fun c ↦ s!"{(c.map (·.length)).sum}"
    let quotC ← timed "quotient commit" (fun _ ↦ B.commit chunks.flatten)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let zeta : _root_.KoalaBear.Fast.Ext4 := ⟨17, 19, 23, k⟩
    let zetaNext (I : Instance _) := zeta * Ext.ofBase (twoAdicGen I.logN)
    let rounds : List (OpenRound B) :=
      [(mainC, (instances.zip exts).map fun (I, e) ↦ (e, [zeta, zetaNext I])),
        (quotC, chunks.flatten.map fun m ↦ (m, [zeta]))] ++
      (permC.map fun pc ↦ (pc, (instances.zip permExts).filterMap fun (I, r) ↦
        r.map fun e ↦ (e, [zeta, zetaNext I]))).toList
    let (opened, reduce) ← timed "opened values" (fun _ ↦ B.openings 1 (rounds.map (·.2)))
      fun o ↦ s!"{o.1.length}"
    let red ← timed "reduce" (fun _ ↦ reduce alpha) fun r ↦ s!"{r.length}"
    let heights := red.map fun (h, _) ↦ h
    let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (heights.headD 0)
      heights
    let _ ← timed "commit phase" (fun _ ↦ (commitPhase B P arities (red.map (·.2))).run
      B.transcript) fun cp ↦ s!"{cp.1.commits.size}"
    let _ ← timed "whole proof" (fun _ ↦ proveBatchWith B P instances words pis) fun pf ↦
        s!"{pf.oodWitness.val}"
  return 0

/-- `2 ^ logN` rows of `w` pseudorandom field elements (SplitMix64), in 16 row chunks of packed
words. -/
def randomTrace (w logN : Nat) : Array ByteArray :=
  let p := _root_.KoalaBear.fieldSize.toUInt64
  let words := 2 ^ logN / 16 * w
  let tasks := (Array.range 16).map fun k ↦ Task.spawn fun _ ↦ Id.run do
    let mut b := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords words
    for i in [0:words] do
      b := write b i ((CompStark.Stark.splitMix (k * words + i).toUInt64).2 % p).toUInt32
    return b
  tasks.map Task.get

/-- `2 ^ logN` rows of Plonky3's Keccak AIR's width of pseudorandom field elements. The prover's
work does not depend on the trace's values, so the Keccak AIR's proof phases are timed on it;
Clean's keccak-air showcase times whole proofs from the generated trace. -/
def keccakShapedTrace (logN : Nat) : Array ByteArray :=
  randomTrace CompStark.Fixtures.Keccak.width logN

open CompStark CompStark.Stark CompStark.Fri in
/-- `keccak-phases (quartic|quintic) LOG_N`: the wall time of each phase of a proof of Plonky3's
Keccak AIR on `keccakShapedTrace LOG_N` over KoalaBear's quartic or quintic extension, at
Plonky3's example configuration (blowup 2, arity up to 8, 87 queries, caps of height 3), twice. -/
def keccakPhases {EF : Type} [Challenge KoalaBear.Fast.Field EF] (logN : Nat)
    (B : Backend KoalaBear.Fast.Field EF 24) (trace : Array ByteArray → B.Trace) : IO UInt32 := do
  let A : Air KoalaBear.Fast.Field := CompStark.Fixtures.Keccak.air
  let w := CompStark.Fixtures.Keccak.width
  let P : Params := ⟨1, 0, 3, 87, 0, 16, 10, 0, 0, 3⟩
  let logChunks := A.logQuotientChunks logN
  let chunks := keccakShapedTrace logN
  for k in [0:2] do
    let lde ← timed "trace lde" (fun _ ↦ B.ldeTrace logN 1 gen w (trace (chunks.modify 0
      (write · 0 k.toUInt32)))) fun _ ↦ ""
    let tc ← timed "trace commit" (fun _ ↦ B.commit [lde])
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let alpha : EF := Challenge.ofCoeffs [5, 7, 11, (k : KoalaBear.Fast.Field)]
    let q ← timed "quotient" (fun _ ↦ B.quotient A [] logN logChunks lde none alpha)
      fun _ ↦ ""
    let qms ← timed "quotient chunks lde" (fun _ ↦ B.chunks P.logBlowup logN logChunks q)
      fun c ↦ s!"{c.length}"
    let qc ← timed "quotient commit" (fun _ ↦ B.commit qms)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let zeta : EF := Challenge.ofCoeffs [17, 19, 23, (k : KoalaBear.Fast.Field)]
    let rounds : List (OpenRound B) :=
      [(tc, [(lde, [zeta, zeta * Ext.ofBase (twoAdicGen logN)])]),
        (qc, qms.map fun m ↦ (m, [zeta]))]
    let (opened, reduce) ← timed "opened values" (fun _ ↦ B.openings 1 (rounds.map (·.2)))
      fun o ↦ s!"{o.1.length}"
    let red ← timed "reduce" (fun _ ↦ reduce alpha) fun r ↦ s!"{r.length}"
    let heights := red.map fun (h, _) ↦ h
    let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) (heights.headD 0)
      heights
    let _ ← timed "commit phase" (fun _ ↦ (commitPhase B P arities (red.map (·.2))).run
      B.transcript) fun cp ↦ s!"{cp.1.commits.size}"
    let _ ← timed "openPcs" (fun _ ↦ (openPcs B P rounds).run B.transcript)
      fun r ↦ s!"{r.1.2.folds.size}"
    let _ ← timed "whole proof" (fun _ ↦ proveWith B P A logN (trace chunks) []) fun pf ↦
      s!"{pf.oodWitness.val}"
  return 0

open CompStark CompStark.Stark CompStark.Fri in
/-- `quotient-phase AIR LOG_N REPS`: the fast prover's quotient phase on `2 ^ LOG_N` rows,
blowup 2, for `keccak` (Plonky3's Keccak AIR on `keccakShapedTrace`), `wide` (`wide 64`),
`widebus` (`wideBus 64`) or `lookup` (`mulAirLookups 8` with local lookups, sending on eight
buses): per round the AIR's quotient values and, with lookups, the permutation trace's extension
and the LogUp constraints' quotient values, from the trace's extension; then the medians of `REPS`
rounds. -/
def quotientPhase (air : String) (logN reps : Nat) : IO UInt32 := do
  let n := 2 ^ logN
  let (A, chunks) : Air KoalaBear.Fast.Field × Array ByteArray ← match air with
    | "keccak" => pure (CompStark.Fixtures.Keccak.air, keccakShapedTrace logN)
    | "wide" => pure (wide 64, #[encodeFields (wideTrace 64 n)])
    | "widebus" => pure (wideBus 64, #[encodeFields (wideTrace 64 n)])
    | "lookup" =>
      pure (mulAirLookups 8 true (List.replicate 8 "MulFib"), #[encodeFields (mulTrace n 8)])
    | _ => IO.eprintln "AIR: keccak, wide, widebus or lookup"; return 1
  let I : Batch.Instance KoalaBear.Fast.Field := .ofAir A logN
  let B := CompStark.KoalaBear.backendFor [CompStark.Fixtures.KeccakKernel.kernel] 1
    [(logN, I.logQuotientChunks)]
  let ext := B.ldeTrace logN 1 gen A.width chunks
  let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, 13⟩
  let chs := (Lookup.challengeLayout [I.lookups] (⟨3, 1, 4, 1⟩ : _root_.KoalaBear.Fast.Ext4)
    ⟨5, 9, 2, 6⟩).headD []
  let labels := #["quotient", "permutation", "lookup quotient"]
  let mut samples : Array (Array Nat) := labels.map fun _ ↦ #[]
  for k in [0:reps] do
    let alpha := alpha + Ext.ofBase (k : KoalaBear.Fast.Field)
    let (t0, q) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦
      B.quotient A [] logN I.logQuotientChunks ext none alpha
    let (t1, pm) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦
      if I.lookups.isEmpty then none else some (B.permutation 1 A I.lookups logN chunks [] chs)
    let (t2, lq) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ match pm with
      | none => B.ofArray #[]
      | some (perm, t) => B.lookupQuotient A (A.lookupConstraints logN) [] logN
          I.logQuotientChunks ext none perm chs t alpha
    IO.println s!"quotient {t0 / 1000000} ms permutation {t1 / 1000000} ms \
      lookup quotient {t2 / 1000000} ms {((B.toArray q).getD 5 0 + (B.toArray lq).getD 5 0).c0.val}"
    samples := (samples.zip #[t0, t1, t2]).map fun (s, t) ↦ s.push t
  for (l, s) in labels.zip samples do
    let m := (s.qsort (· < ·))[s.size / 2]!
    IO.println s!"lean {air} 2^{logN} {l} median {m / 1000000} ms"
  return 0


/-- The median time of three proofs by `B` of `A` on the traces `trace 0, trace 1, trace 2`,
checked against the proof `rust?` on the first if given. -/
def proveTimed {EF : Type} [CompStark.Challenge KoalaBear.Fast.Field EF] (label : String)
    (B : CompStark.Fri.Backend KoalaBear.Fast.Field EF 24)
    (P : CompStark.Fri.Params) (A : CompStark.Stark.Air KoalaBear.Fast.Field) (logN : Nat)
    (trace : Nat → B.Trace) (pis : List KoalaBear.Fast.Field)
    (rust? : Option (CompStark.Stark.Proof KoalaBear.Fast.Field EF)) :
    IO UInt32 := do
  if let some rust := rust? then
    unless CompStark.Stark.proveWith B P A logN (trace 0) pis == rust do
      IO.eprintln "proof differs from Plonky3's"; return 1
    IO.println "proof matches Plonky3's"
  let mut samples := #[]
  for k in [0:3] do
    let t ← IO.lazyPure fun _ ↦ trace k
    let (ns, pf) ← timeNs fun _ ↦ do return CompStark.Stark.proveWith B P A logN t pis
    samples := samples.push ns
    if pf.degreeBits == 12345 then IO.println ""
  let m := (samples.qsort (· < ·))[1]!
  IO.println s!"lean {label} ms median {m / 1000000}.{m / 1000 % 1000}"
  return 0


open CompStark CompStark.Stark CompStark.Fri in
/-- `openings-phase (wide|keccak) LOG_N REPS`: the fast prover's openings, blowup 2, on the
extension of `wideTrace 64` or `keccakShapedTrace LOG_N` with its two quotient chunks of the
extension's height: per round the values of the trace at `ζ` and `ζ ω` and of the chunks at `ζ`,
and the batched reduction; then the medians of `REPS` rounds. -/
def openingsPhase (air : String) (logN reps : Nat) : IO UInt32 := do
  let (A, chunks) : Air KoalaBear.Fast.Field × Array ByteArray :=
    if air == "keccak" then (CompStark.Fixtures.Keccak.air, keccakShapedTrace logN)
    else (wide 64, #[encodeFields (wideTrace 64 (2 ^ logN))])
  let B := CompStark.KoalaBear.backendFor [] 1 [(logN, A.logQuotientChunks logN)]
  let ext ← IO.lazyPure fun _ ↦ B.ldeTrace logN 1 gen A.width chunks
  let quot ← IO.lazyPure fun _ ↦ (List.range 2).map fun c ↦
    B.lde logN 1 gen 4 ((wideTrace 4 (2 ^ logN)).set! 0 (c : KoalaBear.Fast.Field))
  IO.println s!"extensions of {ext.height} and {(quot.map (·.height)).sum} rows"
  let labels := #["opened values", "reduce"]
  let mut samples : Array (Array Nat) := labels.map fun _ ↦ #[]
  for k in [0:reps] do
    let zeta : _root_.KoalaBear.Fast.Ext4 := ⟨17, 19, 23, (k : KoalaBear.Fast.Field)⟩
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, (k : KoalaBear.Fast.Field)⟩
    let rounds := [[(ext, [zeta, zeta * Ext.ofBase (twoAdicGen logN)])],
      quot.map fun m ↦ (m, [zeta])]
    let (t0, op) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ B.openings 1 rounds
    let (t1, red) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ op.2 alpha
    IO.println s!"opened values {t0 / 1000000} ms reduce {t1 / 1000000} ms {red.length}"
    samples := (samples.zip #[t0, t1]).map fun (s, t) ↦ s.push t
  for (l, s) in labels.zip samples do
    let m := (s.qsort (· < ·))[s.size / 2]!
    IO.println s!"lean {air} 2^{logN} {l} median {m / 1000000} ms"
  return 0

/-- Plonky3's example configuration: blowup 2, arity up to 8, 87 queries, caps of height 3. -/
def keccakParams : CompStark.Fri.Params := ⟨1, 0, 3, 87, 0, 16, 10, 0, 0, 3⟩

/-- The Keccak AIR's shape on `2 ^ logN` rows. -/
def keccakShapes (logN : Nat) : List (Nat × Nat) :=
  [(logN, (CompStark.Fixtures.Keccak.air : CompStark.Stark.Air
      KoalaBear.Fast.Field).logQuotientChunks
    logN)]

open CompStark CompStark.Stark CompStark.Fri in
/-- `keccak-prove EXT LOG_N`: the median time of three proofs of Plonky3's Keccak AIR on
`keccakShapedTrace LOG_N` over KoalaBear's `quartic` or `quintic` extension (`fast`), at Plonky3's
example configuration (blowup 2, arity up to 8, 87 queries, caps of height 3), with the AIR's
generated quotient kernel (`compstark-bench keccak-prove-bench EXT LOG_N`). -/
def keccakProve {EF : Type} [Challenge KoalaBear.Fast.Field EF] (ext : String) (logN : Nat)
    (B : Backend KoalaBear.Fast.Field EF 24) (trace : Array ByteArray → B.Trace) : IO UInt32 := do
  let chunks := keccakShapedTrace logN
  proveTimed s!"fast prove keccak {ext} 2^{logN}" B keccakParams CompStark.Fixtures.Keccak.air logN
    (fun k ↦ trace (chunks.modify 0 (write · 0 k.toUInt32))) [] none

/-- The phase marks of a `gate` run, written to `scripts/perf-gate`'s control FIFO, each
acknowledged on its acknowledgement FIFO before the run goes on, so that the counters it reads at
a mark are the run's exactly at that point. -/
structure Marks where
  ctl : IO.FS.Handle
  ack : IO.FS.Handle

/-- The marks through the FIFOs `ctl` and `ack` of the directory `dir`. -/
def Marks.open (dir : System.FilePath) : IO Marks := do
  let ctl ← IO.FS.Handle.mk (dir / "ctl") .write
  let ack ← IO.FS.Handle.mk (dir / "ack") .read
  return ⟨ctl, ack⟩

def Marks.send (m : Marks) (msg : String) : IO Unit := do
  m.ctl.putStrLn msg
  m.ctl.flush
  let _ ← m.ack.getLine

/-- Compute `f ()` between the marks `begin` and `end label`. -/
def Marks.phase {α : Type} (m : Marks) (label : String) (f : Unit → α) : IO α := do
  m.send "begin"
  let r ← IO.lazyPure f
  m.send s!"end {label}"
  return r

open CompStark CompStark.Stark CompStark.Fri in
/-- The phases of a proof of the AIR instances `items` (an AIR, its rows' `logN` and its trace)
by the backend `B`, each between marks: the traces' extension and commitment, the quotients, the
extension and commitment of their chunks, the opened values at `zeta` and `zeta ω` with the
inverse denominators of both, the batched reduction by `alpha`, FRI's commit phase, the query grinding and the query openings at
pseudorandom indices. -/
def gatePhases {EF : Type} [Challenge KoalaBear.Fast.Field EF] (m : Marks)
    (B : Backend KoalaBear.Fast.Field EF 24) (P : Params)
    (items : List (Air KoalaBear.Fast.Field × Nat × B.Trace)) (alpha zeta : EF) : IO Unit := do
  let exts ← m.phase "trace lde" fun _ ↦ items.map fun (A, logN, t) ↦
    B.ldeTrace logN P.logBlowup gen A.width t
  let tc ← m.phase "trace commit" fun _ ↦ B.commit exts
  let qs ← m.phase "quotient" fun _ ↦ (items.zip exts).map fun ((A, logN, _), e) ↦
    B.quotient A [] logN (A.logQuotientChunks logN) e none alpha
  let chunks ← m.phase "quotient lde" fun _ ↦ (items.zip qs).map fun ((A, logN, _), q) ↦
    B.chunks P.logBlowup logN (A.logQuotientChunks logN) q
  let qc ← m.phase "quotient commit" fun _ ↦ B.commit chunks.flatten
  let rounds : List (OpenRound B) :=
    [(tc, (items.zip exts).map fun ((_, logN, _), e) ↦
        (e, [zeta, zeta * Ext.ofBase (twoAdicGen logN)])),
      (qc, chunks.flatten.map fun c ↦ (c, [zeta]))]
  let (_, reduce) ← m.phase "opened values" fun _ ↦ B.openings P.logBlowup (rounds.map (·.2))
  let red ← m.phase "reduce" fun _ ↦ reduce alpha
  let heights := red.map (·.1)
  let logMax := heights.headD 0
  let arities := foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax heights
  let cp ← m.phase "commit phase" fun _ ↦
    ((commitPhase B P arities (red.map (·.2))).run B.transcript).1
  let w ← m.phase "grind" fun _ ↦ B.transcript.grinder B.transcript.state P.queryPowBits
  let indices := (List.range P.numQueries).map fun i ↦
    ((splitMix i.toUInt64).2 % (2 ^ logMax).toUInt64).toNat
  let (ins, folds) ← m.phase "query openings" fun _ ↦
    (rounds.map fun (c, _) ↦ openMulti B P.capHeight c (indices.map (· >>> (logMax - B.logHeight c))),
      answerFolds B P.capHeight cp.data cp.arities.toList indices)
  IO.println s!"phases: {cp.commits.size} commits, witness \
    {Montgomery.Native32.FastField.toNat w}, {ins.length} rounds, {folds.length} folds"

/-- `wide 64` on `2 ^ logN` rows with blowup 2, 100 queries and 16 bits of query grinding. -/
def wideParams : CompStark.Fri.Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0, 0⟩

/-- Dependent permutation chain, with the survey's nonzero initial lane. -/
@[noinline] def keccakChain (n : Nat) (s : Array UInt64) : Array UInt64 :=
  match n with
  | 0 => s
  | n + 1 => keccakChain n (CompStark.Keccak.f1600 s)

/-- Serial hash loop consuming a complete output lane from every digest. -/
@[noinline] def keccakHashes (n : Nat) (input : ByteArray) (hu : input.size < USize.size) (sink : UInt64) : UInt64 :=
  match n with
  | 0 => sink
  | n + 1 =>
    let h := CompStark.Keccak.keccak256 input hu
    keccakHashes n input hu (sink + CompStark.Keccak.readLane h 0)

/-- Independent states with different nonzero lane values. -/
def keccakStates : Array (Array UInt64) :=
  Array.ofFn (n := 1024) fun j ↦ Array.ofFn (n := 25) fun i ↦
    (j.val * 25 + i.val + 1).toUInt64 * 0x9e3779b97f4a7c15

/-- Independent messages in the survey's contiguous, repeating byte pattern. -/
def keccakInputs (len : Nat) : Array ByteArray :=
  Array.ofFn (n := 1024) fun j ↦ ByteArray.mk (Array.ofFn (n := len) fun i ↦
    (j.val * len + i.val).toUInt8)

theorem keccakInputs_addressable (len : Nat) (hlen : len < 4294967296) :
    ∀ input ∈ keccakInputs len, input.size < USize.size := by
  intro input hi
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hi
  simp only [ByteArray.size, Array.size_ofFn]
  exact lt_of_lt_of_le hlen USize.le_size

/-- Independent permutation throughput, carrying all outputs into the next batch. -/
@[noinline] def keccakStateBatches (n : Nat) (states : Array (Array UInt64)) :
    Array (Array UInt64) :=
  match n with
  | 0 => states
  | n + 1 => keccakStateBatches n (CompStark.Keccak.f1600Batch states)

/-- Consume every digest of every independent hash batch. -/
@[noinline] def keccakHashBatches (n : Nat) (inputs : Array ByteArray)
    (hu : ∀ input ∈ inputs, input.size < USize.size) (sink : UInt64) : UInt64 :=
  match n with
  | 0 => sink
  | n + 1 =>
    let hashes := CompStark.Keccak.keccak256Batch inputs hu
    let sink := hashes.foldl (fun s h ↦ s + CompStark.Keccak.readLane h 0) sink
    keccakHashBatches n inputs hu sink

/-- Keccak kernel timings. Input-dependent sinks prevent loop-invariant hash elimination. -/
def keccakKernels (n : Nat) : IO UInt32 := do
  if n = 0 then
    IO.eprintln "positive operation count required"; return 1
  let seed := (Array.replicate 25 (0 : UInt64)).set! 0 0x123456789abcdef0
  let (ns, s) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ keccakChain n seed
  IO.println s!"f1600 n={n} ns/op={ns / n} sink={s[0]!}"
  for len in ([⟨64, by decide⟩, ⟨512, by decide⟩] : List (Fin 10000)) do
    let input := ByteArray.mk (Array.ofFn (n := len.val) fun i ↦ i.val.toUInt8)
    have hu : input.size < USize.size := by
      simp only [input, ByteArray.size, Array.size_ofFn]
      exact lt_of_lt_of_le (by omega) USize.le_size
    let (ns, sink) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ keccakHashes n input hu 0
    IO.println s!"keccak256 len={len} n={n} ns/op={ns / n} sink={sink}"
  let rounds := (n + 1023) / 1024
  let count := rounds * 1024
  let (ns, states) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ keccakStateBatches rounds keccakStates
  let sink := states.foldl (fun s state ↦ s + state[0]!) (0 : UInt64)
  IO.println s!"f1600 batch n={count} ns/op={ns / count} sink={sink}"
  for len in ([⟨64, by decide⟩, ⟨512, by decide⟩] : List (Fin 10000)) do
    let inputs := keccakInputs len.val
    let (ns, sink) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ keccakHashBatches rounds inputs
      (keccakInputs_addressable len.val (by omega)) 0
    IO.println s!"keccak256 batch len={len} n={count} ns/op={ns / count} sink={sink}"
  return 0

open CompStark CompStark.Stark CompStark.Fri in
/-- A proof of `A` on `2 ^ logN` rows by `B`, between marks, and its verification by `verify`,
between marks, which must end in `expected`. -/
def gateProveVerify {EF : Type} [Challenge KoalaBear.Fast.Field EF] (m : Marks)
    (B : Backend KoalaBear.Fast.Field EF 24) (P : Params) (A : Air KoalaBear.Fast.Field)
    (logN : Nat) (trace : B.Trace)
    (verify : Proof KoalaBear.Fast.Field EF → Except String Unit)
    (expected : Except String Unit) : IO UInt32 := do
  let pf ← m.phase "prove" fun _ ↦ proveWith B P A logN trace []
  let r ← m.phase "verify" fun _ ↦ verify pf
  unless r == expected do
    IO.eprintln s!"verifier: {repr r}, expected {repr expected}"; return 1
  IO.println s!"prove: witness {pf.oodWitness.val}, verify: {repr r}"
  return 0

/-- Shared-challenge E-table folds, checked against the independent scalar word kernel. -/
def sumcheckFoldRun (phase : {α : Type} → String → (Unit → α) → IO α) : IO UInt32 := do
  let rows := 16384
  let width := 4
  let value := fun i : Nat => (⟨⟨UInt64.ofNat (31 * i + 0x123456789abcdef0)⟩,
    ⟨UInt64.ofNat (i * i + 0xfedcba9876543210)⟩,
    ⟨UInt64.ofNat (17 * i + 0x8000000000000001)⟩⟩ : BF64.WordExt3)
  let input := Vector.ofFn fun i : Fin (2 * rows * width) => value i.val
  let products ← phase "products" fun _ => Array.ofFn fun i : Fin (rows * width) =>
    CompStark.Sumcheck.extMulFive input[2 * i.val]! input[2 * i.val + 1]!
  for i in [:products.size] do
    unless products[i]! == BF64.WordExt3.mul input[2 * i]! input[2 * i + 1]! do
      throw (IO.userError s!"five-product multiplication mismatch at {i}")
  let r := value 19
  let plan ← phase "prepare" fun _ => CompStark.Sumcheck.prepare r
  let output ← phase "fold" fun _ => CompStark.Sumcheck.fold plan rows width input
  have hn : 8 * (2 * rows * width) < USize.size := lt_of_lt_of_le (by decide) USize.le_size
  let packed := CompStark.Sumcheck.fillScalars (2 * rows * width) hn fun i hi => input.uget i hi
  let packedOutput ← phase "packed-fold" fun _ =>
    CompStark.Sumcheck.foldPacked plan rows width (2 * rows * width) packed hn (by rfl)
  let unpacked := packedOutput.toArray (lt_of_lt_of_le (by decide) USize.le_size)
  unless unpacked == output.toArray do
    throw (IO.userError "packed sumcheck fold disagrees with scalar array fold")
  for i in [:rows * width] do
    let a := input[2 * (i / width) * width + i % width]!
    let b := input[(2 * (i / width) + 1) * width + i % width]!
    let expected := BF64.WordExt3.add a (BF64.WordExt3.mul r (BF64.WordExt3.add a b))
    unless output[i]!.toField == expected.toField do
      throw (IO.userError s!"sumcheck fold mismatch at {i}")
  let baseInput := Vector.ofFn fun i : Fin (2 * rows * width) =>
    (⟨(value i.val).c0, ⟨0⟩, ⟨0⟩⟩ : BF64.WordExt3)
  let baseOutput ← phase "base-fold" fun _ => CompStark.Sumcheck.fold plan rows width baseInput
  let basePacked := CompStark.Sumcheck.fillScalars (2 * rows * width) hn fun i hi => baseInput.uget i hi
  let basePackedOutput ← phase "packed-base-fold" fun _ =>
    CompStark.Sumcheck.foldPacked plan rows width (2 * rows * width) basePacked hn (by rfl)
  unless basePackedOutput.toArray (lt_of_lt_of_le (by decide) USize.le_size) == baseOutput.toArray do
    throw (IO.userError "packed base fold disagrees with scalar fold")
  for i in [:rows * width] do
    let a := baseInput[2 * (i / width) * width + i % width]!
    let b := baseInput[(2 * (i / width) + 1) * width + i % width]!
    let expected := BF64.WordExt3.add a (BF64.WordExt3.mul r (BF64.WordExt3.add a b))
    unless baseOutput[i]! == expected do
      throw (IO.userError s!"base sumcheck fold mismatch at {i}")
  let constantInput := Vector.ofFn fun i : Fin (2 * rows * width) =>
    value ((i.val / (2 * width)) * width + i.val % width)
  let constantOutput ← phase "constant-fold" fun _ => CompStark.Sumcheck.fold plan rows width constantInput
  let constantPacked := CompStark.Sumcheck.fillScalars (2 * rows * width) hn fun i hi => constantInput.uget i hi
  let constantPackedOutput ← phase "packed-constant-fold" fun _ =>
    CompStark.Sumcheck.foldPacked plan rows width (2 * rows * width) constantPacked hn (by rfl)
  unless constantPackedOutput.toArray (lt_of_lt_of_le (by decide) USize.le_size) == constantOutput.toArray do
    throw (IO.userError "packed constant fold disagrees with scalar fold")
  for i in [:rows * width] do
    unless constantOutput[i]! == value i do
      throw (IO.userError s!"constant fold mismatch at {i}")
  IO.println s!"fold rows={rows} width={width} sink={output[rows * width - 1]!.c0.val}"
  return 0

/-- Binary-field PCS map preparation, packed bit folds and factored opening weights. -/
def pcsRun (phase : {α : Type} → String → (Unit → α) → IO α) : IO UInt32 := do
  let challenges := CompStark.Fixtures.Pcs.challenges
  let coordinates ← phase "coordinates" fun _ => CompStark.Pcs.coordinateWeights challenges
  unless coordinates[191]!.c0.val == 5242164331567799370 do
    throw (IO.userError "ring coordinate weights disagree with Rust")
  let point : Fin (4 + 4) → BF64.Ext3 := fun i =>
    (CompStark.Fixtures.Pcs.value (i.val + 101)).toField
  let factors := CompStark.Pcs.wordFactoredEq (lo := 4) (hi := 4) point
  let tensor : Vector BF64.WordExt3 256 := Vector.ofFn fun i => factors.eval (CompStark.Pcs.vertex 8 i)
  let packed : Vector BF64.Word 256 := Vector.ofFn fun i =>
    ⟨UInt64.ofNat (0x9e3779b97f4a7c15 * (i.val + 1))⟩
  let slices ← phase "bit-fold" fun _ => CompStark.Pcs.foldBits packed tensor
  let mapped ← phase "basis" fun _ => tensor.map (CompStark.Pcs.applyCoordinates coordinates)
  let input := CompStark.Fixtures.Pcs.encodingInput 6 16
  let plan : AdditiveNTT.Bitsliced.Plan AdditiveNTT.Packed.flatBasis 8 (by decide) ← phase "encoding-plan" fun _ =>
    AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis 8 (by decide)
  let encoded ← phase "encoding" fun _ =>
    CompStark.Pcs.encodeExtensionRows (ell := 6) (rate := 2) (by decide) plan 16
      (by decide) input (by decide)
  let positions : Vector (Fin 256) 7 := ⟨#[3, 17, 3, 255, 128, 0, 64], rfl⟩
  let induced ← phase "induction" fun _ =>
    CompStark.Pcs.induceRows (ell := 6) (rate := 2) (by decide) plan.toPacked 3 positions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val + 77)) c
  let dense ← phase "induction-dense" fun _ =>
    CompStark.Pcs.induceDenseRows (ell := 6) (rate := 2) (by decide) plan.toPacked 3 positions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val + 77)) c
  let split ← phase "induction-split" fun _ =>
    CompStark.Pcs.induceSplitRows 3 3 2 (by decide) 3 positions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val + 77)) c
  let sparse ← phase "induction-sparse" fun _ =>
    CompStark.Pcs.induceOccupiedRows (ell := 6) (rate := 2) (by decide) plan.toPacked 3 positions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val + 77)) c
  let expectedInduced ← IO.FS.readBinFile "tests/data/pcs/induced.bin"
  unless induced.val.bytes == expectedInduced && dense.val.bytes == expectedInduced &&
      split.val.bytes == expectedInduced && sparse.val.bytes == expectedInduced do throw (IO.userError "induced weights Rust mismatch")
  let largePositions : Vector (Fin 16384) 137 := Vector.ofFn fun q =>
    ⟨(if q.val%7 = 0 then 0 else q.val*7919+91) % 16384, Nat.mod_lt _ (by decide)⟩
  let largePlan ← phase "induction-scalar-plan" fun _ =>
    (AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis 14 (by decide)).toPacked
  let largeDense ← phase "induction-large-dense" fun _ =>
    CompStark.Pcs.induceSplitRows 6 6 2 (by decide) 3 largePositions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val+77)) c
  let largeSparse ← phase "induction-large-sparse" fun _ =>
    CompStark.Pcs.induceOccupiedRows (ell := 12) (rate := 2) (by decide) largePlan 3 largePositions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val+77)) c
  let preparedPlan ← phase "induction-plan" fun _ => CompStark.Pcs.sparseInductionPlan 14 (by decide)
  let largePrepared ← phase "induction-large-prepared" fun _ =>
    CompStark.Pcs.induceOccupiedRows (ell := 12) (rate := 2) (by decide) preparedPlan 3 largePositions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val+77)) c
  let largeCompact ← phase "induction-large-compact" fun _ =>
    CompStark.Pcs.induceOccupiedCompactRows (ell := 12) (rate := 2) (by decide) 3 largePositions fun q c =>
      CompStark.Pcs.mapLimb (CompStark.Fixtures.Pcs.value (q.val+77)) c
  let expectedLarge ← IO.FS.readBinFile "tests/data/pcs/induced-large.bin"
  unless largeCompact.val.bytes == expectedLarge && largeDense.val.bytes == expectedLarge && largeSparse.val.bytes == expectedLarge && largePrepared.val.bytes == expectedLarge do
    throw (IO.userError "large induced weights Rust mismatch")
  for rows in [16, 256, 1024] do
    let input : Vector BF64.WordExt3 (2*rows*1) := Vector.ofFn fun i =>
      CompStark.Fixtures.Pcs.value (i.val+71)
    let weight : Vector BF64.WordExt3 (2*rows*1) := Vector.ofFn fun i =>
      CompStark.Fixtures.Pcs.value (i.val+173)
    let r := CompStark.Fixtures.Pcs.value 43
    let folded ← phase s!"challenge-fold-{rows}" fun _ =>
      CompStark.Pcs.foldPairChallenge r rows 1 input weight
    let direct ← phase s!"challenge-scalar-{rows}" fun _ =>
      (CompStark.Pcs.foldScalar r rows 1 input, CompStark.Pcs.foldScalar r rows 1 weight)
    let reference ← phase s!"challenge-prepared-{rows}" fun _ =>
      let shared := CompStark.Sumcheck.prepare r
      (CompStark.Sumcheck.fold shared rows 1 input, CompStark.Sumcheck.fold shared rows 1 weight)
    unless folded == reference && direct == reference do
      throw (IO.userError s!"challenge fold mismatch: {rows}")
  let acc : Vector BF64.WordExt3 256 := Vector.ofFn fun i => CompStark.Fixtures.Pcs.value (i.val + 100)
  let incoming : Vector BF64.WordExt3 256 := Vector.ofFn fun i => CompStark.Fixtures.Pcs.value (i.val + 200)
  let shared ← phase "accumulated-prepare" fun _ => CompStark.Sumcheck.prepare (CompStark.Fixtures.Pcs.value 43)
  let accumulated ← phase "accumulated" fun _ => CompStark.Pcs.addScaled shared acc incoming
  let expectedAccumulated ← IO.FS.readBinFile "tests/data/pcs/accumulated.bin"
  unless CompStark.Fixtures.Pcs.bytes accumulated.toArray == expectedAccumulated do
    throw (IO.userError "accumulated weights Rust mismatch")
  let round ← phase "whir-round" fun _ => CompStark.Pcs.roundCoefficients 128 1 accumulated incoming
  let expectedRound ← IO.FS.readBinFile "tests/data/pcs/round.bin"
  unless CompStark.Fixtures.Pcs.bytes round.toArray == expectedRound do
    throw (IO.userError "native WHIR round mismatch")
  let projected ← phase "basis-project" fun _ => CompStark.Fixtures.Pcs.basisMatrices (coordinates.size-192)
  for (name, values) in [("projection", projected.1.toArray), ("lane-factors", projected.2.toArray)] do
    let expected ← IO.FS.readBinFile s!"tests/data/pcs/{name}.bin"
    unless CompStark.Fixtures.Pcs.bytes values == expected do
      throw (IO.userError s!"projected Basis Rust mismatch: {name}")
  let columns := CompStark.Fixtures.Pcs.projectionColumns (coordinates.size-192)
  let witness := CompStark.Fixtures.Pcs.projectionWitness (coordinates.size-192)
  let projected ← phase "basis-columns" fun _ => CompStark.Pcs.projectColumns 8 1024 200 witness columns
  unless projected == CompStark.Pcs.projectBasis 8 1024 200 witness
      (columns.map CompStark.Pcs.BasisColumn.expand) do
    throw (IO.userError "shared Basis column matrix mismatch")
  let liftValues := Vector.ofFn fun i : Fin 4096 => CompStark.Fixtures.Pcs.value (i.val+31)
  let liftPoints : Vector (CompStark.Pcs.BasisWindow 4096) 8 := Vector.ofFn fun _ =>
    ⟨0, 4096, liftValues, by decide⟩
  let liftWeights := Vector.ofFn fun i : Fin 200 => CompStark.Fixtures.Pcs.value (i.val+601)
  let lifted ← phase "basis-lift" fun _ => CompStark.Pcs.liftPointBinary 4096 8 liftPoints liftValues liftWeights
  let referenceLift ← phase "basis-lift-reference" fun _ => CompStark.Pcs.liftColumns 4096 200 liftWeights
    (liftPoints.map CompStark.Pcs.BasisColumn.point ++
      Vector.ofFn (fun bit : Fin 192 => CompStark.Pcs.BasisColumn.binary liftValues bit))
  unless lifted == referenceLift do
    throw (IO.userError "byte-prepared Basis reconstruction mismatch")
  let expected ← IO.FS.readBinFile "tests/data/pcs/encoded.bin"
  unless encoded.val.bytes == expected do throw (IO.userError "bitsliced E encoding Rust mismatch")
  for (name, actual) in [("coordinates", coordinates.toArray), ("tensor", tensor.toArray),
      ("slices", slices.toArray), ("mapped", mapped.toArray)] do
    let expected ← IO.FS.readBinFile s!"tests/data/pcs/{name}.bin"
    unless CompStark.Fixtures.Pcs.bytes actual == expected do
      throw (IO.userError s!"PCS byte mismatch: {name}")
  IO.println s!"PCS coordinates={coordinates.size} sink={coordinates[191]!.c0.val} slices={slices[63]!.c0.val}"
  return 0

/-- Commitment, canonical opening, retained writer transport and deterministic grinding. -/
def keccakMerkleRun (phase : {α : Type} → String → (Unit → α) → IO α) : IO UInt32 := do
  let input := CompStark.Fixtures.KeccakMerkle.rows 4096 64 (by decide)
  let tree ← IO.ofExcept (← phase "commit" fun _ ↦ CompStark.Keccak.Merkle.commit input)
  unless tree.2.root.val.data == #[246, 17, 103, 241, 171, 70, 74, 202, 75, 217, 117,
      91, 169, 255, 12, 45, 103, 72, 209, 98, 119, 43, 201, 23, 37, 220, 29, 144,
      241, 233, 48, 207] do
    throw (IO.userError "Keccak Merkle root differs from Rust")
  let opening ← IO.ofExcept (← phase "open" fun _ ↦
    tree.2.open CompStark.Fixtures.KeccakMerkle.queries)
  unless opening.leafData.length == 100 && opening.siblingHashes.length == 528 do
    throw (IO.userError "Keccak Merkle opening shape differs from Rust")
  unless CompStark.Keccak.Merkle.verify tree.1 tree.2.root
      CompStark.Fixtures.KeccakMerkle.queries opening do
    throw (IO.userError "Keccak Merkle opening failed")
  IO.println s!"commit root {tree.2.root.val.data}, rows {opening.leafData.length}, siblings {opening.siblingHashes.length}"
  let result ← phase "duplex" fun _ ↦ CompStark.Fixtures.KeccakMerkle.duplexLoop
    10000 0 ⟨CompStark.Fixtures.KeccakMerkle.initial, #[]⟩ 0
  unless result.1 == 15976019921783725211 && result.2.stream.size == 10000 do
    throw (IO.userError "Keccak duplex sink differs from Rust")
  IO.println s!"duplex sink {result.1}, messages {result.2.stream.size}"
  let frame (n : Nat) : Array UInt64 := #[n.toUInt64, 0, 0, 4]
  let accept (out : Array UInt64) := out[0]! &&& 0xff == 0
  let nonce ← phase "grind" fun _ ↦ CompStark.Keccak.Duplex.grind
    CompStark.Fixtures.KeccakMerkle.rate (fun _ _ _ ↦ ())
    CompStark.Fixtures.KeccakMerkle.initial frame accept 65536
  let some (nonce, _) := nonce | throw (IO.userError "Keccak grind exhausted")
  unless nonce == 73 do throw (IO.userError "Keccak grinding nonce differs from Rust")
  IO.println s!"grinding nonce {nonce}"
  return 0

open CompStark CompStark.Stark CompStark.Fri in
/-- `gate WORKLOAD DIR`: one single-threaded run of a workload of `scripts/perf-gate`, its phases
marked through the FIFOs of `DIR`, at a fixed size from fixed inputs:

* `wide-quartic`, `wide-quintic`: `wide 64` on $2^{16}$ rows (`wideParams`) over the quartic or
  quintic extension, by phase (`gatePhases`), then a whole proof and its verification.
* `keccak`: Plonky3's Keccak AIR on `keccakShapedTrace 13` at Plonky3's example configuration, by
  phase, then a whole proof and its verification, which runs to the last check and rejects the
  pseudorandom trace's out-of-domain evaluation.
* `batch`: three `wide 64` tables of $2^{16}$, $2^{15}$ and $2^{12}$ rows, by phase, then a whole
  batch proof.
* `lookup`: `lookupBatch 14 12`, the first table's permutation trace and LogUp quotient, then a
  whole batch proof.
* `merkle`: the packed Merkle root of $2^{16}$ rows of 64 elements.
* `lde`: the coset LDE of `keccakShapedTrace 14`, column by column.
* `keccak-scalar`: 10,000 chained Keccak-f permutations and 64/512-byte hashes.
* `keccak-batch`: ten batches of 1,024 independent permutations and 64/512-byte hashes.
* `keccak-merkle`: 4,096 leaves of 64 lanes, 100 pruned queries, 10,000 writer messages,
  and an eight-bit smallest-nonce grind.
* `sumcheck-fold`: prepare one cubic-extension challenge and fold 16,384 ordinary and constant four-column row pairs. -/
def gate (workload : String) (dir : System.FilePath) : IO UInt32 := do
  let m ← Marks.open dir
  match workload with
  | "wide-quartic" | "wide-quintic" =>
    let logN := 16
    let A := wide 64
    let trace := #[encodeFields (wideTrace 64 (2 ^ logN))]
    let shapes := [(logN, A.logQuotientChunks logN)]
    if workload == "wide-quartic" then
      let B := CompStark.KoalaBear.backendFor [] 1 shapes
      gatePhases m B wideParams [(A, logN, trace)] (Challenge.ofCoeffs [5, 7, 11, 13])
        (Challenge.ofCoeffs [17, 19, 23, 29])
      gateProveVerify m B wideParams A logN trace
        (CompStark.KoalaBear.verifyFast wideParams A none · []) (.ok ())
    else
      let B := CompStark.KoalaBear.backendForQuintic [] 1 shapes
      gatePhases m B wideParams [(A, logN, trace)] (Challenge.ofCoeffs [5, 7, 11, 13])
        (Challenge.ofCoeffs [17, 19, 23, 29])
      gateProveVerify m B wideParams A logN trace
        (CompStark.KoalaBear.verifyFastQuintic wideParams A none · []) (.ok ())
  | "keccak" =>
    let logN := 13
    let A := CompStark.Fixtures.Keccak.air
    let trace := keccakShapedTrace logN
    let B := CompStark.KoalaBear.backendFor [CompStark.Fixtures.KeccakKernel.kernel] 1
      (keccakShapes logN)
    gatePhases m B keccakParams [(A, logN, trace)] (Challenge.ofCoeffs [5, 7, 11, 13])
      (Challenge.ofCoeffs [17, 19, 23, 29])
    gateProveVerify m B keccakParams A logN trace
      (CompStark.KoalaBear.verifyFast keccakParams A none · [])
      (.error "out-of-domain evaluation mismatch")
  | "batch" =>
    let logNs := [16, 15, 12]
    let instances : List (Batch.Instance KoalaBear.Fast.Field) :=
      logNs.map fun logN ↦ .ofAir (wide 64) logN
    let traces := logNs.map fun logN ↦ #[encodeFields (wideTrace 64 (2 ^ logN))]
    let B := CompStark.KoalaBear.backendFor [] 1 (Batch.shapes instances)
    gatePhases m B wideParams ((instances.zip traces).map fun (I, t) ↦ (I.air, I.logN, t))
      (Challenge.ofCoeffs [5, 7, 11, 13]) (Challenge.ofCoeffs [17, 19, 23, 29])
    let pf ← m.phase "prove" fun _ ↦ Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B wideParams
      instances traces (logNs.map fun _ ↦ [])
    IO.println s!"prove: witness {pf.oodWitness.val}"
    return 0
  | "lookup" =>
    let (instances, traces, pis) := lookupBatch 14 12
    let words := traces.map fun t ↦ #[encodeFields t]
    let B := CompStark.KoalaBear.backendFor [] 1 (Batch.shapes instances)
    let some I := instances.head? | return 1
    let A := I.air
    let ext := B.ldeTrace I.logN 1 gen A.width (words.headD #[])
    let chs := (Lookup.challengeLayout [I.lookups] (⟨3, 1, 4, 1⟩ : _root_.KoalaBear.Fast.Ext4)
      ⟨5, 9, 2, 6⟩).headD []
    let (perm, t) ← m.phase "permutation" fun _ ↦
      B.permutation 1 A I.lookups I.logN (words.headD #[]) [] chs
    let lq ← m.phase "lookup quotient" fun _ ↦ B.lookupQuotient A (A.lookupConstraints I.logN) []
      I.logN I.logQuotientChunks ext none perm chs t ⟨5, 7, 11, 13⟩
    let pf ← m.phase "prove" fun _ ↦ Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B wideParams
      instances words pis
    IO.println s!"lookup quotient: {lq.n} values, prove: witness {pf.oodWitness.val}"
    return 0
  | "merkle" =>
    let w := 64
    let vals := Array.ofFn (n := 2 ^ 16 * w) fun k ↦
      KoalaBear.Fast.ofUInt32 ((7 * k.val + 1) % 2130706433).toUInt32
    let chunks := #[encodeFields vals]
    let root ← m.phase "root" fun _ ↦ CompStark.Merkle.Packed.root KoalaBear.fieldSize w chunks
    IO.println s!"root word {read root 0}"
    return 0
  | "pcs" => pcsRun (fun label f ↦ m.phase label f)
  | "sumcheck-fold" => sumcheckFoldRun (fun label f ↦ m.phase label f)
  | "keccak-merkle" => keccakMerkleRun (fun label f ↦ m.phase label f)
  | "keccak-scalar" =>
    let seed := (Array.replicate 25 (0 : UInt64)).set! 0 0x123456789abcdef0
    let s ← m.phase "f1600 chain" fun _ ↦ keccakChain 10000 seed
    unless s[0]! == 0x03d0008026579d6c do
      IO.eprintln "Keccak permutation sink mismatch"; return 1
    IO.println s!"permutation sink {s[0]!}"
    for len in ([⟨64, by decide⟩, ⟨512, by decide⟩] : List (Fin 10000)) do
      let input := ByteArray.mk (Array.ofFn (n := len.val) fun i ↦ i.val.toUInt8)
      have hu : input.size < USize.size := by
        simp only [input, ByteArray.size, Array.size_ofFn]
        exact lt_of_lt_of_le (by omega) USize.le_size
      let sink ← m.phase s!"hash {len}" fun _ ↦ keccakHashes 10000 input hu 0
      let expected := 10000 * CompStark.Keccak.readLane
        (VCVio.Algorithms.Keccak.keccak256 input) 0
      unless sink == expected do
        IO.eprintln s!"Keccak hash {len} sink mismatch"; return 1
      IO.println s!"hash {len} sink {sink}"
    return 0
  | "keccak-batch" =>
    let states ← m.phase "f1600" fun _ ↦ keccakStateBatches 10 keccakStates
    let expected := (List.range 10).foldl
      (fun ss _ ↦ ss.map VCVio.Algorithms.Keccak.f1600) keccakStates
    unless states == expected do
      IO.eprintln "Keccak batch permutation mismatch"; return 1
    IO.println s!"batch states {states.size}, sink {(states[0]!)[0]!}"
    for len in ([⟨64, by decide⟩, ⟨512, by decide⟩] : List (Fin 10000)) do
      let inputs := keccakInputs len.val
      let sink ← m.phase s!"hash {len}" fun _ ↦ keccakHashBatches 10 inputs
        (keccakInputs_addressable len.val (by omega)) 0
      let expected := 10 * (inputs.map VCVio.Algorithms.Keccak.keccak256).foldl
        (fun s h ↦ s + CompStark.Keccak.readLane h 0) (0 : UInt64)
      unless sink == expected do
        IO.eprintln s!"Keccak batch hash {len} sink mismatch"; return 1
      IO.println s!"batch hash {len} sink {sink}"
    return 0
  | "lde" =>
    let logN := 14
    let trace := keccakShapedTrace logN
    let some P := CompStark.Stark.Fast.plan? (p := _root_.KoalaBear.fieldSize) logN 1
      CompStark.gen | return 1
    let cols ← m.phase "coset lde" fun _ ↦
      CompStark.Stark.Fast.ldeColumns P CompStark.Fixtures.Keccak.width trace
    IO.println s!"lde: {cols.size} columns"
    return 0
  | _ => IO.eprintln s!"unknown workload {workload}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["pcs"] => pcsRun (fun label f => do
      let start ← IO.monoNanosNow
      let result := f ()
      let finish ← IO.monoNanosNow
      IO.println s!"{label}: {finish - start} ns"
      pure result)
  | ["sumcheck-fold"] => sumcheckFoldRun (fun _ f => pure (f ()))
  | ["keccak-merkle"] => keccakMerkleRun (fun label f ↦ do
      let t ← IO.monoNanosNow
      let result ← IO.lazyPure f
      let elapsed := (← IO.monoNanosNow) - t
      IO.println s!"{label} ns={elapsed}"
      return result)
  | ["keccak-kernels", n] => keccakKernels n.toNat!
  | ["poseidon2-spec", logN] =>
    let n := 2 ^ logN.toNat!
    let P := KoalaBear.width16 KoalaBear.Fast.Field
    let s0 : Vector KoalaBear.Fast.Field 16 :=
      Vector.ofFn fun i ↦ KoalaBear.Fast.ofUInt32 i.val.toUInt32
    let mut samples := #[]
    for _ in [0:7] do
      let (ns, r) ← timeNs fun _ ↦ do
        let mut s := s0
        for _ in [0:n] do
          s := permute P s
        return s[0].val.toUInt64
      samples := samples.push (ns / n)
      if r == 12345 then IO.println "" -- keep the result live
    IO.println s!"poseidon2-spec width16 ns/perm median {(samples.qsort (· < ·))[3]!}"
    return 0
  | ["poseidon2-packed", logN] =>
    let n := 2 ^ logN.toNat!
    let groups := n / 8
    let P := KoalaBear.width16 KoalaBear.Fast.Field
    let K := Packed.Packed16.ofParams P
    -- State `l` of group `g` starts as `(g * 8 + l) * 16 + j` in coordinate `j`.
    let init : Array KoalaBear.Fast.Field := Array.ofFn (n := 128 * groups) fun k ↦
      let g := k.val / 128; let j := k.val % 128 / 8; let l := k.val % 8
      KoalaBear.Fast.ofUInt32 ((g * 8 + l) * 16 + j).toUInt32
    let buf := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields init
    let run (b : ByteArray) : ByteArray := Id.run do
      let mut b := b
      for g in [0:groups] do
        b := Packed.permute16 _root_.KoalaBear.fieldSize K b (128 * g).toUSize
      return b
    -- Check every lane of the first group against the specification.
    let out := run buf
    for l in [0:8] do
      let s : Vector KoalaBear.Fast.Field 16 := Vector.ofFn fun j ↦ init.getD (j.val * 8 + l) 0
      let e := permute P s
      for j in [0:16] do
        let w := CompPoly.CPolynomial.NTTFast.Packed.Native.read out (8 * j + l)
        if w != (e.toArray.getD j 0).val then
          IO.eprintln s!"mismatch lane {l} coordinate {j}"; return 1
    let mut samples := #[]
    for k in [0:7] do
      let input := CompPoly.CPolynomial.NTTFast.Packed.Native.write buf 0 k.toUInt32
      let (ns, r) ← timeNs fun _ ↦ do
        let b := run input
        return (CompPoly.CPolynomial.NTTFast.Packed.Native.read b 0).toUInt64
      samples := samples.push (ns * 10 / n)
      if r == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[3]!
    IO.println s!"poseidon2-packed width16 ns/perm median {m / 10}.{m % 10}"
    return 0
  | ["merkle", logH, widthArg, chunksArg] =>
    let h := 2 ^ logH.toNat!
    let w := widthArg.toNat!
    let C := chunksArg.toNat!
    let enc := encodeFields
    let entry (k : Nat) : KoalaBear.Fast.Field :=
      KoalaBear.Fast.ofUInt32 ((7 * k + 1) % 2130706433).toUInt32
    -- Check small shapes against the specification: odd heights, single rows, partial blocks.
    for (sh, sw) in [(1, 1), (2, 3), (5, 16), (8, 17), (13, 40), (64, 10), (33, 7)] do
      let vals := Array.ofFn (n := sh * sw) fun k ↦ entry k.val
      let spec := @CompStark.Merkle.Poseidon2.root KoalaBear.Fast.Field _
        (.ofSpec (KoalaBear.width16 _) (KoalaBear.width24 _)) [⟨sw, sh, vals⟩]
      let got := CompStark.Merkle.Packed.root KoalaBear.fieldSize sw #[enc vals]
      for j in [0:8] do
        if read got j != (spec.toArray.getD j 0).val then
          IO.eprintln s!"merkle mismatch at {sh} × {sw}, word {j}"; return 1
    let rowsPer := h / C
    let chunks := (Array.range C).map fun c ↦
      enc (Array.ofFn (n := rowsPer * w) fun k ↦ entry (c * rowsPer * w + k.val))
    let rootWords := CompStark.Merkle.Packed.root KoalaBear.fieldSize w chunks
    let canon := (List.range 8).map fun j ↦
      (KoalaBear.Fast.ringEquiv
          (CompPoly.CPolynomial.NTTFast.Packed.ofWord _ (read rootWords j))).val
    IO.println s!"root {canon}"
    let m ← timeMedian 15 fun k ↦
      let input := chunks.modify 0 fun c ↦ write c 0 k.toUInt32
      (read (CompStark.Merkle.Packed.root KoalaBear.fieldSize w input) 0).toUInt64
    IO.println s!"merkle 2^{logH} x {w} ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | ["leaves", rowsArg, widthArg] =>
    let rows := rowsArg.toNat!
    let w := widthArg.toNat!
    let m := encodeFields
      (Array.ofFn (n := rows * w) fun k ↦ KoalaBear.Fast.ofUInt32 k.val.toUInt32)
    let mut samples := #[]
    for k in [0:7] do
      let input := write m 0 k.toUInt32
      let (ns, r) ← timeNs fun _ ↦ do
        return (read
          (CompStark.Merkle.Packed.hashRange KoalaBear.fieldSize input w 0 rows) 0).toUInt64
      samples := samples.push ns
      if r == 12345 then IO.println ""
    let med := (samples.qsort (· < ·))[3]!
    IO.println s!"leaves {rows} x {w}: {med / 1000} us, {med / rows} ns/row"
    return 0
  | ["leavespar", rowsArg, widthArg, chunksArg] =>
    let rows := rowsArg.toNat!
    let w := widthArg.toNat!
    let C := chunksArg.toNat!
    let chunks := (Array.range C).map fun c ↦ encodeFields
      (Array.ofFn (n := rows / C * w) fun k ↦ KoalaBear.Fast.ofUInt32 (k.val + c).toUInt32)
    let mut samples := #[]
    for k in [0:7] do
      let input := chunks.modify 0 fun c ↦ write c 0 k.toUInt32
      let (ns, r) ← timeNs fun _ ↦ do
        let ts := input.map fun c ↦ Task.spawn fun _ ↦
          CompStark.Merkle.Packed.hashRange KoalaBear.fieldSize c w 0 (rows / C)
        let j := CompPoly.Tasks.join ts
        return j.get.foldl (fun acc t ↦ acc + (read t 0).toUInt64) 0
      samples := samples.push ns
      if r == 12345 then IO.println ""
    let med := (samples.qsort (· < ·))[3]!
    IO.println s!"leavespar {rows} x {w} in {C} chunks: {med / 1000} us"
    return 0
  | ["babybear-perm", logN] =>
    -- BabyBear's packed permutations of both widths, against the specification on one state.
    let groups := 2 ^ logN.toNat! / 8
    let K16 := CompStark.BabyBear.defaultInstances.K16
    let K24 := CompStark.BabyBear.defaultInstances.K24
    let time (t : Nat) (perm : ByteArray → USize → ByteArray) : IO Nat := do
      let buf := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
        (Array.ofFn (n := 8 * t * groups) fun k ↦ _root_.BabyBear.Fast.ofUInt32 k.val.toUInt32)
      let mut samples := #[]
      for k in [0:15] do
        let input := CompPoly.CPolynomial.NTTFast.Packed.Native.write buf 0 k.toUInt32
        if CompPoly.CPolynomial.NTTFast.Packed.Native.read input 1 == 12345 then IO.println ""
        let (ns, r) ← timeNs fun _ ↦ do
          let mut b := input
          for g in [0:groups] do
            b := perm b (8 * t * g).toUSize
          return (CompPoly.CPolynomial.NTTFast.Packed.Native.read b 0).toUInt64
        samples := samples.push (ns * 10 / (8 * groups))
        if r == 12345 then IO.println ""
      return (samples.qsort (· < ·))[7]!
    let m16 ← time 16 (Packed.permute16 _root_.BabyBear.fieldSize K16)
    let m24 ← time 24 (Packed.permute24 _root_.BabyBear.fieldSize K24)
    let P := CompStark.Poseidon2.BabyBear.width16 _root_.BabyBear.Fast.Field
    let (ns, r) ← timeNs fun _ ↦ do
      let mut s : Vector _root_.BabyBear.Fast.Field 16 := Vector.ofFn fun i ↦ (i.val : _)
      for _ in [0:64] do
        s := permute P s
      return s[0].val.toUInt64
    if r == 12345 then IO.println ""
    IO.println s!"babybear packed ns/perm width16 {m16 / 10}.{m16 % 10} width24 {m24 / 10}.{m24 % 10}"
    IO.println s!"babybear specification ns/perm width16 {ns / 64}"
    return 0
  | ["perm24", logN] =>
    let groups := 2 ^ logN.toNat! / 8
    let K := Packed.Packed24.ofParams (KoalaBear.width24 KoalaBear.Fast.Field)
    let buf := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
      (Array.ofFn (n := 192 * groups) fun k ↦ KoalaBear.Fast.ofUInt32 k.val.toUInt32)
    -- Each sample permutes its own copy of the buffer, made (and read) before the clock starts.
    let mut samples := #[]
    for k in [0:15] do
      let input := CompPoly.CPolynomial.NTTFast.Packed.Native.write buf 0 k.toUInt32
      if CompPoly.CPolynomial.NTTFast.Packed.Native.read input 1 == 12345 then IO.println ""
      let (ns, r) ← timeNs fun _ ↦ do
        let mut b := input
        for g in [0:groups] do
          b := Packed.permute24 _root_.KoalaBear.fieldSize K b (192 * g).toUSize
        return (CompPoly.CPolynomial.NTTFast.Packed.Native.read b 0).toUInt64
      samples := samples.push (ns * 10 / (8 * groups))
      if r == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[7]!
    IO.println s!"perm24 ns/perm median {m / 10}.{m % 10}"
    return 0
  | ["phases", "quartic", logN] =>
    phases logN.toNat! (CompStark.KoalaBear.backendFor [] 1 [(logN.toNat!, 1)])
  | ["phases", "quintic", logN] =>
    phases logN.toNat! (CompStark.KoalaBear.backendForQuintic [] 1 [(logN.toNat!, 1)])
  | ["lde", logN, w, reps] =>
    -- `lde LOG_N WIDTH REPS`: the median of `REPS` coset extensions by 2 of `randomTrace WIDTH
    -- LOG_N`, column by column (`compstark-bench lde LOG_N WIDTH`).
    let logN := logN.toNat!
    let w := w.toNat!
    let trace := randomTrace w logN
    let some P := CompStark.Stark.Fast.plan? (p := _root_.KoalaBear.fieldSize) logN 1
      CompStark.gen | return 1
    let mut samples := #[]
    for k in [0:reps.toNat!] do
      let input := trace.modify 0 (write · 0 k.toUInt32)
      let (ns, cols) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦
        CompStark.Stark.Fast.ldeColumns P w input
      if cols.size == 12345 then IO.println ""
      samples := samples.push ns
    let m := (samples.qsort (· < ·))[samples.size / 2]!
    IO.println s!"lean lde 2^{logN} x {w} ms median {m / 1000000}.{m / 100000 % 10}"
    return 0
  | ["keccak-phases", "quartic", logN] =>
    keccakPhases logN.toNat! (CompStark.KoalaBear.backendFor
      [CompStark.Fixtures.KeccakKernel.kernel] 1 (keccakShapes logN.toNat!)) id
  | ["keccak-phases", "quintic", logN] =>
    keccakPhases logN.toNat! (CompStark.KoalaBear.backendForQuintic
      [CompStark.Fixtures.KeccakKernel.kernel] 1 (keccakShapes logN.toNat!)) id
  | ["keccak-prove", "quartic", logN] =>
    keccakProve "quartic" logN.toNat! (CompStark.KoalaBear.backendFor
      [CompStark.Fixtures.KeccakKernel.kernel] 1 (keccakShapes logN.toNat!)) id
  | ["keccak-prove", "quintic", logN] =>
    keccakProve "quintic" logN.toNat! (CompStark.KoalaBear.backendForQuintic
      [CompStark.Fixtures.KeccakKernel.kernel] 1 (keccakShapes logN.toNat!)) id
  | ["phases-batch"] => phasesBatch
  | ["phases-lookup"] => phasesLookup
  | ["gate", workload, dir] => gate workload dir
  | ["openings-phase", air, logN, reps] => openingsPhase air logN.toNat! reps.toNat!
  | ["quotient-phase", air, logN, reps] => quotientPhase air logN.toNat! reps.toNat!
  | "prove" :: backend :: air :: rest =>
    -- `prove (spec|fast|fast-quintic) (fib|wide) LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES
    -- COMMIT_POW QUERY_POW [BATCH_POW OOD_POW] [JSON]`: the proof's median time, over the quartic
    -- extension or, for `fast-quintic`, the quintic one, checked against Plonky3's proof in `JSON`
    -- if given.
    let B := CompStark.Stark.specBackend KoalaBear.Fast.Ext4
    let ps := (rest.takeWhile String.isNat).map String.toNat!
    let P : CompStark.Fri.Params ← match ps.drop 1 with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0, 0⟩
      | [b, f, a, q, cp, qp, bp, op] => pure ⟨b, f, a, q, cp, qp, bp, op, 0, 0⟩
      | _ => IO.eprintln "seven or nine parameters"; return 1
    let logN := ps.headD 0
    let A := if air == "wide" then CompStark.Stark.wide 64 else CompStark.Stark.fibonacci
    let (trace, pis) :=
      if air == "wide" then (wideTrace 64 (2 ^ logN), []) else fibInstance (2 ^ logN)
    let json? := (rest.drop ps.length).head?
    if backend == "fast-quintic" then
      let rust? ← json?.mapM fun path ↦ do
        IO.ofExcept (CompStark.Stark.Json.parse (p := KoalaBear.fieldSize)
          (EF := KoalaBear.Fast.Ext5) (← IO.FS.readFile path))
      return ← proveTimed s!"fast prove {air} quintic 2^{logN}"
        (CompStark.KoalaBear.backendForQuintic [] P.logBlowup [(logN, A.logQuotientChunks logN)])
        P A logN (fun k ↦ #[encodeFields (trace.set! 0 (k : _))]) pis rust?
    let rust? ← json?.mapM fun path ↦ do
      IO.ofExcept (CompStark.Stark.Json.parse (p := KoalaBear.fieldSize)
        (EF := KoalaBear.Fast.Ext4) (← IO.FS.readFile path))
    if backend == "fast" then
      -- The fast backend's extension plans are built once, outside timing, as Plonky3's twiddles.
      proveTimed s!"fast prove {air} 2^{logN}"
        (CompStark.KoalaBear.backendFor [] P.logBlowup [(logN, A.logQuotientChunks logN)]) P A logN
        (fun k ↦ #[encodeFields (trace.set! 0 (k : _))]) pis rust?
    else
      proveTimed s!"spec prove {air} 2^{logN}" B P A logN (fun k ↦ trace.set! 0 (k : _)) pis
        rust?
  | "prove-batch" :: rest =>
    -- `prove-batch LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW
    -- OOD_POW]`: the fast batch prover's median time on three `wide 64` tables of `2 ^ 20`,
    -- `2 ^ 19` and `2 ^ 16` rows (`compstark-bench batch-bench wide …`).
    let P : CompStark.Fri.Params ← match rest.map String.toNat! with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0, 0⟩
      | [b, f, a, q, cp, qp, bp, op] => pure ⟨b, f, a, q, cp, qp, bp, op, 0, 0⟩
      | _ => IO.eprintln "six or eight parameters"; return 1
    let logNs := [20, 19, 16]
    let instances : List (CompStark.Batch.Instance KoalaBear.Fast.Field) :=
      logNs.map fun logN ↦ .ofAir (CompStark.Stark.wide 64) logN
    let traces := logNs.map fun logN ↦ wideTrace 64 (2 ^ logN)
    let pis := logNs.map fun _ ↦ []
    -- The fast backend's extension plans are built once, outside timing, as Plonky3's twiddles.
    let B := CompStark.KoalaBear.backendFor [] P.logBlowup (CompStark.Batch.shapes instances)
    let mut samples := #[]
    for k in [0:3] do
      let ws ← IO.lazyPure fun _ ↦ traces.map fun t ↦ #[encodeFields (t.set! 0 (k : _))]
      let (ns, pf) ← timeNs fun _ ↦ do
        return CompStark.Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B P instances ws pis
      samples := samples.push ns
      if pf.oodWitness == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[1]!
    IO.println
      s!"lean fast prove-batch wide 2^20+2^19+2^16 ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | "prove-batch-lookup" :: rest =>
    -- `prove-batch-lookup LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [JSON]`:
    -- the fast batch prover's median time on `lookupBatch 18 16` (`compstark-bench batch-bench
    -- lookup-bench …`), checked against Plonky3's proof in `JSON` if given.
    let ps := (rest.takeWhile String.isNat).map String.toNat!
    let P : CompStark.Fri.Params ← match ps with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0, 0⟩
      | _ => IO.eprintln "six parameters"; return 1
    let (instances, traces, pis) := lookupBatch 18 16
    let words := traces.map fun t ↦ #[encodeFields t]
    let B := CompStark.KoalaBear.backendFor [] P.logBlowup (CompStark.Batch.shapes instances)
    if let path :: _ := rest.drop ps.length then
      let rust ← IO.ofExcept (CompStark.Stark.Json.parseBatch (p := KoalaBear.fieldSize)
        (EF := KoalaBear.Fast.Ext4) (← IO.FS.readFile path))
      unless CompStark.Batch.proveBatchWith B P instances words pis == rust do
        IO.eprintln "proof differs from Plonky3's"; return 1
      IO.println "proof matches Plonky3's"
    let mut samples := #[]
    for k in [0:3] do
      let (ns, pf) ← timeNs fun _ ↦ do
        return CompStark.Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B P instances words
          (pis.map (·.map (· + (k : KoalaBear.Fast.Field) - k)))
      samples := samples.push ns
      if pf.oodWitness == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[1]!
    IO.println s!"lean fast prove-batch lookup-bench ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | _ => IO.eprintln "usage: CompStarkBench poseidon2-spec LOG_N"; return 1
