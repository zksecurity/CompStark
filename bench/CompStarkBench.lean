import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.Packed
import CompStark.Merkle.Packed
import CompStark.Merkle.Tree
import CompStark.Stark.Prover
import CompStark.KoalaBear.Fast
import CompStark.Mont32.Json
import CompStark.Batch.Prover
import CompStark.Stark.Fingerprint
import CompStarkFixtures.Keccak

/-! # CompStark micro-benchmarks

`CompStarkBench poseidon2-spec LOG_N`: the width-16 specification on the Montgomery field, on
`2 ^ LOG_N` chained states; prints the median nanoseconds per permutation of seven runs.
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

/-- The batch `lookup-bench` of `compstark-bench`: `mulAirLookups 8` on `2 ^ 18` rows with local
lookups and sending on the bus `MulFib`, `fibonacciLookups` receiving eight times on `2 ^ 18`
rows, and `mulAirLookups 8` with local lookups on `2 ^ 16` rows; with traces and public values. -/
def lookupBatch : List (CompStark.Batch.Instance KoalaBear.Fast.Field) ×
    List (Array KoalaBear.Fast.Field) × List (List KoalaBear.Fast.Field) :=
  let n := 2 ^ 18
  let f := fibs n
  ([⟨CompStark.Stark.mulAirLookups 8 true (List.replicate 8 "MulFib"), 18⟩,
      ⟨CompStark.Stark.fibonacciLookups 18 "MulFib" 8, 18⟩,
      ⟨CompStark.Stark.mulAirLookups 8 true [], 16⟩],
    [mulTrace n 8, Array.ofFn (n := 2 * n) fun j ↦ f.getD (j.val / 2 + j.val % 2) 0,
      mulTrace (2 ^ 16) 8],
    [[], [0, 1, f.getD n 0], []])

open CompStark CompStark.Stark CompStark.Fri in
/-- The wall time of each phase of the fast prover on `wide 64`, `2 ^ logN` rows, blowup 2. -/
def phases (logN : Nat) : IO UInt32 := do
  let B := CompStark.KoalaBear.backendFor 1 [(logN, 1)]
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0, 0⟩
  let A := wide 64
  let trace := wideTrace 64 (2 ^ logN)
  let t ← IO.monoMsNow
  let lde := B.lde logN 1 gen 64 trace
  let t1 ← IO.monoMsNow
  IO.println s!"trace lde {t1 - t} ms"
  let tc := B.commit [lde]
  IO.println s!"trace commit {(← IO.monoMsNow) - t1} ms {((B.cap tc 0).getD 0 0)[0].val}"
  let qlog := logN + 1
  let t3 ← IO.monoMsNow
  let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, 13⟩
  let qs := B.quotient A [] logN 1 lde none alpha
  let t4 ← IO.monoMsNow
  IO.println s!"quotient {t4 - t3} ms {qs.size}"
  let chunks := (List.range 2).map fun c ↦
    let shift := gen * powF (twoAdicGen qlog) c
    let vals := chunkValues qs 2 c (2 ^ logN)
    B.lde logN 1 (gen * shift⁻¹) 4 vals
  let t5 ← IO.monoMsNow
  IO.println s!"quotient chunks lde {t5 - t4} ms {chunks.length}"
  let qc := B.commit chunks
  let t6 ← IO.monoMsNow
  IO.println s!"quotient commit {t6 - t5} ms {((B.cap qc 0).getD 0 0)[0].val}"
  let zeta : _root_.KoalaBear.Fast.Ext4 := ⟨17, 19, 23, 29⟩
  let rounds : List (OpenRound B) :=
    [(tc, [(lde, [zeta, zeta * zeta])]), (qc, chunks.map fun m ↦ (m, [zeta]))]
  let t6 ← IO.monoMsNow
  let opened := rounds.map fun (_, ms) ↦ ms.map fun (m, zs) ↦ B.openedAt 1 m zs
  let t7 ← IO.monoMsNow
  IO.println s!"opened values {t7 - t6} ms {opened.length}"
  let items := ((rounds.zip opened).map fun ((_, ms), orow) ↦
    (ms.zip orow).map fun ((m, zs), ovs) ↦ (m, zs.zip ovs)).flatten
  let red := B.reduce alpha items
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
    logNs.map fun logN ↦ ⟨wide 64, logN⟩
  let B := CompStark.KoalaBear.backendFor P.logBlowup (Batch.shapes instances)
  for k in [0:2] do
    let traces := logNs.map fun logN ↦ (wideTrace 64 (2 ^ logN)).set! 0 (k : _)
    let exts ← timed "trace lde" (fun _ ↦ (instances.zip traces).map fun (I, t) ↦
      B.lde I.logN 1 BaseField.gen 64 t) fun e ↦ s!"{(e.map (·.height)).sum}"
    let mainC ← timed "trace commit" (fun _ ↦ B.commit exts)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, k⟩
    let qs ← timed "quotient" (fun _ ↦ (instances.zip exts).map fun (I, e) ↦
      B.quotient I.air [] I.logN I.logQuotientChunks e none alpha) fun q ↦ s!"{(q.map (·.size)).sum}"
    let chunks ← timed "quotient chunks lde" (fun _ ↦ (instances.zip qs).map fun (I, q) ↦
      chunksOf B P I.logN I.logQuotientChunks q) fun c ↦ s!"{(c.map (·.length)).sum}"
    let quotC ← timed "quotient commit" (fun _ ↦ B.commit chunks.flatten)
      fun c ↦ s!"{((B.cap c 0).getD 0 0)[0].val}"
    let zeta : _root_.KoalaBear.Fast.Ext4 := ⟨17, 19, 23, k⟩
    let rounds : List (OpenRound B) :=
      [(mainC, (instances.zip exts).map fun (I, e) ↦
          (e, [zeta, zeta * Ext.ofBase (twoAdicGen I.logN)])),
        (quotC, chunks.flatten.map fun m ↦ (m, [zeta]))]
    let opened ← timed "opened values" (fun _ ↦ rounds.map fun (_, ms) ↦ ms.map fun (m, zs) ↦
      B.openedAt 1 m zs) fun o ↦ s!"{o.length}"
    let items := ((rounds.zip opened).map fun ((_, ms), orow) ↦
      (ms.zip orow).map fun ((m, zs), ovs) ↦ (m, zs.zip ovs)).flatten
    let red ← timed "reduce" (fun _ ↦ B.reduce alpha items) fun r ↦ s!"{r.length}"
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

open CompStark CompStark.Stark CompStark.Fri in
/-- `keccak LOG_N REPS`: Plonky3's Keccak AIR on `2 ^ LOG_N` rows of pseudorandom permutations, at
Plonky3's example configuration (blowup 2, arity up to 8, 87 queries, caps of height 3): per round
the trace generation, the fast prover's phases (the trace's extension from its row chunks, its
commitment, the quotient) and a whole proof from the row chunks; then the medians of `REPS`
rounds. -/
def keccak (logN reps : Nat) : IO UInt32 := do
  let p := _root_.KoalaBear.fieldSize
  let A : Air KoalaBear.Fast.Field := CompStark.Fixtures.Keccak.air
  let w := CompStark.Fixtures.Keccak.width
  let P : Params := ⟨1, 0, 3, 87, 0, 16, 10, 0, 0, 3⟩
  let inputs := (Array.range (2 ^ logN / 24)).map fun k ↦ (Array.range 25).map fun i ↦
    (splitMix (25 * k + i).toUInt64).2
  let B := CompStark.KoalaBear.backendFor 1 [(logN, A.logQuotientChunks logN)]
  let labels := #["tracegen", "trace lde", "trace commit", "quotient", "whole proof"]
  let mut samples : Array (Array Nat) := labels.map fun _ ↦ #[]
  for _ in [0:reps] do
    let (t0, chunks) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦
      CompStark.Fixtures.Keccak.trace p inputs 16
    let (t1, lde) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ B.ldeTrace logN 1 gen w chunks
    let (t2, tc) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ B.commit [lde]
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, 13⟩
    let (t3, q) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦
      B.quotient A [] logN (A.logQuotientChunks logN) lde none alpha
    if tc.mats.length + q.size == 12345 then IO.println ""
    let (t4, pf) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ proveWith B P A logN chunks []
    if pf.degreeBits == 12345 then IO.println ""
    let ts := #[t0, t1, t2, t3, t4]
    IO.println (" ".intercalate ((labels.zip ts).toList.map fun (l, t) ↦
      s!"{l} {t / 1000000} ms"))
    samples := (samples.zip ts).map fun (s, t) ↦ s.push t
  for (l, s) in labels.zip samples do
    let m := (s.qsort (· < ·))[s.size / 2]!
    IO.println s!"lean keccak 2^{logN} {l} median {m / 1000000} ms"
  return 0


open CompStark CompStark.Stark CompStark.Fri in
/-- `quotient-phase AIR LOG_N REPS`: the fast prover's quotient phase on `2 ^ LOG_N` rows,
blowup 2, for `keccak` (Plonky3's Keccak AIR), `wide` (`wide 64`), `widebus` (`wideBus 64`) or
`lookup` (`mulAirLookups 8` with local lookups, sending on eight buses): per round the AIR's
quotient values and, with lookups, the permutation trace's extension and the LogUp constraints'
quotient values, from the trace's extension; then the medians of `REPS` rounds. -/
def quotientPhase (air : String) (logN reps : Nat) : IO UInt32 := do
  let n := 2 ^ logN
  let (A, chunks) : Air KoalaBear.Fast.Field × Array ByteArray ← match air with
    | "keccak" =>
      let inputs := (Array.range (n / 24)).map fun k ↦ (Array.range 25).map fun i ↦
        (splitMix (25 * k + i).toUInt64).2
      pure (CompStark.Fixtures.Keccak.air,
        CompStark.Fixtures.Keccak.trace _root_.KoalaBear.fieldSize inputs 16)
    | "wide" => pure (wide 64, #[encodeFields (wideTrace 64 n)])
    | "widebus" => pure (wideBus 64, #[encodeFields (wideTrace 64 n)])
    | "lookup" =>
      pure (mulAirLookups 8 true (List.replicate 8 "MulFib"), #[encodeFields (mulTrace n 8)])
    | _ => IO.eprintln "AIR: keccak, wide, widebus or lookup"; return 1
  let I : Batch.Instance KoalaBear.Fast.Field := ⟨A, logN⟩
  let B := CompStark.KoalaBear.backendFor 1 [(logN, I.logQuotientChunks)]
  let trace := B.traceValues chunks
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
      if I.lookups.isEmpty then none else some (B.permutation 1 A I.lookups logN trace [] chs)
    let (t2, lq) ← timeNs fun _ ↦ IO.lazyPure fun _ ↦ match pm with
      | none => #[]
      | some (perm, t) => B.lookupQuotient A (A.lookupConstraints logN) [] logN
          I.logQuotientChunks ext none perm chs t alpha
    IO.println s!"quotient {t0 / 1000000} ms permutation {t1 / 1000000} ms \
      lookup quotient {t2 / 1000000} ms {((q.getD 5 0) + lq.getD 5 0).c0.val}"
    samples := (samples.zip #[t0, t1, t2]).map fun (s, t) ↦ s.push t
  for (l, s) in labels.zip samples do
    let m := (s.qsort (· < ·))[s.size / 2]!
    IO.println s!"lean {air} 2^{logN} {l} median {m / 1000000} ms"
  return 0


/-- The median time of three proofs by `B` of `A` on the traces `trace 0, trace 1, trace 2`,
checked against the proof `rust?` on the first if given. -/
def proveTimed (label : String)
    (B : CompStark.Fri.Backend KoalaBear.Fast.Field KoalaBear.Fast.Ext4 24)
    (P : CompStark.Fri.Params) (A : CompStark.Stark.Air KoalaBear.Fast.Field) (logN : Nat)
    (trace : Nat → B.Trace) (pis : List KoalaBear.Fast.Field)
    (rust? : Option (CompStark.Stark.Proof KoalaBear.Fast.Field KoalaBear.Fast.Ext4)) :
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


def main (args : List String) : IO UInt32 := do
  match args with
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
        b := Packed.permute16 K b (128 * g).toUSize
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
          (CompStark.Merkle.Packed.hashChunk KoalaBear.fieldSize input w rows) 0).toUInt64
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
          CompStark.Merkle.Packed.hashChunk KoalaBear.fieldSize c w (rows / C)
        let j := CompPoly.Tasks.join ts
        return j.get.foldl (fun acc t ↦ acc + (read t 0).toUInt64) 0
      samples := samples.push ns
      if r == 12345 then IO.println ""
    let med := (samples.qsort (· < ·))[3]!
    IO.println s!"leavespar {rows} x {w} in {C} chunks: {med / 1000} us"
    return 0
  | ["perm24", logN] =>
    let groups := 2 ^ logN.toNat! / 8
    let K := Packed.Packed24.ofParams (KoalaBear.width24 KoalaBear.Fast.Field)
    let buf := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
      (Array.ofFn (n := 192 * groups) fun k ↦ KoalaBear.Fast.ofUInt32 k.val.toUInt32)
    let m ← timeMedian 15 fun k ↦ Id.run do
      let mut b := CompPoly.CPolynomial.NTTFast.Packed.Native.write buf 0 k.toUInt32
      for g in [0:groups] do
        b := Packed.permute24 K b (192 * g).toUSize
      return (CompPoly.CPolynomial.NTTFast.Packed.Native.read b 0).toUInt64
    IO.println s!"perm24 ns/perm {m * 10 / (8 * groups) / 10}.{m * 10 / (8 * groups) % 10}"
    return 0
  | ["phases", logN] => phases logN.toNat!
  | ["keccak", logN, reps] => keccak logN.toNat! reps.toNat!
  | ["keccak-lde", logN] =>
    -- The trace's extension from packed words, five times.
    let logN := logN.toNat!
    let w := CompStark.Fixtures.Keccak.width
    let inputs := (Array.range (2 ^ logN / 24)).map fun k ↦ (Array.range 25).map fun i ↦
      (CompStark.Stark.splitMix (25 * k + i).toUInt64).2
    let trace := CompStark.Fixtures.Keccak.trace _root_.KoalaBear.fieldSize inputs 16
    let some P := CompStark.Stark.Fast.plan? (p := _root_.KoalaBear.fieldSize) logN 1
      CompStark.gen | return 1
    for k in [0:5] do
      let chunks ← timed "coset lde chunks" (fun _ ↦ P.cosetLde w (trace.modify 0 (write · 0
        k.toUInt32))) (s!"{·.size} chunks")
      let _ ← timed "join" (fun _ ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.joinRows chunks)
        (s!"{·.size} bytes")
    return 0
  | ["phases-batch"] => phasesBatch
  | ["quotient-phase", air, logN, reps] => quotientPhase air logN.toNat! reps.toNat!
  | "prove" :: backend :: air :: rest =>
    -- `prove (spec|fast) (fib|wide) LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW
    -- QUERY_POW [BATCH_POW OOD_POW] [JSON]`: the proof's median time, checked against Plonky3's
    -- proof in `JSON` if given.
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
    let rust? ← (rest.drop ps.length).head?.mapM fun path ↦ do
      IO.ofExcept (CompStark.Stark.Json.parse (p := KoalaBear.fieldSize)
        (EF := KoalaBear.Fast.Ext4) (← IO.FS.readFile path))
    if backend == "fast" then
      -- The fast backend's extension plans are built once, outside timing, as Plonky3's twiddles.
      proveTimed s!"fast prove {air} 2^{logN}"
        (CompStark.KoalaBear.backendFor P.logBlowup [(logN, A.logQuotientChunks logN)]) P A logN
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
      logNs.map fun logN ↦ ⟨CompStark.Stark.wide 64, logN⟩
    let traces := logNs.map fun logN ↦ wideTrace 64 (2 ^ logN)
    let pis := logNs.map fun _ ↦ []
    -- The fast backend's extension plans are built once, outside timing, as Plonky3's twiddles.
    let B := CompStark.KoalaBear.backendFor P.logBlowup (CompStark.Batch.shapes instances)
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
    -- the fast batch prover's median time on `lookupBatch` (`compstark-bench batch-bench
    -- lookup-bench …`), checked against Plonky3's proof in `JSON` if given.
    let ps := (rest.takeWhile String.isNat).map String.toNat!
    let P : CompStark.Fri.Params ← match ps with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0, 0⟩
      | _ => IO.eprintln "six parameters"; return 1
    let (instances, traces, pis) := lookupBatch
    let words := traces.map fun t ↦ #[encodeFields t]
    let B := CompStark.KoalaBear.backendFor P.logBlowup (CompStark.Batch.shapes instances)
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
