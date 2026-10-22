import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.Packed
import CompStark.Merkle.Packed
import CompStark.Merkle.Tree
import CompStark.Stark.Prover
import CompStark.KoalaBear.Fast
import CompStark.Mont32.Json
import CompStark.Batch.Prover

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
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0⟩
  let A := wide 64
  let trace := wideTrace 64 (2 ^ logN)
  let t ← IO.monoMsNow
  let lde := B.lde logN 1 gen 64 trace
  let t1 ← IO.monoMsNow
  IO.println s!"trace lde {t1 - t} ms"
  let tc := B.commit [lde]
  IO.println s!"trace commit {(← IO.monoMsNow) - t1} ms {((B.root tc).toArray.getD 0 0).val}"
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
  IO.println s!"quotient commit {t6 - t5} ms {((B.root qc).toArray.getD 0 0).val}"
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
  let P : Params := ⟨1, 0, 1, 100, 0, 16, 0, 0, 0⟩
  let logNs := [20, 19, 16]
  let instances : List (Batch.Instance KoalaBear.Fast.Field) :=
    logNs.map fun logN ↦ ⟨wide 64, logN⟩
  let B := CompStark.KoalaBear.backendFor P.logBlowup (Batch.shapes instances)
  for k in [0:2] do
    let traces := logNs.map fun logN ↦ (wideTrace 64 (2 ^ logN)).set! 0 (k : _)
    let exts ← timed "trace lde" (fun _ ↦ (instances.zip traces).map fun (I, t) ↦
      B.lde I.logN 1 BaseField.gen 64 t) fun e ↦ s!"{(e.map (·.height)).sum}"
    let mainC ← timed "trace commit" (fun _ ↦ B.commit exts)
      fun c ↦ s!"{((B.root c).toArray.getD 0 0).val}"
    let alpha : _root_.KoalaBear.Fast.Ext4 := ⟨5, 7, 11, k⟩
    let qs ← timed "quotient" (fun _ ↦ (instances.zip exts).map fun (I, e) ↦
      B.quotient I.air [] I.logN I.logQuotientChunks e none alpha) fun q ↦ s!"{(q.map (·.size)).sum}"
    let chunks ← timed "quotient chunks lde" (fun _ ↦ (instances.zip qs).map fun (I, q) ↦
      chunksOf B P I.logN I.logQuotientChunks q) fun c ↦ s!"{(c.map (·.length)).sum}"
    let quotC ← timed "quotient commit" (fun _ ↦ B.commit chunks.flatten)
      fun c ↦ s!"{((B.root c).toArray.getD 0 0).val}"
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
    let _ ← timed "whole proof" (fun _ ↦ Batch.proveBatchWith B P instances traces
      (logNs.map fun _ ↦ [])) fun pf ↦ s!"{pf.oodWitness.val}"
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
  | ["phases-batch"] => phasesBatch
  | "prove" :: backend :: air :: rest =>
    -- `prove (spec|fast) (fib|wide) LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW
    -- QUERY_POW [BATCH_POW OOD_POW] [JSON]`: the proof's median time, checked against Plonky3's
    -- proof in `JSON` if given.
    let B := CompStark.Stark.specBackend KoalaBear.Fast.Ext4
    let ps := (rest.takeWhile String.isNat).map String.toNat!
    let P : CompStark.Fri.Params ← match ps.drop 1 with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0⟩
      | [b, f, a, q, cp, qp, bp, op] => pure ⟨b, f, a, q, cp, qp, bp, op, 0⟩
      | _ => IO.eprintln "seven or nine parameters"; return 1
    let logN := ps.headD 0
    let A := if air == "wide" then CompStark.Stark.wide 64 else CompStark.Stark.fibonacci
    let (trace, pis) :=
      if air == "wide" then (wideTrace 64 (2 ^ logN), []) else fibInstance (2 ^ logN)
    -- The fast backend's extension plans are built once, outside timing, as Plonky3's twiddles.
    let B := if backend == "fast" then
      CompStark.KoalaBear.backendFor P.logBlowup [(logN, A.logQuotientChunks logN)] else B
    if let path :: _ := rest.drop ps.length then
      let rust ← IO.ofExcept
        (CompStark.Stark.Json.parse (p := KoalaBear.fieldSize) (EF := KoalaBear.Fast.Ext4)
          (← IO.FS.readFile path))
      unless CompStark.Stark.proveWith B P A logN trace pis == rust do
        IO.eprintln "proof differs from Plonky3's"; return 1
      IO.println "proof matches Plonky3's"
    let mut samples := #[]
    for k in [0:3] do
      let (ns, pf) ← timeNs fun _ ↦ do
        return CompStark.Stark.proveWith B P A logN (trace.set! 0 (k : _))
          pis
      samples := samples.push ns
      if pf.degreeBits == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[1]!
    IO.println s!"lean {backend} prove {air} 2^{logN} ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | "prove-batch" :: rest =>
    -- `prove-batch LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW
    -- OOD_POW]`: the fast batch prover's median time on three `wide 64` tables of `2 ^ 20`,
    -- `2 ^ 19` and `2 ^ 16` rows (`compstark-bench batch-bench wide …`).
    let P : CompStark.Fri.Params ← match rest.map String.toNat! with
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0⟩
      | [b, f, a, q, cp, qp, bp, op] => pure ⟨b, f, a, q, cp, qp, bp, op, 0⟩
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
      let (ns, pf) ← timeNs fun _ ↦ do
        return CompStark.Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B P instances
          (traces.map (·.set! 0 (k : _))) pis
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
      | [b, f, a, q, cp, qp] => pure ⟨b, f, a, q, cp, qp, 0, 0, 0⟩
      | _ => IO.eprintln "six parameters"; return 1
    let (instances, traces, pis) := lookupBatch
    let B := CompStark.KoalaBear.backendFor P.logBlowup (CompStark.Batch.shapes instances)
    if let path :: _ := rest.drop ps.length then
      let rust ← IO.ofExcept (CompStark.Stark.Json.parseBatch (p := KoalaBear.fieldSize)
        (EF := KoalaBear.Fast.Ext4) (← IO.FS.readFile path))
      unless CompStark.Batch.proveBatchWith B P instances traces pis == rust do
        IO.eprintln "proof differs from Plonky3's"; return 1
      IO.println "proof matches Plonky3's"
    let mut samples := #[]
    for k in [0:3] do
      let (ns, pf) ← timeNs fun _ ↦ do
        return CompStark.Batch.proveBatchWith (EF := KoalaBear.Fast.Ext4) B P instances traces
          (pis.map (·.map (· + (k : KoalaBear.Fast.Field) - k)))
      samples := samples.push ns
      if pf.oodWitness == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[1]!
    IO.println s!"lean fast prove-batch lookup-bench ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | _ => IO.eprintln "usage: CompStarkBench poseidon2-spec LOG_N"; return 1
