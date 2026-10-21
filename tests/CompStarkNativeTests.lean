/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStarkTests
import CompStark.KoalaBear.Fast
import CompStark.BabyBear.Fast
import CompStark.Mont32.Json
import CompStark.Plonky3.Batch

/-! # Compiled known-answer tests

The checks that run the packed kernels, which the interpreter cannot run (CompPoly's inline C
stores), compiled: `lake test` builds the `#guard` library `CompStarkTests` with this executable
and runs it.

* KoalaBear's Poseidon2 Merkle hashes and tree, and the duplex challenger, on its packed
  implementation (`KoalaBear.instPoseidon2Field`), against Plonky3 (`bench/rust`,
  `cargo run --release` and `RAYON_NUM_THREADS=1 compstark-bench challenger`); the packed Merkle
  root of single matrices against them.
* Plonky3 `uni-stark` proofs over KoalaBear (`tests/data/AIR_*.json`, from `RAYON_NUM_THREADS=1
  compstark-bench stark AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW
  QUERY_POW`), with preprocessed columns for `prep` and `prep0` (`mulFib`), periodic columns
  for `periodic`, `periodic-wide`, `periodic-tiny` (`periodicAir`) and `pcube` (`periodicCube`),
  and no next row read for `square`:
  each verifies against
  the verifying key of its preprocessed trace, the verifier rejects it with a changed opened
  value, a changed preprocessed opening, or a missing or wrong verifying key, and the
  specification prover and the fast prover reproduce it from the same trace. Over the quintic
  extension, the specification prover's proofs verify.
* The fast prover over BabyBear reproduces Plonky3's BabyBear proofs
  (`tests/data/babybear_AIR_*.json`).
* Plonky3 `batch-stark` proofs over KoalaBear (`tests/data/batch_CASE_*.json`, from
  `RAYON_NUM_THREADS=1 compstark-bench batch CASE LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES
  COMMIT_POW QUERY_POW`), of instances of mixed heights with and without preprocessed and
  periodic columns: each verifies against the batch's common data and is rejected tampered, with
  other degree bits or public values, with reordered instances, or against other preprocessed
  traces; and the specification prover reproduces it.
-/

namespace CompStarkTests.Native
open CompStark CompStark.Stark

/-- Fail with `label` unless `ok`. -/
def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"check failed: {label}")

namespace KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The canonical value of an element. -/
def canon (x : F) : Nat := Montgomery.Native32.FastField.toNat x

/-- The leaf hash of `0, …, n - 1`, as canonical outputs. -/
def hashIota (n : Nat) : Vector Nat 8 :=
  (Hash.Poseidon2.hash F ((List.range n).map Nat.cast)).map canon

/-- Plonky3's `PaddingFreeSponge<Perm24, 24, 16, 8>` and
`TruncatedPermutation<Perm16, 2, 8, 16>`. -/
def hashes : IO Unit := do
  check "hash 0" (hashIota 0 == #v[0, 0, 0, 0, 0, 0, 0, 0])
  check "hash 1" (hashIota 1 == #v[1918697942, 2025897067, 904050874, 1093610768, 214053233,
    1029880100, 2130076554, 348914674])
  check "hash 8" (hashIota 8 == #v[2129455014, 874087217, 1458168736, 922046730, 1131850208,
    1220695934, 117092781, 1149877263])
  check "hash 16" (hashIota 16 == #v[2025173805, 376571109, 397667895, 290387531, 643976470,
    262727570, 1515118423, 1345373838])
  check "hash 17" (hashIota 17 == #v[844004974, 1951610042, 349288228, 1448257859, 1632348304,
    293373545, 1305932743, 1694177388])
  check "hash 32" (hashIota 32 == #v[672207092, 533529338, 1473891192, 529835554, 826152480,
    2004142315, 2127886961, 765825440])
  check "hash 50" (hashIota 50 == #v[152354270, 1737983126, 949754739, 63128631, 744917888,
    2129863449, 1572018287, 40780702])
  check "compress" ((Hash.Poseidon2.compress F (Vector.ofFn fun i ↦ (i.val : _))
      (Vector.ofFn fun i ↦ ((100 + i.val : Nat) : _))).map canon ==
    #v[1291065250, 534321063, 510018167, 1981420033, 1609350329, 949133113, 1145580169,
      1762919665])

/-- A `height × width` matrix with entries `base, base + 1, …`. -/
def mat (base height width : Nat) : Merkle.Matrix F :=
  ⟨width, height, Array.ofFn (n := height * width) fun k ↦ ((base + k.val : Nat) : _)⟩

/-- The Merkle root of matrices `(base, height, width)`. -/
def rootOf (ms : List (Nat × Nat × Nat)) : Vector Nat 8 :=
  (Merkle.Poseidon2.root F (ms.map fun (b, h, w) ↦ mat b h w)).map canon

/-- The packed Merkle root of one matrix. -/
def packedRoot (base height width : Nat) : Vector Nat 8 :=
  let words := Merkle.Packed.root _root_.KoalaBear.fieldSize width
    #[CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (mat base height width).values]
  Vector.ofFn fun j ↦ canon (Stark.Fast.word words j.val)

/-- Roots of Plonky3's `MerkleTreeMmcs` on its Poseidon2 sponge and compression, covering odd
heights, single rows and injected smaller matrices. -/
def merkle : IO Unit := do
  let r1 := #v[1155711827, 200156654, 541381612, 2023518838, 127806045, 1732402474, 795809767,
    424002287]
  let r2 := #v[1179533772, 1644046154, 885019917, 499638768, 755068498, 1225070632, 492715846,
    349555037]
  let r3 := #v[1560602542, 1248288235, 887541759, 535668730, 308529504, 1692843089, 1979814949,
    502346592]
  check "root 8 × 3" (rootOf [(0, 8, 3)] == r1 && packedRoot 0 8 3 == r1)
  check "root 5 × 2" (rootOf [(0, 5, 2)] == r2 && packedRoot 0 5 2 == r2)
  check "root 1 × 10" (rootOf [(0, 1, 10)] == r3 && packedRoot 0 1 10 == r3)
  check "root of five" (rootOf [(0, 4, 5), (1000, 8, 3), (2000, 2, 1), (3000, 1, 7),
    (4000, 8, 2)] == #v[1288239597, 509039961, 491576154, 1966105894, 2160008, 1134247778,
      1401521895, 388012225])
  check "root of two" (rootOf [(0, 6, 3), (500, 3, 2)] == #v[869426140, 1213736601, 1861497526,
    1175038896, 43495077, 968121270, 579718730, 338406565])

/-- Plonky3's challenger on a fixed sequence from the transcript `t`: observe `0, …, 19`, sample
two elements and an extension element, observe `7` and an extension element, sample 10 bits,
grind 6 bits, and sample once more. -/
def challengerRun (t : Transcript F 24) : List Nat :=
  let c := (List.range 20).foldl (fun c i ↦ Transcript.observe c (i : F)) t
  let (a, c) := c.sample
  let (b, c) := c.sample
  let (e, c) := (c.sampleExt : EF × Transcript F 24)
  let c := (c.observe 7).observeExt (⟨100, 101, 102, 103⟩ : EF)
  let (bits, c) := c.sampleBits 10
  let (w, c) := c.grind 6
  let (z, _) := c.sample
  [canon a, canon b, canon e.c0, canon e.c1, canon e.c2, canon e.c3, bits, canon w, canon z]

/-- The specification and the fast transcripts against Plonky3's challenger. -/
def challenger : IO Unit := do
  let expected := [69659790, 574214938, 972478078, 1575898908, 847888869, 1166426239, 701, 195,
    759660911]
  check "challenger" (challengerRun Poseidon2.initTranscript == expected)
  check "fast challenger"
      (challengerRun (CompStark.KoalaBear.backendFor 0 0 0).transcript == expected)

/-- The Fibonacci trace of `n` rows from `(0, 1)` and its public values. -/
def fibInstance (n : Nat) : Array F × List F :=
  let (t, _, r) := (List.range n).foldl (fun ((t, l, r) : Array F × F × F) _ ↦
    (t.push l |>.push r, r, l + r)) (#[], 0, 1)
  (t, [0, 1, t.getD (2 * n - 1) r])

/-- The `cube` trace of `n` rows from `(2, 0)` and its public values. -/
def cubeInstance (n : Nat) : Array F × List F :=
  let (t, _, _) := (List.range n).foldl (fun ((t, x, y) : Array F × F × F) _ ↦
    (t.push x |>.push y, x * x * x + y, y + 1)) (#[], 2, 0)
  (t, [2, 0, t.getD (2 * n - 2) 0])

/-- The `mulFib` trace of `n` rows from `(1, 2)` and its public values. -/
def prepInstance (n : Nat) : Array F × List F :=
  let (t, _, _) := (List.range n).foldl (fun ((t, a, b) : Array F × F × F) i ↦
    let p : F := ((i % 2 : Nat) : F)
    let s : F := (((i + 1) % 6 : Nat) : F)
    (t.push a |>.push b, b, p * a * b + s * (a + b))) (#[], 1, 2)
  (t, [1, 2])

/-- The trace of `n` rows of `wide 64` from `xⱼ = j`. -/
def wideTrace (n : Nat) : Array F := Id.run do
  let mut out := Array.emptyWithCapacity (64 * n)
  let mut row : Array F := Array.ofFn (n := 64) fun j ↦ (j.val : _)
  for _ in [0:n] do
    out := out ++ row
    row := Array.ofFn (n := 64) fun j ↦
      let x := row.getD j 0
      x * x * x + row.getD ((j.val + 1) % 64) 0
  return out

/-- The trace of `n` rows of `periodicAir cols`: each column its periodic column. -/
def periodicInstance (cols : List (List F)) (n : Nat) : Array F × List F :=
  (Array.ofFn (n := n * 2) fun k ↦
    let c := cols.getD (k.val % 2) []
    c.getD (k.val / 2 % c.length) 0, [])

/-- The `periodicCube` trace of `n` rows from `(2, 0)` and its public values. -/
def pcubeInstance (n : Nat) : Array F × List F :=
  let (t, _, _) := (List.range n).foldl (fun ((t, x, y) : Array F × F × F) i ↦
    let s : F := ((i % 4 + 1 : Nat) : F)
    (t.push x |>.push y, 3 * x * x * x + s * y, y + s)) (#[], 2, 0)
  (t, [2, t.getD (2 * n - 2) 0])

/-- The `square` trace of `n` rows: `a = i + 1`, `b = a²` on row `i`. -/
def squareInstance (n : Nat) : Array F × List F :=
  (Array.ofFn (n := n * 2) fun k ↦
    let a : F := ((k.val / 2 + 1 : Nat) : F)
    if k.val % 2 = 0 then a else a * a, [])

/-- Plonky3's periods of `PeriodicAir`: the default, the wide range and the tiny quotient. -/
def periodicCols : List (List F) := [[1, 2, 3, 4], [10, 20]]
def periodicWideCols : List (List F) := [[7], (List.range 32).map Nat.cast]
def periodicTinyCols : List (List F) := [[9], [1, 2]]

/-- The parameters `logN logBlowup logFinal maxLogArity queries commitPow queryPow [batchPow
oodPow]`. -/
def params : List Nat → IO (Nat × Fri.Params)
  | [logN, b, f, a, q, cp, qp] => pure (logN, ⟨b, f, a, q, cp, qp, 0, 0⟩)
  | [logN, b, f, a, q, cp, qp, bp, op] => pure (logN, ⟨b, f, a, q, cp, qp, bp, op⟩)
  | _ => throw (IO.userError "seven or nine parameters")

/-- The proof with its first opened trace value changed. -/
def tamper (proof : Proof F EF) : Proof F EF :=
  { proof with opened := { proof.opened with
      traceLocal := proof.opened.traceLocal.modify 0 (· + 1) } }

/-- The proof with its first opened preprocessed value changed. -/
def tamperPreprocessed (proof : Proof F EF) : Proof F EF :=
  { proof with opened := { proof.opened with
      preprocessedLocal := proof.opened.preprocessedLocal.map (·.modify 0 (· + 1)) } }

/-- The saved proof of `air logN` for parameters `logN logBlowup logFinal maxLogArity queries
commitPow queryPow [batchPow oodPow]` verifies against the verifying key of its preprocessed
trace, is rejected when tampered, and both provers reproduce it. With preprocessed columns, it is
also rejected with a changed preprocessed opening, without a verifying key, and against the key
of another preprocessed trace. If the AIR does not read the next row, it is rejected with a next
row opened. -/
def proof (name : String) (air : Nat → Air F) (inst : Nat → Array F × List F)
    (ps : List Nat) : IO Unit := do
  let (logN, P) ← params ps
  let A := air logN
  let vk := setup P A logN
  let file := s!"{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let (trace, pis) := inst (2 ^ logN)
  if let .error e := verify P A vk rust pis then throw (IO.userError s!"{file}: {e}")
  check s!"{file}: rejects a tampered proof" (verify P A vk (tamper rust) pis matches .error _)
  unless A.mainNextRow do
    let withNext := { rust with opened := { rust.opened with
      traceNext := some (Array.replicate A.width 0) } }
    check s!"{file}: rejects an opened next row" (verify P A vk withNext pis matches .error _)
  if 0 < A.preprocessedWidth then
    check s!"{file}: rejects a tampered preprocessed opening"
      (verify P A vk (tamperPreprocessed rust) pis matches .error _)
    check s!"{file}: rejects a missing verifying key" (verify P A none rust pis matches .error _)
    let other := setup P { A with preprocessed := A.preprocessed.modify 0 (· + 1) } logN
    check s!"{file}: rejects another verifying key" (verify P A other rust pis matches .error _)
  check s!"{file}: specification prover" (prove EF P A logN trace pis == rust)
  check s!"{file}: fast prover"
    (proveWith (CompStark.KoalaBear.backendFor logN P.logBlowup (A.logQuotientChunks logN)) P A
      logN trace pis == rust)

/-- Over the quintic extension, the specification prover's proof verifies, and is rejected for
other public values. -/
def proofExt5 (air : Nat → Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit := do
  let (logN, P) ← params ps
  let A := air logN
  let (trace, pis) := inst (2 ^ logN)
  let pf := prove _root_.KoalaBear.Fast.Ext5 P A logN trace pis
  if let .error e := verify P A (setup P A logN) pf pis then
    throw (IO.userError s!"Ext5 {ps}: {e}")
  check s!"Ext5 {ps}: rejects other public values"
    (verify P A (setup P A logN) pf (pis.map (· + 1)) matches .error _)

/-- The Fibonacci numbers `F_0, …, F_n`. -/
def fibs (n : Nat) : Array F :=
  ((List.range n).foldl (fun ((a, b, out) : F × F × Array F) _ ↦ (b, a + b, out.push b))
    (0, 1, #[0])).2.2

/-- `mul_trace` of `batch-stark/tests/simple.rs`: `rows` rows of `mulAir reps`. -/
def mulTrace (rows reps : Nat) : Array F :=
  let w := 3 * reps + 1
  let f := fibs rows
  Array.ofFn (n := rows * w) fun k ↦
    let i := k.val / w
    let j := k.val % w
    if j + 1 = w then (if i + 1 = rows then 0 else f.getD (i + 1) 0)
    else if j % 3 = 0 then f.getD i 0
    else if j % 3 = 1 then f.getD (i + 1) 0
    else f.getD i 0 * f.getD (i + 1) 0

/-- An instance of the batch KATs with its trace and public values. -/
abbrev BatchInstance := Batch.Instance F × Array F × List F

def fibIndexed (logN : Nat) : BatchInstance :=
  (⟨fibonacciIndexed logN, logN⟩, fibInstance (2 ^ logN))
def mulInstance (logN reps : Nat) : BatchInstance :=
  (⟨mulAir reps, logN⟩, mulTrace (2 ^ logN) reps, [])

/-- The batches of `compstark-bench batch CASE`. -/
def batchCase : String → List BatchInstance
  | "three" => [fibIndexed 4, mulInstance 3 2, fibIndexed 3]
  | "mixed" => [fibIndexed 4, mulInstance 4 2]
  | "periodic" => [(⟨periodicAir periodicCols, 6⟩, periodicInstance periodicCols 64)]
  | "single" => [fibIndexed 5]
  | "prepmul" => [(⟨preprocessedMul 4 2, 4⟩, Array.ofFn (n := 16) fun i ↦ ((2 * i.val : Nat) : F),
      []), fibIndexed 5, mulInstance 3 1]
  | "square" => [(⟨square, 4⟩, squareInstance 16), fibIndexed 3]
  | _ => []

/-- The saved batch proof of `name` for the parameters `logBlowup logFinal maxLogArity queries
commitPow queryPow [batchPow oodPow]` verifies against the batch's common data; is rejected when
tampered, with a next row opened for an AIR that does not read it, with reordered instances, with
other degree bits, against the commitment to other preprocessed traces, and with an instance's
public values changed; and the specification prover reproduces it. -/
def batchProof (name : String) (ps : List Nat) : IO Unit := do
  let (_, P) ← params (0 :: ps)
  let insts := batchCase name
  let instances := insts.map (·.1)
  let traces := insts.map (·.2.1)
  let pis := insts.map (·.2.2)
  let common := Batch.setupBatch P instances
  let file := s!"batch_{name}_{"_".intercalate (ps.map toString)}"
  let rust : Batch.BatchProof F EF ←
    IO.ofExcept (Json.parseBatch (← IO.FS.readFile s!"tests/data/{file}.json"))
  if let .error e := Batch.verifyBatch P instances common rust pis then
    throw (IO.userError s!"{file}: {e}")
  let tampered := { rust with opened := rust.opened.modify (rust.opened.size - 1) fun o ↦
    { o with traceLocal := o.traceLocal.modify 0 (· + 1) } }
  check s!"{file}: rejects a tampered proof"
    (Batch.verifyBatch P instances common tampered pis matches .error _)
  for (I, i) in instances.zipIdx do
    unless I.air.mainNextRow do
      let withNext := { rust with opened := rust.opened.modify i fun o ↦
        { o with traceNext := some (Array.replicate I.air.width 0) } }
      check s!"{file}: rejects an opened next row"
        (Batch.verifyBatch P instances common withNext pis matches .error _)
  check s!"{file}: rejects other degree bits"
    (Batch.verifyBatch P instances common
      { rust with degreeBits := rust.degreeBits.modify 0 (· + 1) } pis matches .error _)
  check s!"{file}: rejects other public values"
    (Batch.verifyBatch P instances common rust (pis.map (·.map (· + 1)))
      matches .error _ || pis.all (·.isEmpty))
  if 1 < instances.length then
    let swapped := instances.drop 1 ++ instances.take 1
    check s!"{file}: rejects reordered instances" (Batch.verifyBatch P swapped
      (Batch.setupBatch P swapped) rust (pis.drop 1 ++ pis.take 1) matches .error _)
  let other := instances.map fun I ↦
    { I with air := { I.air with preprocessed := I.air.preprocessed.modify 2 (· + 1) } }
  if common.preprocessed.isSome then
    check s!"{file}: rejects other preprocessed traces"
      (Batch.verifyBatch P instances (Batch.setupBatch P other) rust pis matches .error _)
  check s!"{file}: specification prover" (Batch.proveBatch EF P instances traces pis == rust)

def batchProofs : IO Unit := do
  for ps in [[2, 0, 1, 4, 0, 0], [1, 1, 2, 6, 1, 2, 2, 3]] do
    batchProof "three" ps
  batchProof "mixed" [2, 0, 2, 5, 0, 0]
  batchProof "periodic" [2, 3, 2, 8, 0, 8]
  batchProof "single" [1, 0, 1, 5, 0, 2]
  batchProof "prepmul" [1, 1, 2, 6, 1, 2, 2, 3]
  batchProof "square" [1, 1, 2, 6, 1, 2, 2, 3]

def proofs : IO Unit := do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [3, 2, 2, 1, 2, 1, 1], [6, 1, 0, 1, 10, 0, 8],
      [6, 1, 1, 3, 8, 2, 4], [5, 2, 0, 2, 5, 0, 0], [5, 2, 1, 2, 6, 1, 2, 2, 3]] do
    proof "fib" (fun _ ↦ fibonacci) fibInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 3, 1, 2, 6, 1, 3], [5, 1, 0, 1, 7, 2, 3, 4, 1]] do
    proof "cube" (fun _ ↦ cube) cubeInstance ps
  proof "wide" (fun _ ↦ wide 64) (fun n ↦ (wideTrace n, [])) [10, 1, 0, 1, 20, 0, 4]
  for ps in [[6, 2, 3, 2, 8, 0, 8], [5, 1, 1, 2, 6, 1, 2, 2, 3]] do
    proof "periodic" (fun _ ↦ periodicAir periodicCols) (periodicInstance periodicCols) ps
  proof "periodic-wide" (fun _ ↦ periodicAir periodicWideCols) (periodicInstance periodicWideCols)
    [6, 2, 3, 2, 8, 0, 8]
  proof "periodic-tiny" (fun _ ↦ periodicAir periodicTinyCols) (periodicInstance periodicTinyCols)
    [1, 1, 0, 1, 6, 0, 2]
  for ps in [[5, 2, 0, 2, 5, 0, 0], [4, 1, 1, 2, 6, 1, 2, 2, 3]] do
    proof "pcube" (fun _ ↦ periodicCube) pcubeInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 1, 1, 2, 6, 1, 2, 2, 3], [3, 2, 2, 1, 2, 0, 0]] do
    proof "prep" (mulFib · true) prepInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 3, 1, 2, 6, 1, 3]] do
    proof "prep0" (mulFib · false) prepInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 1, 1, 2, 6, 1, 2, 2, 3]] do
    proof "square" (fun _ ↦ square) squareInstance ps
  for ps in [[3, 2, 2, 1, 2, 0, 0], [5, 2, 0, 2, 5, 0, 3], [4, 1, 0, 1, 3, 1, 1, 2, 2]] do
    proofExt5 (fun _ ↦ fibonacci) fibInstance ps
  proofExt5 (fun _ ↦ cube) cubeInstance [4, 2, 0, 1, 4, 1, 2]
  proofExt5 (mulFib · true) prepInstance [4, 2, 0, 1, 4, 1, 2]
  proofExt5 (fun _ ↦ periodicCube) pcubeInstance [4, 2, 0, 1, 4, 1, 2]

end KoalaBear

namespace BabyBear

local notation "F" => _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

/-- The fast prover reproduces Plonky3's saved BabyBear proof of `air logN`. -/
def proof (name : String) (air : Nat → Air F) (inst : Nat → Array F × List F)
    (ps : List Nat) : IO Unit := do
  let (logN, P) ← KoalaBear.params ps
  let A := air logN
  let file := s!"babybear_{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let (trace, pis) := inst (2 ^ logN)
  check s!"{file}: fast prover"
    (proveWith (CompStark.BabyBear.backendFor logN P.logBlowup (A.logQuotientChunks logN)) P A
      logN trace pis == rust)

def proofs : IO Unit := do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [6, 1, 1, 3, 8, 2, 4], [4, 1, 1, 2, 5, 1, 1, 3, 2]] do
    proof "fib" (fun _ ↦ fibonacci) CompStarkTests.BabyBear.fibInstance ps
  proof "cube" (fun _ ↦ cube) CompStarkTests.BabyBear.cubeInstance [5, 3, 1, 2, 6, 1, 3]
  proof "prep" (mulFib · true) CompStarkTests.BabyBear.prepInstance [4, 2, 0, 1, 4, 0, 0]
  proof "prep0" (mulFib · false) CompStarkTests.BabyBear.prepInstance [5, 1, 1, 2, 5, 1, 1, 3, 2]
  proof "periodic" (fun _ ↦ periodicAir CompStarkTests.BabyBear.periodicCols)
    (CompStarkTests.BabyBear.periodicInstance CompStarkTests.BabyBear.periodicCols)
    [5, 1, 1, 2, 6, 1, 2, 2, 3]
  proof "periodic-tiny" (fun _ ↦ periodicAir CompStarkTests.BabyBear.periodicTinyCols)
    (CompStarkTests.BabyBear.periodicInstance CompStarkTests.BabyBear.periodicTinyCols)
    [1, 1, 0, 1, 6, 0, 2]
  proof "pcube" (fun _ ↦ periodicCube) CompStarkTests.BabyBear.pcubeInstance
    [4, 1, 1, 2, 6, 1, 2, 2, 3]
  proof "square" (fun _ ↦ square) CompStarkTests.BabyBear.squareInstance [4, 1, 1, 2, 6, 1, 2, 2, 3]

end BabyBear

end CompStarkTests.Native

open CompStarkTests.Native in
def main : IO UInt32 := do
  try
    KoalaBear.hashes
    KoalaBear.merkle
    KoalaBear.challenger
    KoalaBear.proofs
    KoalaBear.batchProofs
    BabyBear.proofs
    IO.println "native tests passed"
    return 0
  catch e =>
    IO.eprintln e
    return 1
