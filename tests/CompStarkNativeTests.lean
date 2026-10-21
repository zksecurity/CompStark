/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStarkTests
import CompStark.KoalaBear.Fast
import CompStark.BabyBear.Fast
import CompStark.Mont32.Json

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
  QUERY_POW`): each verifies, the verifier rejects it with a changed opened value, and the
  specification prover and the fast prover reproduce it from the same trace. Over the quintic
  extension, the specification prover's proofs verify.
* The fast prover over BabyBear reproduces Plonky3's BabyBear proofs
  (`tests/data/babybear_AIR_*.json`).
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
  check "hash 1" (hashIota 1 == #v[1372179428, 133812428, 696896225, 1987094720, 2054524407,
    903120858, 1657571027, 324691152])
  check "hash 8" (hashIota 8 == #v[2067671377, 285730248, 67081120, 1570755920, 810744145,
    2106090739, 18027642, 346009986])
  check "hash 16" (hashIota 16 == #v[403818341, 1636855270, 787684945, 1713176768, 2101345750,
    943584829, 1807014356, 1669906235])
  check "hash 17" (hashIota 17 == #v[1076045929, 1862126369, 541684338, 161054317, 197069995,
    79500844, 1582073440, 882092014])
  check "hash 32" (hashIota 32 == #v[300880145, 421418732, 997536514, 622983904, 1383735143,
    464819595, 1098806565, 1343681663])
  check "hash 50" (hashIota 50 == #v[856552550, 535981396, 1199560609, 1880955451, 1889767569,
    338613516, 2127631099, 1133148347])
  check "compress" ((Hash.Poseidon2.compress F (Vector.ofFn fun i ↦ (i.val : _))
      (Vector.ofFn fun i ↦ ((100 + i.val : Nat) : _))).map canon ==
    #v[1735060840, 251194189, 1830597343, 733824892, 2052730034, 1625998731, 1433224953,
      835724207])

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
  let r1 := #v[839328004, 1713888626, 47538326, 961529694, 1367537855, 384103636, 1060544133,
    485679400]
  let r2 := #v[489187703, 929509427, 1512075425, 176164476, 1755927159, 1019341202, 1923645285,
    1724637561]
  let r3 := #v[807353722, 690866596, 1884109333, 1323245552, 1700476937, 1797497072, 1087871157,
    1493878500]
  check "root 8 × 3" (rootOf [(0, 8, 3)] == r1 && packedRoot 0 8 3 == r1)
  check "root 5 × 2" (rootOf [(0, 5, 2)] == r2 && packedRoot 0 5 2 == r2)
  check "root 1 × 10" (rootOf [(0, 1, 10)] == r3 && packedRoot 0 1 10 == r3)
  check "root of five" (rootOf [(0, 4, 5), (1000, 8, 3), (2000, 2, 1), (3000, 1, 7),
    (4000, 8, 2)] == #v[1170636731, 1464782430, 93151705, 555063351, 1082903266, 2078379327,
      13779068, 1472929077])
  check "root of two" (rootOf [(0, 6, 3), (500, 3, 2)] == #v[1638766218, 131982039, 1467186891,
    1331228402, 1237520776, 1318414788, 1465319517, 1282851410])

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
  let expected := [1315075128, 621498114, 1241469331, 965142788, 1213494102, 2071041246, 703, 123,
    1348157896]
  check "challenger" (challengerRun Poseidon2.initTranscript == expected)
  check "fast challenger" (challengerRun (CompStark.KoalaBear.backendFor 0 0 0).transcript ==
      expected)

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

/-- The proof with its first opened trace value changed. -/
def tamper (proof : Proof F EF) : Proof F EF :=
  { proof with opened := { proof.opened with
      traceLocal := proof.opened.traceLocal.modify 0 (· + 1) } }

/-- The saved proof of `air` for parameters `logN logBlowup logFinal maxLogArity queries
commitPow queryPow` verifies, is rejected when tampered, and both provers reproduce it. -/
def proof (name : String) (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit :=
    do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let file := s!"{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  if let .error e := verify P A rust pis then throw (IO.userError s!"{file}: {e}")
  check s!"{file}: rejects a tampered proof" (verify P A (tamper rust) pis matches .error _)
  check s!"{file}: specification prover" (prove EF P A logN trace pis == rust)
  check s!"{file}: fast prover"
    (proveWith (CompStark.KoalaBear.backendFor logN b A.logQuotientChunks) P A logN trace pis ==
        rust)

/-- Over the quintic extension, the specification prover's proof verifies, and is rejected for
other public values. -/
def proofExt5 (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit := do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  let pf := prove _root_.KoalaBear.Fast.Ext5 P A logN trace pis
  if let .error e := verify P A pf pis then throw (IO.userError s!"Ext5 {ps}: {e}")
  check s!"Ext5 {ps}: rejects other public values"
    (verify P A pf (pis.map (· + 1)) matches .error _)

def proofs : IO Unit := do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [3, 2, 2, 1, 2, 1, 1], [6, 1, 0, 1, 10, 0, 8],
      [6, 1, 1, 3, 8, 2, 4], [5, 2, 0, 2, 5, 0, 0]] do
    proof "fib" fibonacci fibInstance ps
  for ps in [[4, 2, 0, 1, 4, 0, 0], [5, 3, 1, 2, 6, 1, 3]] do
    proof "cube" cube cubeInstance ps
  proof "wide" (wide 64) (fun n ↦ (wideTrace n, [])) [10, 1, 0, 1, 20, 0, 4]
  for ps in [[3, 2, 2, 1, 2, 0, 0], [5, 2, 0, 2, 5, 0, 3]] do
    proofExt5 fibonacci fibInstance ps
  proofExt5 cube cubeInstance [4, 2, 0, 1, 4, 1, 2]

end KoalaBear

namespace BabyBear

local notation "F" => _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

/-- The fast prover reproduces Plonky3's saved BabyBear proof of `air`. -/
def proof (name : String) (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit :=
    do
  let [logN, b, f, a, q, cp, qp] := ps | throw (IO.userError "seven parameters")
  let file := s!"babybear_{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let P : Fri.Params := ⟨b, f, a, q, cp, qp⟩
  let (trace, pis) := inst (2 ^ logN)
  check s!"{file}: fast prover"
    (proveWith (CompStark.BabyBear.backendFor logN b A.logQuotientChunks) P A logN trace pis ==
        rust)

def proofs : IO Unit := do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [6, 1, 1, 3, 8, 2, 4]] do
    proof "fib" fibonacci CompStarkTests.BabyBear.fibInstance ps
  proof "cube" cube CompStarkTests.BabyBear.cubeInstance [5, 3, 1, 2, 6, 1, 3]

end BabyBear

end CompStarkTests.Native

open CompStarkTests.Native in
def main : IO UInt32 := do
  try
    KoalaBear.hashes
    KoalaBear.merkle
    KoalaBear.challenger
    KoalaBear.proofs
    BabyBear.proofs
    IO.println "native tests passed"
    return 0
  catch e =>
    IO.eprintln e
    return 1
