/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Stark.Fingerprint
import CompStark.KoalaBear.Poseidon2
import CompStark.KoalaBear.Challenge
import CompStark.Plonky3.Prover
import CompStark.Stark.Fast
import CompStark.KoalaBear.Fast
import CompStark.Mont32.Json
import CompStarkFixtures.Keccak
import CompStarkFixtures.KeccakKernel
import CompStarkFixtures.Poseidon2Example
import CompPoly.Univariate.NTTFast.Packed.Instances

/-! # Fingerprints and Plonky3's Keccak example

Compiled checks (`tests/CompStarkNativeTests.lean`), since the fingerprint's sponge runs on
KoalaBear's packed Poseidon2:

* The fingerprint reports of the example AIRs and of Plonky3's `KeccakAir` match Plonky3's, line
  for line (`tests/data/fingerprint/AIR_LOGN.json`, from `compstark-bench fingerprint AIR LOGN`):
  the same shape, constraint values, lookups and digest.
* Plonky3's example `prove_prime_field_31` for Keccak-f over KoalaBear with Poseidon2 Merkle
  hashes, on `2 ^ 6` rows (`tests/data/keccak_example_6.json`, the permutations' inputs
  `tests/data/keccak_example_6_inputs.txt` and Plonky3's trace
  `tests/data/keccak_example_6_trace.txt`, from `RAYON_NUM_THREADS=1 compstark-bench
  keccak-example 6 tests/data`, the example's configuration from the same upstream functions:
  caps of height `3`, the Poseidon2 constants of `SmallRng` seeded with `1`, 87 queries): the
  verifier accepts its proof, and the fast prover, with the AIR's generated quotient kernel, and
  the specification prover reproduce it from Plonky3's trace.
-/

namespace CompStarkTests.Keccak
open CompStark CompStark.Stark
open CompPoly.CPolynomial.NTTFast.Packed.Native (encodeFields)

local notation "F" => _root_.KoalaBear.Fast.Field
local notation "EF" => _root_.KoalaBear.Fast.Ext4

/-- The example AIRs by their names in `compstark-bench fingerprint`, for `2 ^ logN` rows. -/
def airs (logN : Nat) : List (String × Air F) :=
  [("fibonacci", fibonacci), ("cube", cube), ("square", square), ("wide", wide 64),
    ("mul-fib", mulFib logN true), ("mul-fib0", mulFib logN false),
    ("periodic", periodicAir [[(1 : Nat), (2 : Nat), (3 : Nat), (4 : Nat)],
      [(10 : Nat), (20 : Nat)]]),
    ("periodic-cube", periodicCube), ("keccak", CompStark.Fixtures.Keccak.air),
    ("wide-bus", wideBus 64), ("range-table", rangeTable logN), ("range-query", rangeQuery),
    ("single-table-local", singleTableLocalLookup),
    ("mul-lookups", mulAirLookups 2 true ["MulFib1", "MulFib2"])]

/-- The first line where two reports differ, if any. -/
def firstDifference (a b : String) : Option (Nat × String × String) :=
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  ((la.zip lb).zipIdx.find? fun ((x, y), _) ↦ x != y).map (fun ((x, y), i) ↦ (i + 1, x, y)) <|>
    if la.length = lb.length then none else some (min la.length lb.length, "", "")

/-- Every example AIR's fingerprint report is Plonky3's. -/
def fingerprints : IO Unit := do
  let logN := 4
  for (name, A) in airs logN do
    let expected ← IO.FS.readFile s!"tests/data/fingerprint/{name}_{logN}.json"
    match firstDifference (A.fingerprint EF logN).2 expected with
    | none => pure ()
    | some (line, ours, theirs) =>
      throw (IO.userError
        s!"fingerprint of {name} differs at line {line}:\n  lean   {ours}\n  plonky3 {theirs}")

/-- The configuration of Plonky3's example: blowup `2`, a constant final polynomial, arity up to
`8`, 87 queries, query and batching grinding of `16` and `10` bits, caps of height `3`. -/
def exampleParams : Fri.Params where
  logBlowup := 1
  logFinalPolyLen := 0
  maxLogArity := 3
  numQueries := 87
  commitPowBits := 0
  queryPowBits := 16
  batchPowBits := 10
  capHeight := 3

/-- Plonky3's trace of its example proof, row-major, from one row of canonical values per line. -/
def exampleTrace : IO (Array F) := do
  let lines := (← IO.FS.readFile "tests/data/keccak_example_6_trace.txt").splitOn "\n"
    |>.filter (· ≠ "")
  return (lines.toArray.map fun l ↦ (l.splitOn " ").toArray.map fun x ↦ (x.toNat! : F)).flatten

/-- Plonky3's example proof verifies with the example's Poseidon2 constants, by the fast verifier
too, which rejects it with an opened value changed, and both provers reproduce it from Plonky3's
trace. -/
def plonky3Example : IO Unit :=
  let I := CompStark.Fixtures.Poseidon2Example.instances
  letI := I.field
  letI := I.packed
  do
  let A : Air F := CompStark.Fixtures.Keccak.air
  let logN := 6
  let P := exampleParams
  let trace ← exampleTrace
  unless trace.size = 2 ^ logN * A.width do
    throw (IO.userError s!"example trace: {trace.size} values")
  let chunks := (Array.range 4).map fun k ↦ encodeFields
    (trace.extract (k * 16 * A.width) ((k + 1) * 16 * A.width))
  let rust : Proof F EF ← IO.ofExcept (Json.parse (p := _root_.KoalaBear.fieldSize)
    (← IO.FS.readFile "tests/data/keccak_example_6.json"))
  unless rust.traceCommit.size = 8 do
    throw (IO.userError s!"example proof: a trace cap of {rust.traceCommit.size} digests")
  match verify P A (setup P A logN) rust [] with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"example proof rejected: {e}")
  unless (I.verifyFast P A (setup P A logN) rust []).isOk do
    throw (IO.userError "the fast verifier rejects the example proof")
  let tampered := { rust with opened.traceLocal := rust.opened.traceLocal.modify 0 (· + 1) }
  if (I.verifyFast P A (setup P A logN) tampered []).isOk then
    throw (IO.userError "the fast verifier accepts a tampered example proof")
  let K := CompStark.Fixtures.KeccakKernel.kernel
  unless K.kernel.code == K.prog.code && decide (K.cs = A.constraints) do
    throw (IO.userError "the generated kernel's code is not the Keccak AIR's program")
  let B := Stark.Fast.backendFor [CompStark.Fixtures.KeccakKernel.kernel] P.logBlowup
    [(logN, A.logQuotientChunks logN)]
  unless proveWith B P A logN chunks [] == rust do
    throw (IO.userError "the fast prover does not reproduce the example proof")
  unless prove EF P A logN trace [] == rust do
    throw (IO.userError "the specification prover does not reproduce the example proof")

end CompStarkTests.Keccak
