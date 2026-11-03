/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.BabyBear.Poseidon2
import CompStark.BabyBear.Challenge
import CompStark.Plonky3.Prover
import CompStark.Mont32.Json

/-! # BabyBear known answers

Plonky3 over BabyBear (`bench/rust: RAYON_NUM_THREADS=1 compstark-bench babybear`): the default
Poseidon2 permutations `default_babybear_poseidon2_16` and `_24` against the specification, and the
traces of the `uni-stark` proofs over BabyBear that the compiled tests check
(`tests/CompStarkNativeTests.lean`), where the Merkle sponge and compression, the challenger and
the proofs run on BabyBear's packed kernels. `periodic`, `periodic-tiny` and `pcube` have periodic
columns; `square` does not read the next row.
-/

namespace CompStarkTests.BabyBear
open CompStark CompStark.Stark

local notation "F" => _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

def canon (x : F) : Nat := Montgomery.Native32.FastField.toNat x

/-- The width-16 specification on the Montgomery field, as canonical outputs. -/
def perm16 (x : Vector Nat 16) : Vector Nat 16 :=
  (Poseidon2.permute (Poseidon2.BabyBear.width16 F) (x.map Nat.cast)).map canon

/-- The width-24 specification on the Montgomery field, as canonical outputs. -/
def perm24 (x : Vector Nat 24) : Vector Nat 24 :=
  (Poseidon2.permute (Poseidon2.BabyBear.width24 F) (x.map Nat.cast)).map canon

#guard perm16 (Vector.replicate 16 0) == #v[1168947398, 128782440, 747404447, 883925857, 360581875,
  1704698758, 1878363991, 1054281681, 682225194, 705839125, 1218819873, 41544645, 1095344608,
  174996601, 1678438226, 11259290]

#guard perm16 (Vector.ofFn (·.val)) == #v[1906786279, 1737026427, 1959749225, 700325316,
  1638050605, 1021608788, 1726691001, 1761127344, 1552405120, 417318995, 36799261, 1215172152,
  614923223, 1300746575, 957311597, 304856115]

#guard perm16 #v[894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
    120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
    1783754913] == #v[516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026,
  1788910906, 563338433, 319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758,
  1052633829, 1344246938]

#guard perm24 (Vector.replicate 24 0) == #v[400117224, 993058517, 1143686568, 167077231, 512027304,
  1699297555, 73036051, 384892923, 1638785080, 1986004076, 962251114, 1342022841, 237647043,
  599501300, 1325347421, 758164838, 909746918, 1857572136, 456675026, 284439419, 1688929831,
  43577996, 781522191, 999813579]

#guard perm24 (Vector.ofFn (·.val)) == #v[57973606, 1742549659, 409441332, 409968379, 1588522739,
  1235046754, 142170282, 1876178281, 428001087, 602964561, 1634659810, 1459495659, 1386997552,
  559996597, 1579968629, 971061809, 169813032, 163759111, 57819583, 648482598, 838234366,
  112505394, 245852421, 766005377]

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

/-- Plonky3's periods of `PeriodicAir`, and those of its tiny-quotient test. -/
def periodicCols : List (List F) := [[1, 2, 3, 4], [10, 20]]
def periodicTinyCols : List (List F) := [[9], [1, 2]]

/-- The proof with its first opened trace value changed. -/
def tamper (proof : Proof F EF) : Proof F EF :=
  { proof with opened := { proof.opened with
      traceLocal := proof.opened.traceLocal.modify 0 (· + 1) } }

end CompStarkTests.BabyBear
