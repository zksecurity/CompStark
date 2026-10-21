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
Poseidon2 permutations `default_babybear_poseidon2_16` and `_24`, the Merkle sponge and
compression on them, and the challenger `DuplexChallenger<BabyBear, Poseidon2BabyBear<24>, 24, 16>`
on the sequence of `CompStarkTests.Challenger`. Then `uni-stark` proofs over BabyBear with the
quartic extension (`compstark-bench stark-babybear AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY
QUERIES COMMIT_POW QUERY_POW`), saved as `tests/data/babybear_AIR_*.json`: each must verify, the
Lean prover must reproduce it exactly, and the verifier must reject it with a changed opened value.
-/

namespace CompStarkTests.BabyBear
open CompStark CompStark.Stark

local notation "F" => _root_.BabyBear.Fast.Field
local notation "EF" => _root_.BabyBear.Fast.Ext4

def canon (x : F) : Nat := Montgomery.Native32.FastField.toNat x

def perm16 (x : Vector Nat 16) : Vector Nat 16 :=
  ((@Poseidon2Field.perm16 F _ _).perm (x.map Nat.cast)).map canon

def perm24 (x : Vector Nat 24) : Vector Nat 24 :=
  ((@Poseidon2Field.perm24 F _ _).perm (x.map Nat.cast)).map canon

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

/-- The leaf hash of `0, …, n - 1`, as canonical outputs. -/
def hashIota (n : Nat) : Vector Nat 8 :=
  (Hash.Poseidon2.hash F ((List.range n).map Nat.cast)).map canon

#guard hashIota 0 == #v[0, 0, 0, 0, 0, 0, 0, 0]
#guard hashIota 17 == #v[1875502830, 974397544, 704688170, 1883141588, 1041265242, 1629291250,
  320604243, 1355043471]
#guard hashIota 50 == #v[399795265, 1943283828, 1079297912, 1957627797, 1004533225, 1719359129,
  725623019, 1932653308]

#guard (Hash.Poseidon2.compress F (Vector.ofFn fun i ↦ (i.val : _))
    (Vector.ofFn fun i ↦ ((100 + i.val : Nat) : _))).map canon ==
  #v[1530764323, 683220462, 336738649, 272658290, 1124681686, 416762908, 1018721039, 1796156880]

/-- The challenger sequence of `CompStarkTests.Challenger`. -/
def challengerRun : List Nat :=
  let c := (List.range 20).foldl (fun c i ↦ Transcript.observe c (i : F)) Poseidon2.initTranscript
  let (a, c) := c.sample
  let (b, c) := c.sample
  let (e, c) := (c.sampleExt : EF × Transcript F 24)
  let c := (c.observe 7).observeExt (⟨100, 101, 102, 103⟩ : EF)
  let (bits, c) := c.sampleBits 10
  let (w, c) := c.grind 6
  let (z, _) := c.sample
  [canon a, canon b, canon e.c0, canon e.c1, canon e.c2, canon e.c3, bits, canon w, canon z]

#guard challengerRun == [1136121201, 999034627, 1736188539, 573305400, 1322564753, 481613251, 227,
  139, 1612444506]

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

/-- The proof with its first opened trace value changed. -/
def tamper (proof : Proof F EF) : Proof F EF :=
  { proof with opened := { proof.opened with
      traceLocal := proof.opened.traceLocal.modify 0 (· + 1) } }

/-- Verify, reproduce and reject when tampered the saved proof of `air` for parameters `logN
logBlowup logFinal maxLogArity queries commitPow queryPow [batchPow oodPow]`. -/
def check (name : String) (A : Air F) (inst : Nat → Array F × List F) (ps : List Nat) : IO Unit :=
    do
  let (logN, P) ← match ps with
    | [logN, b, f, a, q, cp, qp] => pure (logN, (⟨b, f, a, q, cp, qp, 0, 0⟩ : Fri.Params))
    | [logN, b, f, a, q, cp, qp, bp, op] => pure (logN, ⟨b, f, a, q, cp, qp, bp, op⟩)
    | _ => throw (IO.userError "seven or nine parameters")
  let file := s!"babybear_{name}_{"_".intercalate (ps.map toString)}"
  let rust : Proof F EF ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"tests/data/{file}.json"))
  let (trace, pis) := inst (2 ^ logN)
  if let .error e := verify P A rust pis then throw (IO.userError s!"{file}: {e}")
  unless prove EF P A logN trace pis == rust do throw (IO.userError s!"{file}: proofs differ")
  if let .ok () := verify P A (tamper rust) pis then
    throw (IO.userError s!"{file}: accepted a tampered proof")

#eval do
  for ps in [[3, 2, 2, 1, 2, 0, 0], [6, 1, 1, 3, 8, 2, 4], [4, 1, 1, 2, 5, 1, 1, 3, 2]] do
    check "fib" fibonacci fibInstance ps
  check "cube" cube cubeInstance [5, 3, 1, 2, 6, 1, 3]

end CompStarkTests.BabyBear
