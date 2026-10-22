/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Air
public import CompStark.Stark.Challenge
public import CompStark.Plonky3.Hash

/-! # AIR fingerprints

A fingerprint identifies an AIR across implementations, here and in Plonky3 (`bench/rust`,
`compstark-bench fingerprint`): it evaluates every constraint and every lookup at one random
point of the extension field and hashes the values with the shape of the AIR. Two AIRs whose
constraints differ as polynomials of degree at most `D` agree at the point with probability at
most `D / |EF|`, about `2 ^ -120` over the quartic extension of a 31-bit field. The report lists
the values constraint by constraint, so that a mismatch points at the constraint.

The point's coordinates are drawn from SplitMix64 seeded with `"AIR_FP_2"`, each `u64` reduced
modulo `p`, `d` draws per extension element, lowest coordinate first, in the order: the current
and the next row of the trace, the current and the next row of the preprocessed trace, the public
values, the periodic columns, and the first-row, last-row and transition selectors. Rows are drawn
at full width whether or not the AIR reads them.

The hashed stream (`stream`), base elements, is:

* the header `2, logN, width, preprocessedWidth, numPublicValues, #periodic, mainNextRow,
  opensPreprocessedNext, #constraints, logQuotientChunks logN, #lookups`;
* the coordinates of every constraint's value, in order;
* per lookup: `0` for a local one, or `1`, the bus name's length and its UTF-8 bytes for a global
  one; the number of tuples; per tuple its width and weight, the coordinates of its elements'
  values and of its multiplicity's. A global lookup counts as one lookup per tuple, as Plonky3
  emits them (`lookupsByTuple`), since only a local lookup's grouping of tuples matters;
* per periodic column its length and values;
* the digest of the preprocessed trace's values (`Hash.Poseidon2.hash`), if it has columns.

The fingerprint is the digest of the stream by Plonky3's Poseidon2 sponge
(`Hash.Poseidon2.hash`).
-/

@[expose] public section
namespace CompStark.Stark

/-- SplitMix64: the next state and the output. -/
def splitMix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (s, z ^^^ (z >>> 31))

namespace Fingerprint

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The seed, `"AIR_FP_2"` as a big-endian `u64`. -/
def seed : UInt64 := 0x4149525f46505f32

/-- `n` base elements of SplitMix64 from state `s`, each output reduced modulo `p`, and the state
after them. -/
def draws (n : Nat) (s : UInt64) : List F × UInt64 := Id.run do
  let mut s := s
  let mut out := #[]
  for _ in [0:n] do
    let (s', z) := splitMix s
    s := s'
    out := out.push (CompPoly.CanonicalNat.ofNat z.toNat : F)
  return (out.toList, s)

/-- `n` extension elements from state `s`, `d` draws each, lowest coordinate first. -/
def points (EF : Type) [Challenge F EF] (n : Nat) (s : UInt64) : Array EF × UInt64 :=
  let d := Challenge.d EF
  let (xs, s) := draws (F := F) (d * n) s
  ((Array.range n).map fun i ↦ Challenge.ofCoeffs ((xs.drop (d * i)).take d), s)

/-- The random point of an AIR: the environment its constraints are evaluated in. -/
def env (A : Air F) (EF : Type) [Challenge F EF] : Expr.Env F EF :=
  let (cur, s) := points EF A.width seed
  let (next, s) := points EF A.width s
  let (prepCur, s) := points EF A.preprocessedWidth s
  let (prepNext, s) := points EF A.preprocessedWidth s
  let (pub, s) := points EF A.numPublicValues s
  let (periodic, s) := points EF A.periodic.length s
  let (sel, _) := points EF 3 s
  { cur := (cur.getD · 0)
    next := (next.getD · 0)
    prepCur := (prepCur.getD · 0)
    prepNext := (prepNext.getD · 0)
    periodic := (periodic.getD · 0)
    pub := (pub.getD · 0)
    const := Ext.ofBase
    isFirstRow := sel.getD 0 0
    isLastRow := sel.getD 1 0
    isTransition := sel.getD 2 0 }

/-- The lookups of `A` as Plonky3 emits them: every global lookup one per tuple. -/
def lookupsByTuple (A : Air F) : List (Lookup F) :=
  A.lookups.flatMap fun l ↦ match l.bus with
    | none => [l]
    | some b => l.entries.map fun e ↦ ⟨some b, [e]⟩

/-- A natural number as a base element. -/
def num (n : Nat) : F := CompPoly.CanonicalNat.ofNat n

/-- The header of the stream. -/
def header (A : Air F) (logN : Nat) : List Nat :=
  [2, logN, A.width, A.preprocessedWidth, A.numPublicValues, A.periodic.length,
    if A.mainNextRow then 1 else 0, if A.opensPreprocessedNext then 1 else 0,
    A.constraints.length, A.logQuotientChunks logN, (lookupsByTuple A).length]

/-- A lookup's tuples evaluated at the point: weight, elements' values and multiplicity's value. -/
def tupleValues (E : Expr.Env F EF) (l : Lookup F) : List (Nat × List EF × EF) :=
  l.entries.map fun (es, c) ↦ (c.weight, es.map (Expr.eval E), c.expr.eval E)

/-- A bus name's UTF-8 bytes. -/
def busBytes (name : String) : List Nat := name.toUTF8.toList.map (·.toNat)

/-- The stream of a lookup. -/
def lookupStream (E : Expr.Env F EF) (l : Lookup F) : List F :=
  (match l.bus with
    | none => [num 0]
    | some b => num 1 :: num (busBytes b).length :: (busBytes b).map num) ++
  num l.entries.length :: (tupleValues E l).flatMap fun (w, es, c) ↦
    num es.length :: num w :: es.flatMap Ext.coeffs ++ Ext.coeffs c

/-- The digest of the preprocessed trace's values, if it has columns. -/
def preprocessedDigest [Poseidon2Field F] (A : Air F) : Option (Vector F 8) :=
  if A.preprocessedWidth = 0 then none else some (Hash.Poseidon2.hash F A.preprocessed.toList)

/-- The fingerprint's stream of `A` for a trace of `2 ^ logN` rows, with the constraints' values
at the point. -/
def stream [Poseidon2Field F] (A : Air F) (logN : Nat) (E : Expr.Env F EF)
    (values : List EF) : List F :=
  (header A logN).map num ++ values.flatMap Ext.coeffs ++ (lookupsByTuple A).flatMap (lookupStream E) ++
    A.periodic.flatMap (fun c ↦ num c.length :: c) ++
    ((preprocessedDigest A).map Vector.toList).getD []

/-- A canonical value as JSON. -/
def nat (x : F) : String := toString (CompPoly.CanonicalNat.toNat x)

/-- A JSON array of strings, on one line. -/
def jsonList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

/-- A JSON array of strings, one per line. -/
def jsonLines (xs : List String) : String :=
  if xs.isEmpty then "[]" else "[\n" ++ ",\n".intercalate xs ++ "\n]"

/-- An extension element as the JSON array of its coordinates. -/
def extJson (x : EF) : String := jsonList ((Ext.coeffs x).map nat)

/-- A lookup at the point as JSON. -/
def lookupJson (E : Expr.Env F EF) (l : Lookup F) : String :=
  let bus := match l.bus with
    | none => "null"
    | some b => "\"" ++ b ++ "\""
  "{\"bus\":" ++ bus ++ ",\"tuples\":" ++ jsonList ((tupleValues E l).map fun (w, es, c) ↦
    "{\"weight\":" ++ toString w ++ ",\"fields\":" ++ jsonList (es.map extJson) ++
      ",\"count\":" ++ extJson c ++ "}") ++ "}"

end Fingerprint

open Fingerprint in
/-- The fingerprint of `A` for a trace of `2 ^ logN` rows over the challenge field `EF`, and its
report: the header, every constraint's value, every lookup's values, the periodic columns, the
preprocessed trace's digest and the fingerprint, as JSON, one constraint and one lookup per
line. -/
def Air.fingerprint {F : Type} [BaseField F] [Poseidon2Field F] (EF : Type) [Challenge F EF]
    (A : Air F) (logN : Nat) : Vector F 8 × String :=
  let E := env A EF
  let values := A.constraints.map (Expr.eval E)
  let digest := Hash.Poseidon2.hash F (stream A logN E values)
  let report := "{\"fingerprint\":2,\n\"header\":" ++
    jsonList ((header A logN).map toString) ++ ",\n\"constraints\":" ++
    jsonLines (values.map extJson) ++ ",\n\"lookups\":" ++
    jsonLines ((lookupsByTuple A).map (lookupJson E)) ++ ",\n\"periodic\":" ++
    jsonList (A.periodic.map fun c ↦ jsonList (c.map nat)) ++ ",\n\"preprocessed\":" ++
    ((preprocessedDigest A).map fun d ↦ jsonList (d.toList.map nat)).getD "null" ++
    ",\n\"digest\":" ++ jsonList (digest.toList.map nat) ++ "}\n"
  (digest, report)

end CompStark.Stark
