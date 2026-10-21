/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Challenge
public import VCVio.Algorithms.Keccak

/-! # Domain separators

Plonky3's typed Fiat–Shamir layer (`p3_challenger::fs`) seeds the challenger at the start of each
sub-protocol, the STARK, its polynomial commitment scheme and FRI, with a domain separator: the
protocol's name and version, the Keccak-256 hash of its interaction pattern, and an instance
label of numbers that fix the run's shape. The challenger observes the seed's bytes as base
elements, the byte count first, then little-endian chunks of `⌊(log₂ p) / 8⌋` bytes (`seed`).

The pattern is the list of the protocol's steps (`Step`), each rendered as Plonky3's alternate
`Display` does: hierarchy, kind, label length and label, length, and type tag, one numbered and
indented line per step (`render`). The type tag of a field element names its field by the modulus,
the degree and the Keccak-256 hash of the algebra's identity (`Challenge.algebraId`).

`starkSeed`, `pcsSeed` and `friSeed` are the seeds of `p3-uni-stark`, `p3-fri-pcs` and `p3-fri`
(`StarkShape`, `PcsShape`, `FriShape`), and `batchSeed` that of `p3-batch-stark` (`BatchShape`),
here without zero knowledge or lookups.
-/

@[expose] public section
namespace CompStark.DomainSeparator

/-- Where a step sits: a single interaction, or the start or end of a nested sub-protocol. -/
inductive Hierarchy | atomic | begin | close

/-- What a step does. -/
inductive Kind | protocol | publicValue | message | challenge | pow

/-- How many values a step carries. -/
inductive Length | none | scalar | fixed (n : Nat)

/-- The type of a step's values: a marker, a commitment, elements of the algebra of degree
`degree` over the prime field of `modulus` with the identity `id`, or indices of `width` bits. -/
inductive Tag | marker | opaque | algebra (modulus degree : Nat) (id : String) | bits (width : Nat)

/-- One step of an interaction pattern. -/
structure Step where
  hierarchy : Hierarchy
  kind : Kind
  label : String
  length : Length
  tag : Tag

/-- Two lowercase hexadecimal digits per byte. -/
def hex (b : ByteArray) : String :=
  b.foldl (fun s x ↦ s ++ String.ofList (Nat.toDigits 16 (x.toNat / 16) ++
    Nat.toDigits 16 (x.toNat % 16))) ""

/-- Keccak-256 of a string's bytes. -/
def keccak (s : String) : ByteArray := VCVio.Algorithms.Keccak.keccak256 s.toUTF8

def Hierarchy.render : Hierarchy → String
  | .atomic => "Atomic" | .begin => "Begin" | .close => "End"

def Kind.render : Kind → String
  | .protocol => "Protocol" | .publicValue => "Public" | .message => "Message"
  | .challenge => "Challenge" | .pow => "Pow"

def Length.render : Length → String
  | .none => "None" | .scalar => "Scalar" | .fixed n => s!"Fixed({n})"

def Tag.render : Tag → String
  | .marker => "Marker"
  | .opaque => "Opaque"
  | .algebra p d id => s!"Algebra({p}^{d};{hex (keccak id)})"
  | .bits w => s!"Bits({w})"

/-- A step as Plonky3 renders it in a pattern. -/
def Step.render (s : Step) : String :=
  s!"{s.hierarchy.render} {s.kind.render} {s.label.utf8ByteSize} {s.label} {s.length.render} " ++
    s.tag.render

/-- The pattern's rendering: a header, then each step numbered with as many digits as the last
index, indented by its nesting. -/
def render (steps : List Step) : String := Id.run do
  let n := steps.length
  let digits := (toString (n - 1)).length
  let mut out := s!"Plonky3 Fiat-Shamir Transcript ({n} interactions)\n"
  let mut depth := 0
  for (s, i) in steps.zipIdx do
    if s.hierarchy matches .close then depth := depth - 1
    let pos := toString i
    out := out ++ "".pushn '0' (digits - pos.length) ++ pos ++ " " ++ "".pushn ' ' (2 * depth) ++
      s.render ++ "\n"
    if s.hierarchy matches .begin then depth := depth + 1
  return out

/-- `n` in `k` big-endian bytes. -/
def bigEndian (k n : Nat) : List UInt8 := (List.range k).reverse.map fun i ↦ (n / 256 ^ i).toUInt8

/-- The seed bytes: the protocol identity (the version, the name, its length in the last of 64
bytes), the pattern's hash, and the instance label of the numbers `inst`, each eight big-endian
bytes after its own length, then the domain tag `0x80`. -/
def seedBytes (version : Nat) (name : String) (steps : List Step) (inst : List Nat) :
    List UInt8 :=
  let nameBytes := name.toUTF8.toList
  let protocolId := version.toUInt8 :: nameBytes ++ List.replicate (62 - nameBytes.length) 0 ++
    [nameBytes.length.toUInt8]
  let label := inst.flatMap fun n ↦ bigEndian 4 8 ++ bigEndian 8 n
  protocolId ++ (keccak (render steps)).toList ++ bigEndian 4 label.length ++ label ++ [0x80]

/-- Consecutive chunks of `k > 0` bytes, the last one possibly shorter. -/
def chunks (k : Nat) (bs : List UInt8) : List (List UInt8) :=
  go bs.length bs
where
  go : Nat → List UInt8 → List (List UInt8)
    | 0, _ | _, [] => []
    | fuel + 1, bs => bs.take k :: go fuel (bs.drop k)

/-- The base elements a challenger over `F` observes for the bytes `bs`: their number, then
little-endian chunks of `⌊(log₂ p) / 8⌋` bytes, `p = |F|`. -/
def toElems (F : Type) [BaseField F] (bs : List UInt8) : List F :=
  let k := Nat.log2 (CompPoly.CanonicalNat.bound F) / 8
  ((bs.length : Nat) : F) :: (chunks k bs).map fun c ↦
    ((c.zipIdx.foldl (fun acc (b, i) ↦ acc + b.toNat * 256 ^ i) 0 : Nat) : F)

variable (F : Type) [BaseField F] (EF : Type) [Challenge F EF]

/-- The type tag of base elements. -/
def baseTag : Tag := .algebra (CompPoly.CanonicalNat.bound F) 1 "p3-scalar-basis-v1"

/-- The type tag of extension elements. -/
def extTag : Tag :=
  .algebra (CompPoly.CanonicalNat.bound F) (Challenge.d EF) (Challenge.algebraId (F := F) EF)

/-- A commitment. -/
def commitment (label : String) : Step := ⟨.atomic, .message, label, .scalar, .opaque⟩

/-- A grinding step of `bits` bits. -/
def powStep (label : String) (bits : Nat) : Step := ⟨.atomic, .pow, label, .fixed bits, baseTag F⟩

/-- A grinding step of `bits` bits, absent at zero difficulty. -/
def pow (label : String) (bits : Nat) : List Step :=
  if bits = 0 then [] else [powStep F label bits]

/-- An extension challenge. -/
def challenge (label : String) : Step := ⟨.atomic, .challenge, label, .scalar, extTag F EF⟩

/-- A delegated sub-protocol. -/
def bracket (label : String) : List Step :=
  [⟨.begin, .protocol, label, .none, .marker⟩, ⟨.close, .protocol, label, .none, .marker⟩]

/-- The seed of `p3-uni-stark` for a trace of `2 ^ logDegree` rows and `width` columns, a
preprocessed trace of `prepWidth` columns, committed if there are any, `numPeriodic` periodic
columns, `numPublic` public values, `chunks` quotient chunks and `oodBits` bits of out-of-domain
grinding; the trace is opened at the next row if `mainNext`, the preprocessed trace if
`prepNext`. -/
def starkSeed (logDegree width prepWidth numPeriodic numPublic chunks oodBits : Nat)
    (mainNext prepNext : Bool) : List F :=
  toElems F <| seedBytes 1 "p3-uni-stark"
    ([commitment "trace_commitment"] ++
      (if prepWidth = 0 then [] else [commitment "preprocessed_commitment"]) ++
      [⟨.atomic, .publicValue, "public_values", .fixed numPublic, baseTag F⟩,
      challenge F EF "alpha",
      commitment "quotient_commitment"] ++ pow F "ood_pow" oodBits ++
      [challenge F EF "zeta"] ++ bracket "opening_argument")
    [logDegree, logDegree, width, prepWidth, numPeriodic, chunks, if mainNext then 1 else 0,
      if prepNext then 1 else 0]

/-- The seed of `p3-fri-pcs` for claimed evaluations of `counts[c][m][k]` elements at the `k`-th
point of matrix `m` of commitment `c`, and `batchBits` bits of grinding before the batching
challenge. -/
def pcsSeed (counts : List (List (List Nat))) (batchBits : Nat) : List F :=
  toElems F <| seedBytes 1 "p3-fri-pcs"
    (counts.flatten.flatten.map (fun w ↦
        ⟨.atomic, .message, "claimed_evaluations", .fixed w, extTag F EF⟩) ++
      pow F "batch_pow" batchBits ++ [challenge F EF "alpha"] ++ bracket "low_degree_test")
    (counts.length :: counts.flatMap fun c ↦ c.length :: c.map List.length)

/-- The seed of `p3-fri` for folds of log arities `arities`, a final polynomial of `finalLen`
coefficients, `commitBits` and `queryBits` bits of grinding, `numQueries` queries of
`indexBits` bits, a blowup of `2 ^ logBlowup` and a largest log arity `maxLogArity`. -/
def friSeed (arities : List Nat) (finalLen commitBits queryBits numQueries indexBits logBlowup
    maxLogArity : Nat) : List F :=
  toElems F <| seedBytes 1 "p3-fri"
    (arities.flatMap (fun _ ↦ [commitment "commit_phase_commitment"] ++
        pow F "commit_pow" commitBits ++ [challenge F EF "fold_challenge"]) ++
      [⟨.atomic, .message, "final_poly", .fixed finalLen, extTag F EF⟩] ++
      pow F "query_pow" queryBits ++
      [⟨.atomic, .challenge, "query_indices", .fixed numQueries, .bits indexBits⟩])
    (logBlowup :: maxLogArity :: arities)

/-- The seed of `p3-batch-stark` for instances of trace widths `widths`, preprocessed widths
`prepWidths` and `numPublic` public values, with a commitment to the preprocessed traces if
`hasPrep`, `lookupInstances` instances with lookups, `lookupBits` bits of grinding before the
lookup challenges and `oodBits` bits of out-of-domain grinding. Every instance's degree bits and
every lookup terminal are an extension message, and the grinding steps are present at zero
difficulty too. -/
def batchSeed (widths prepWidths numPublic : List Nat) (hasPrep : Bool)
    (lookupInstances lookupBits oodBits : Nat) : List F :=
  toElems F <| seedBytes 1 "p3-batch-stark"
    (widths.map (fun _ ↦ ⟨.atomic, .message, "degree_bits", .scalar, extTag F EF⟩) ++
      [commitment "main_commitment"] ++
      numPublic.map (fun k ↦ ⟨.atomic, .publicValue, "public_values", .fixed k, baseTag F⟩) ++
      (if hasPrep then [commitment "preprocessed_commitment"] else []) ++
      (if lookupInstances = 0 then [] else
        [powStep F "lookup_pow" lookupBits, challenge F EF "lookup_alpha",
          challenge F EF "lookup_beta", commitment "permutation_commitment"] ++
        List.replicate lookupInstances
          ⟨.atomic, .message, "lookup_terminal", .scalar, extTag F EF⟩) ++
      [challenge F EF "constraint_challenge", commitment "quotient_commitment",
        powStep F "ood_pow" oodBits, challenge F EF "zeta"] ++ bracket "opening_argument")
    (widths.length :: widths ++ prepWidths)

end CompStark.DomainSeparator
