/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Plonky3.Prover
public import CompStark.Mont32.Challenge
public import CompStark.Poseidon2.PackedField
public import CompStark.Merkle.PackedColumns
public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompStark.Stark.Words
public import CompStark.Stark.ExtWords
public import CompStark.Stark.ProgWords
public import CompStark.Stark.ProgGroup

/-! # The fast prover backend

The kernels of `Backend` on packed Montgomery words, over a Montgomery field `FastField p` with its
domains (`Mont32BaseField`), the quartic extension `Ext4 p` (`Binomial4`), Plonky3's Poseidon2
(`Poseidon2Field`) on packed groups (`PackedPoseidon2`) and CompPoly's coset LDE kernels. Matrices
are packed column by column (`PMat`), in blocks of rows:

* The transcript is Plonky3's duplex challenger on the field's Poseidon2 implementation. Grinding
  tries eight candidates per packed permutation, as Plonky3 does, and returns the smallest that
  passes.
* Low-degree extension is CompPoly's batched coset LDE, every column extended by one task into its
  coset blocks (`ldeColumns`), which are the extension's blocks of columns.
* The Merkle digest layers come from the packed Merkle commitment: the tallest matrices' rows side
  by side are hashed from their columns, and the matrices of each smaller height are hashed
  likewise and injected into the layer of their height by one more packed compression.
* The LogUp kernels work on blocks of rows as base words or as planes of extension coordinates
  (`XVal`, keeping the cheapest kind through every operation). The permutation trace's fractions
  are computed block by block, every denominator inverted through the norm with one batch
  inversion per tuple, the rows written in parallel ranges of blocks and their accumulators
  shifted by the sums before them (`permutationWords`); its extension is CompPoly's coset LDE of
  those words. The LogUp constraints' quotient values are evaluated block by block in the
  extension's bit-reversed row order, as the AIR's, and accumulated in place with the powers of
  `α` (`lookupQuotientWith`).

The kernels compute the specification's functions on the shapes the prover gives them
(`Fri.Refines`): matrices of `2 ^ k` rows within the two-adic subgroups, addressable by machine
indices, and opening points outside the base field.

Every function is generic in the modulus. The compiler specializes it where a field instantiates
it, with the field's Montgomery constants as immediates; that module belongs to the CPU-targeted
native library.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri CompStark.Poseidon2 Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-- A matrix of base elements as packed Montgomery words, column by column in blocks of `rows`
rows: `cols[b * width + j]` holds column `j` on the rows `b · rows, …, b · rows + rows - 1`. -/
structure PMat where
  width : Nat
  height : Nat
  rows : Nat
  cols : Array ByteArray

/-- Column `j` of a packed matrix from row `r` on: its block's buffer, and the word of row `r`. -/
@[inline] def PMat.colAt (m : @& PMat) (j r : Nat) : ByteArray × Nat :=
  (m.cols.getD (r / m.rows * m.width + j) .empty, r % m.rows)

/-- A field element from a packed word. -/
def word (b : ByteArray) (i : Nat) : F :=
  CompPoly.CPolynomial.NTTFast.Packed.ofWord p (CompPoly.CPolynomial.NTTFast.Packed.Native.read b i)

/-- The first passing candidate of batch `b`, `8 b, …, 8 b + 7`: `group` holds eight copies of the
duplexed state as a packed group, and the candidates go into coordinate `wi`. -/
def grindBatch (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : @& ByteArray)
    (wi bits b : Nat) : Option Nat :=
  let W := (List.range 8).foldl (fun W l ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write W
    (8 * wi + l) ((8 * b + l : Nat) : FastField p).val)
    (group.copySlice 0 ByteArray.empty 0 group.size)
  let out := PackedPoseidon2.permute24 p W
  ((List.range 8).find? fun l ↦ 8 * b + l < p &&
    FastField.toNat (word (p := p) out (8 * 15 + l)) % 2 ^ bits == 0).map (8 * b + ·)

/-- The first passing candidate of the `nb` batches from `b`, if any. -/
def grindRange (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : @& ByteArray)
    (wi bits : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | nb + 1, b =>
    match grindBatch p group wi bits b with
    | some m => some m
    | none => grindRange p group wi bits nb (b + 1)

/-- The smallest passing candidate from wave `wave` on: each wave splits 1024 batches of eight
candidates among 16 tasks, and the first wave with a passing candidate has the smallest. -/
def grindWaves (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : ByteArray) (wi bits : Nat) :
    Nat → Nat → FastField p
  | 0, _ => 0
  | fuel + 1, wave =>
    let ts := (Array.range 16).map fun k ↦ Task.spawn fun _ ↦
      grindRange p group wi bits 64 (1024 * wave + 64 * k)
    match (ts.map Task.get).findSome? id with
    | some c => (c : FastField p)
    | none => grindWaves p group wi bits fuel (wave + 1)

/-- The coordinate of a grinding witness after the pending input `c.input`: its length, or 24,
past the group, if the input fills the rate, where the absorption drops the witness. -/
def witnessSlot (c : Challenger F 24) : Nat := if c.input.size < 16 then c.input.size else 24

/-- The smallest grinding witness for `bits`, eight candidates per packed permutation as Plonky3
grinds, in parallel waves: the state absorbing the input and a witness, with the candidates in
the witness's coordinate. -/
def grind [Poseidon2Field (FastField p)] [PackedPoseidon2 p] (c : Challenger F 24)
    (bits : Nat) : F :=
  let base := Challenger.absorbInto 16 c.state (c.input.push 0).toList
  let group := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := 192) fun k ↦ base.toArray.getD (k / 8) 0)
  grindWaves p group (witnessSlot c) bits (p / 8192 + 1) 0

/-- The fast transcript. -/
def transcript [Mont32BaseField p] [Poseidon2Field (FastField p)]
    [PackedPoseidon2 p] : Transcript F 24 :=
  Transcript.initWith Poseidon2.duplex grind

/-- The domain of order `2 ^ k` of the base field, `k ≤ twoAdicity`. -/
def domain [Mont32BaseField p] (k : Nat) (h : k ≤ twoAdicity F) :
    CompPoly.CPolynomial.NTT.Domain F :=
  ⟨k, twoAdicGen k, BaseField.isPrimitiveRoot_twoAdicGen k h⟩

/-- CompPoly's plan for extensions of `2 ^ logH`-row matrices by `2 ^ bits` onto `shift · ⟨ω_N⟩`,
`ω_N = twoAdicGen (logH + bits)`. -/
def plan? [Mont32BaseField p] (logH bits : Nat) (shift : F) : Option (LdePlan p) :=
  if h : logH + bits ≤ twoAdicity F then
    have h29 : logH + bits ≤ 29 := le_trans h (Mont32BaseField.twoAdicity_le_29 p)
    some (LdePlan.ofDomain (domain (logH + bits) h) bits
      (by change bits ≤ logH + bits; omega) shift (by change logH + bits ≤ 32; omega) (by
        have hp : 2 ^ (logH + bits) ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) h29
        have := USize.le_size
        change 4 * 2 ^ (logH + bits) < USize.size
        omega))
  else none

/-- The number of row ranges each of `chunks` input chunks of a `2 ^ logH`-row matrix splits into
for its transpose: ranges of 256 rows, whose transposed columns of 1 KiB keep the writes of a
range within few pages. -/
def lineRanges (logH chunks : Nat) : Nat := max 1 (2 ^ logH / chunks / 256)

open CompPoly.CPolynomial.NTTFast.Packed.Native (transposeRows columnCoefficients
  gatherColumn cosetBlock) in
/-- The extension by `P` of the `w`-column matrix whose rows are the chunks `ms` of equal heights,
column by column: block `t` of column `j`, the values on coset `bitrev t`, at `t * w + j`. Tasks
transpose row ranges of the chunks into columns (`lineRanges`); every column is one task, its
coefficients and then each of its coset blocks, the last one from the coefficients' buffer. -/
def ldeColumns (P : LdePlan p) (w : Nat) (ms : Array ByteArray) : Array ByteArray :=
  let q := lineRanges P.logH ms.size
  let rows := 2 ^ P.logH / (ms.size * q)
  let pieces := CompPoly.Tasks.join (CompPoly.Tasks.spawnAll (ms.size * q) fun k ↦
    transposeRows (ms.getD (k / q) .empty) w (k % q * rows) rows)
  let blocks := (CompPoly.Tasks.join ((Array.range w).map fun j ↦ pieces.bind fun ps ↦
    Task.spawn fun _ ↦
      let c := columnCoefficients P (gatherColumn ps rows j)
      (Array.range (2 ^ P.bits)).map fun t ↦ cosetBlock P c t)).get
  (Array.range (2 ^ P.bits)).flatMap fun t ↦ blocks.map fun b ↦ b.getD t .empty

/-- CompPoly's batched coset extension, bit-reversed rows, of a matrix given as chunks of packed
rows, as columns in blocks of the input's height (`ldeColumns`). Plans come from `plans` when one
matches, else are built; there is none beyond the two-adic subgroups. -/
def ldeWordsWith [Mont32BaseField p] (plans : List (Nat × Nat × F × LdePlan p))
    (logH bits : Nat) (shift : F) (w : Nat) (ms : Array ByteArray) : PMat :=
  let found := plans.find? fun (h, b, s, _) ↦ h == logH && b == bits && s == shift
  match found.map (·.2.2.2) <|> plan? logH bits shift with
  | some P => ⟨w, 2 ^ (logH + bits), 2 ^ logH, ldeColumns P w ms⟩
  | none => ⟨w, 0, 1, #[]⟩

/-- CompPoly's batched coset LDE, bit-reversed rows, packed: `ldeRef` on words. -/
def ldeWith [Mont32BaseField p] (plans : List (Nat × Nat × F × LdePlan p))
    (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) : PMat :=
  ldeWordsWith plans logH bits shift w #[CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields m]

/-- The extension without cached plans. -/
def lde [Mont32BaseField p] (logH bits : Nat) (shift : F) (w : Nat)
    (m : Array F) : PMat :=
  ldeWith [] logH bits shift w m

/-- The extension plans of a proof of a `2 ^ logN`-row trace and `2 ^ logChunks` quotient chunks:
the trace's extension on `g · ⟨ω_N⟩` and every chunk's. -/
def ldePlans [Mont32BaseField p] (logN logBlowup logChunks : Nat) : List
    (Nat × Nat × F × LdePlan p) :=
  let qlog := logN + logChunks
  let shifts : List F := gen :: (List.range (2 ^ logChunks)).map fun c ↦
    gen * (gen * powF (twoAdicGen qlog) c)⁻¹
  shifts.filterMap fun s ↦ (plan? logN logBlowup s).map fun P ↦ (logN, logBlowup, s, P)

/-- The columns of matrices side by side from row `r` on (`PMat.colAt`). -/
def colsList (ms : List PMat) (r : Nat) : List (ByteArray × Nat) :=
  ms.flatMap fun m ↦ (List.range m.width).map fun j ↦ m.colAt j r

/-- The padded leaf digests of the rows of matrices of height `h` side by side, and their number:
hashed from the matrices' columns by parallel tasks over ranges of at most 512 rows, each range
within one block of rows of every matrix. -/
def leafLayer (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (ms : List PMat) (h : Nat) : ByteArray × Nat :=
  let w := ms.foldl (· + ·.width) 0
  let size := ms.foldl (fun a m ↦ Nat.gcd a m.rows) 512
  let parts := h / size
  let first := (CompPoly.Tasks.spawnAll parts fun k ↦
    Merkle.Packed.hashColumns p ((colsList ms (k * size)).map (·.1)).toArray
      ((colsList ms (k * size)).map (·.2)).toArray w size).foldl (fun acc t ↦ acc ++ t.get)
      (ByteArray.emptyWithCapacity (32 * (h + 1)))
  let padded := if h = 1 then 1 else h + h % 2
  (Merkle.Packed.padDigests first h padded, padded)

/-- Digests `0, …, n - 1` of two layers interleaved: digest `i` of `a`, then digest `i` of `b`. -/
def interleaveDigests (a b : @& ByteArray) (n : Nat) : ByteArray :=
  (List.range n).foldl (fun out i ↦ out ++ a.extract (32 * i) (32 * i + 32) ++
    b.extract (32 * i) (32 * i + 32)) (ByteArray.emptyWithCapacity (64 * n))

/-- Digests as consecutive packed words. -/
def encodeDigests (ds : Array (Digest F)) : ByteArray :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (ds.flatMap (·.toArray))

/-- The layer above a layer of `n` digests with the matrices `inj` of height `n` injected:
digest `i` becomes the compression of digest `i` and the leaf digest of row `i` of `inj` side by
side, by the packed compression of the two layers interleaved. -/
def injectLayer (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (layer : ByteArray) (n : Nat) (inj : List PMat) : ByteArray :=
  if inj.isEmpty then layer else
    let (hs, _) := leafLayer p inj n
    (Merkle.Packed.nextLayer p (interleaveDigests layer hs n) (2 * n)).1

/-- `out` followed by at most `fuel` layers above `layer` of `n` digests, up to the root, with the
matrices of `rest`, tallest first, injected where their height is the layer's. -/
def upperMixed (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (rest : List PMat) (layer : ByteArray) (n : Nat) (out : Array ByteArray) :
    Nat → Array ByteArray
  | 0 => out
  | fuel + 1 =>
    if n ≤ 1 then out else
    let (l, n') := Merkle.Packed.nextLayer p layer n
    let inj := rest.takeWhile (·.height == n')
    let l := injectLayer p l n' inj
    upperMixed p (rest.drop inj.length) l n' (out.push l) fuel

/-- The packed digest layers of the Merkle tree of matrices of heights powers of two, leaves
first: the tallest matrices' rows side by side hashed, then every layer compressed, with the
matrices of its height injected (Plonky3's `MerkleTree::new`). -/
def commitLayers (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (ms : List PMat) : Array ByteArray :=
  let sorted := ms.mergeSort fun a b ↦ b.height ≤ a.height
  match sorted with
  | [] => #[]
  | m :: _ =>
    let tallest := sorted.takeWhile (·.height == m.height)
    let (first, n) := leafLayer p tallest m.height
    upperMixed p (sorted.drop tallest.length) first n #[first] n

/-- Packed matrices under one Merkle tree, with the packed digest layers, leaves first. -/
structure Commit where
  mats : List PMat
  layers : Array ByteArray

/-- Commit to packed matrices (`commitLayers`). -/
def commit (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (ms : List PMat) : Commit :=
  ⟨ms, commitLayers p ms⟩

namespace Commit

/-- The largest matrix height. -/
def maxHeight (c : Commit) : Nat := c.mats.foldl (fun m a ↦ max m a.height) 0

/-- Row `r` of a packed matrix, word by word from its columns. -/
def readRow (m : PMat) (r : Nat) : Array F :=
  Array.ofFn (n := m.width) fun j ↦ word (m.colAt j r).1 (m.colAt j r).2

/-- Digest `k` of a packed layer: its 32 bytes, copied out, whose word reads always fit. -/
def readDigest (b : ByteArray) (k : Nat) : Digest F :=
  let d := b.extract (32 * k) (32 * k + 32)
  Vector.ofFn fun j ↦ word d j.val

/-- The Merkle cap of height `h` (`Committed.cap`). -/
def cap (c : Commit) (h : Nat) : Cap F :=
  let levels := c.layers.size - 1
  let h := min h levels
  Array.ofFn (n := 2 ^ h) fun t ↦ readDigest (c.layers.getD (levels - h) .empty) t

/-- `Committed.openAt` on packed rows and layers. -/
def openAt (c : Commit) (index : Nat) : BatchOpening F :=
  let logMax := Merkle.log2Ceil c.maxHeight
  let rows := c.mats.map fun m ↦ readRow m (index >>> (logMax - Merkle.log2Ceil m.height))
  ⟨rows.toArray, Array.ofFn (n := logMax) fun i ↦
    readDigest (c.layers.getD i.val .empty) ((index >>> i.val) ^^^ 1)⟩

end Commit

/-- A packed matrix's columns for programs. -/
def PMat.toCols (m : PMat) : Prog.Cols := ⟨m.cols, m.width, m.rows⟩

/-- Rows `r0, …, r0 + B - 1` of a packed matrix, transposed: column `c` at words `c B`, copied from
the columns, word by word unless they lie in one block of rows. -/
def PMat.block (m : @& PMat) (r0 B : Nat) : ByteArray :=
  let out := ByteArray.emptyWithCapacity (4 * (m.width * B))
  if r0 % m.rows + B ≤ m.rows then
    Merkle.Packed.foldRange (fun out c ↦
      (m.colAt c r0).1.copySlice (4 * (m.colAt c r0).2) out out.size (4 * B)) m.width 0 out
  else
    Merkle.Packed.foldRange (fun out c ↦ Merkle.Packed.foldRange (fun out k ↦
      (m.colAt c (r0 + k)).1.copySlice (4 * (m.colAt c (r0 + k)).2) out out.size 4) B 0 out)
      m.width 0 out

/-- Whether the rows `next[r0], …, next[r0 + B - 1]` are consecutive. -/
def seqRows (next : @& Array Nat) (r0 B : Nat) : Bool :=
  (List.range B).all fun k ↦ next.getD (r0 + k) 0 == next.getD r0 0 + k

/-- The empty matrix. -/
def PMat.empty : PMat := ⟨0, 0, 1, #[]⟩

/-- The columns of a packed row-major matrix of width `w` and `n` rows, in one block. -/
def rowMajorCols (m : @& ByteArray) (w n : Nat) : Prog.Cols :=
  let t := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows m w 0 n
  ⟨(Array.range w).map fun j ↦ t.extract (4 * (j * n)) (4 * (j * n + n)), w, n⟩

/-- Words `i, …, i + B - 1` of `b`. -/
def slice (b : @& ByteArray) (i B : Nat) : ByteArray := b.extract (4 * i) (4 * (i + B))

/-- The rows `perm[i0], …, perm[i0 + len - 1]` of a packed row-major matrix of width `w`,
copied whole. -/
def permuteRange (m : @& ByteArray) (w : Nat) (perm : @& Array Nat) (i0 len : Nat) : ByteArray :=
  Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (len * w)
  for k in [0:len] do
    out := m.copySlice (4 * w * perm.getD (i0 + k) 0) out (4 * w * k) (4 * w)
  return out

/-- The rows `perm[0], perm[1], …` of a packed row-major matrix of width `w`, by parallel ranges. -/
def permuteWords (m : ByteArray) (w : Nat) (perm : Array Nat) : ByteArray :=
  let n := perm.size
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    permuteRange m w perm (k * size) (if k + 1 = parts then n - k * size else size)
  ts.foldl (fun acc t ↦ acc ++ t.get) (ByteArray.emptyWithCapacity (4 * n * w))

/-- The tables of the quotient on the quotient domain of a `2 ^ degreeBits`-row trace with
`2 ^ logChunks` chunks, rows in the extension's bit-reversed order: the order, the selectors, the
inverse vanishing polynomial (period `2 ^ logChunks`), the next rows, and per block of `B` rows
the first next row when the next rows form a block. They depend only on the shape. -/
structure QuotientTables (q : ℕ) [Mont32Field q] where
  degreeBits : Nat
  logChunks : Nat
  perm : Array Nat
  invZh : Array (FastField q)
  first : ByteArray
  last : ByteArray
  trans : ByteArray
  next : Array Nat
  B : Nat
  hB : 4 * B < USize.size

/-- The quotient tables of a shape. -/
def quotientTables [Mont32BaseField p] (degreeBits logChunks : Nat) : QuotientTables p :=
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let perm := bitRevPerm qlog
  let xs := cosetPoints gen qlog
  let gInv : F := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  let next := perm.map fun i ↦ perm.getD ((i + period) % n) 0
  let R := n / (if n < 4096 then 1 else 16)
  let B := min R 256
  { degreeBits, logChunks, perm, invZh := batchInv zhs, next, B
    hB := Nat.lt_of_lt_of_le (by omega) USize.le_size
    first := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      zhs.getD (i % period) 0 * invFirst.getD i 0)
    last := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      zhs.getD (i % period) 0 * invLast.getD i 0)
    trans := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (perm.map fun i ↦
      xs.getD i 0 - gInv) }

/-- Field elements hash by their words. -/
instance : Hashable F := ⟨fun x ↦ hash x.val⟩

/-- The powers `α ^ 0, …, α ^ (K - 1)`, by successive products. -/
def powerSeq [Mont32BaseField p] [Binomial4 p] (alpha : EF) (K : Nat) : Array EF :=
  ((List.range K).foldl (fun (acc, x) _ ↦ (acc.push x, x * alpha)) ((#[] : Array EF), 1)).1

/-- The weights `α ^ (K - 1 - k)` of `K` constraints, four coordinates each. -/
def weightCoords [Mont32BaseField p] [Binomial4 p] (alpha : EF) (K : Nat) : Array F :=
  let pw := powerSeq alpha K
  Array.ofFn (n := 4 * K) fun i ↦
    (Ext.coeffs (pw.getD (K - 1 - i.val / 4) 0)).getD (i.val % 4) 0

/-- The kernel of `kernels` with the program's code, if any. -/
def kernelFor (kernels : List (Prog.GroupKernel p)) (code : Array (Prog.Instr F)) :
    Option (Prog.GroupKernel p) :=
  kernels.find? fun k ↦ k.code == code

/-- A program on groups of rows: by its kernel `k?`, or interpreted. -/
def groupRun (k? : Option (Prog.GroupKernel p)) (code : Array (Prog.Instr F))
    (env : Prog.GroupEnv) (s : ByteArray) : ByteArray :=
  match k? with
  | some k => k.run env s
  | none => Prog.run (Prog.groupMachine p env) code s

/-- A group kernel generated for the program of the constraints `cs` (`Prog.compile`), with the
program. -/
structure AirKernel (q : ℕ) [Mont32Field q] where
  kernel : Prog.GroupKernel q
  cs : List (Expr (FastField q))
  prog : Prog (FastField q)
  prog_eq : prog = Prog.compile cs

/-- A kernel whose code is its program's. -/
abbrev CheckedKernel (q : ℕ) [Mont32Field q] := { k : AirKernel q // k.kernel.code = k.prog.code }

/-- The kernels of `kernels` whose code is their program's. -/
def checkedKernels (kernels : List (AirKernel p)) : List (CheckedKernel p) :=
  kernels.filterMap fun k ↦ if h : k.kernel.code = k.prog.code then some ⟨k, h⟩ else none

/-- The program of the constraints `cs` and its run on groups of rows: a checked kernel's for
`cs`, without compiling them, or compiled and run by a kernel with its code, or interpreted. -/
def progRun (ks : List (CheckedKernel p)) (cs : List (Expr F)) :
    Prog F × (Prog.GroupEnv → ByteArray → ByteArray) :=
  match ks.find? fun k ↦ decide (k.1.cs = cs) with
  | some k => (k.1.prog, k.1.kernel.run)
  | none =>
    let prog := Prog.compile cs
    (prog, groupRun (kernelFor (ks.map (·.1.kernel)) prog.code) prog.code)

/-- The values of a program accumulating every row of the quotient domain, in the extension's
bit-reversed order, put in natural order: the program runs on blocks of rows, `block r0` giving the
block from row `r0` its view and loads, in parallel ranges of blocks, each range with one state; on
blocks of a multiple of sixteen rows as one group (`run`, the program on the group machine), else
by `Prog.runBlock`. Every row's accumulators are its value's coordinates, times the inverse
vanishing polynomial. -/
def quotientBlocks [Mont32BaseField p] [Binomial4 p] (T : QuotientTables p) (prog : Prog F)
    (run : Prog.GroupEnv → ByteArray → ByteArray) (scal wts : Array F)
    (block : Nat → Prog.View × Prog.Loads) : Array EF := Id.run do
  let n := 2 ^ (T.degreeBits + T.logChunks)
  let period := 2 ^ T.logChunks
  let perm := T.perm
  let B := T.B
  let blocks := n / B
  let scalW := scal.map (·.val)
  let wtsW := wts.map (·.val)
  let byRow := parChunks blocks (min blocks 16) fun b0 nb ↦ Id.run do
    let mut out := Array.emptyWithCapacity (nb * B)
    if B % 16 = 0 ∧ 4 * (B * (4 + prog.regs)) < USize.size then
      let mut st := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (B * (4 + prog.regs))
      for blk in [b0:b0 + nb] do
        let r0 := blk * B
        let (v, L) := block r0
        let env := Prog.blockEnv B v L scalW wtsW
        st := run env (Prog.clearAccs B st)
        for i in [0:B] do
          out := out.push (Ext4.smul (T.invZh.getD (perm.getD (r0 + i) 0 % period) 0)
            ⟨word st i, word st (B + i), word st (2 * B + i), word st (3 * B + i)⟩)
    else
      let mut regs : Prog.Regs (4 * B) := Array.replicate (4 + prog.regs)
        ⟨CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B, ByteArray.size_zeros _⟩
      for blk in [b0:b0 + nb] do
        let r0 := blk * B
        let (v, L) := block r0
        regs := Prog.runBlock p prog.code v L scal wts B T.hB (Prog.clearAcc T.hB B regs)
        for i in [0:B] do
          out := out.push (Ext4.smul (T.invZh.getD (perm.getD (r0 + i) 0 % period) 0)
            ⟨word (Prog.regBuf regs 0) i, word (Prog.regBuf regs 1) i,
              word (Prog.regBuf regs 2) i, word (Prog.regBuf regs 3) i⟩)
    return out
  return perm.map fun r ↦ byRow.getD r 0

/-- The periodic columns of `A` on the quotient domain of the tables `T`, in the extension's
bit-reversed order, as words. -/
def periodicWords [Mont32BaseField p] (T : QuotientTables p) (A : Air F) : Array ByteArray :=
  (A.periodic.map fun col ↦
    let tab := periodicOnQuotient col T.degreeBits T.logChunks
    CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields (T.perm.map fun r ↦
      periodicRow tab r)).toArray

/-- `quotientOfLde` on packed words with the shape's tables `T`: the constraints' program
(`Prog.compile`, a checked kernel's of `ks` if there is one, `progRun`) on blocks of rows in the
extension's bit-reversed order (`quotientBlocks`), every block's rows of the extensions copied
from their columns, their next rows gathered. -/
def quotientWith [Mont32BaseField p] [Binomial4 p] (ks : List (CheckedKernel p))
    (T : QuotientTables p) (A : Air F) (pis : List F) (ext : PMat) (prep : Option PMat)
    (alpha : EF) : Array EF :=
  let pm := prep.getD PMat.empty
  let per := periodicWords T A
  let pr := progRun ks A.constraints
  quotientBlocks T pr.1 pr.2
    pis.toArray (weightCoords alpha A.constraints.length) fun r0 ↦
      (⟨ext.block r0 T.B, 0, T.B⟩,
        ⟨ext.toCols, pm.toCols, pm.block r0 T.B, PMat.empty.toCols, .empty, r0, T.next,
          seqRows T.next r0 T.B, per, T.first, T.last, T.trans⟩)

/-- `quotientOfLde` on packed words. -/
def quotient [Mont32BaseField p] [Binomial4 p] (A : Air F) (pis : List F)
    (degreeBits logChunks : Nat) (ext : PMat) (prep : Option PMat) (alpha : EF) : Array EF :=
  quotientWith [] (quotientTables degreeBits logChunks) A pis ext prep alpha

/-! ### LogUp kernels -/

/-- A block of `B` values of an extension expression: one value for every row (`const`), base
words (`base`), or extension planes (`ext`). Each operation keeps the cheapest kind. -/
inductive XVal (p : ℕ) [Mont32Field p] where
  | const (c : Ext4 p)
  | base (w : ByteArray)
  | ext (v : EVec p)

namespace XVal

/-- `B` copies of the word `c`. -/
abbrev rep (c : F) (B : Nat) : ByteArray := Words.replicateWord c.val B

/-- The planes of a block of `B` values. -/
def planes (B : Nat) : XVal p → EVec p
  | const c => ⟨B, rep c.c0 B, rep c.c1 B, rep c.c2 B, rep c.c3 B⟩
  | base w => ⟨B, w, CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B,
      CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B,
      CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B⟩
  | ext v => v

/-- Base words times an extension scalar. -/
def scaleBase (B : Nat) (w : ByteArray) (c : EF) : EVec p :=
  let z := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
  ⟨B, Words.mulAddWords p z w c.c0.val B, Words.mulAddWords p z w c.c1.val B,
    Words.mulAddWords p z w c.c2.val B, Words.mulAddWords p z w c.c3.val B⟩

def add (B : Nat) : XVal p → XVal p → XVal p
  | const a, const b => const (a + b)
  | base a, base b => base (Words.addWords p a b B)
  | ext v, base w => ext ⟨B, Words.addWords p v.c0 w B, v.c1, v.c2, v.c3⟩
  | base w, ext v => ext ⟨B, Words.addWords p w v.c0 B, v.c1, v.c2, v.c3⟩
  | x, y => ext ((x.planes B).add (y.planes B))

def sub (B : Nat) : XVal p → XVal p → XVal p
  | const a, const b => const (a - b)
  | base a, base b => base (Words.subWords p a b B)
  | ext v, base w => ext ⟨B, Words.subWords p v.c0 w B, v.c1, v.c2, v.c3⟩
  | x, y => ext ((x.planes B).sub (y.planes B))

def mul [Binomial4 p] (B : Nat) : XVal p → XVal p → XVal p
  | const a, const b => const (a * b)
  | base a, base b => base (Words.mulWords p a b B)
  | const c, base w => ext (scaleBase B w c)
  | base w, const c => ext (scaleBase B w c)
  | const c, ext v => ext (v.smul c)
  | ext v, const c => ext (v.smul c)
  | base w, ext v => ext (v.mulBase w)
  | ext v, base w => ext (v.mulBase w)
  | ext a, ext b => ext (a.mul b)

end XVal

/-- `X ^ j · s`: the weight of coordinate `j` of a value weighted by `s`. -/
def xPowMul [Binomial4 p] (j : Nat) (s : EF) : EF := (List.range j).foldl
  (fun x _ ↦ ⟨Binomial4.mulW x.c3, x.c0, x.c1, x.c2⟩) s

/-- The weights of `K` extension constraints, coordinate `j` of constraint `k` weighted by
`X ^ j α ^ (K - 1 - k)`, four coordinates each. -/
def extWeightCoords [Mont32BaseField p] [Binomial4 p] (alpha : EF) (K : Nat) : Array F :=
  Array.ofFn (n := 16 * K) fun i ↦
    (Ext.coeffs (xPowMul (i.val / 4 % 4) (Ext.pow alpha (K - 1 - i.val / 16)))).getD (i.val % 4) 0

/-- `lookupQuotientOfLde` on packed words with the shape's tables `T`, as `quotientWith`: the
extension constraints' program (`Prog.compileExt`, its scalars the public values, the terminal
and the challenges) on blocks of rows (`quotientBlocks`). -/
def lookupQuotientWith [Mont32BaseField p] [Binomial4 p] (kernels : List (Prog.GroupKernel p))
    (T : QuotientTables p) (A : Air F) (ext : List (Lookup.ExtExpr F)) (pis : List F) (tr : PMat)
    (prep : Option PMat) (perm : PMat) (chs : List EF) (terminal alpha : EF) : Array EF :=
  let pm := prep.getD PMat.empty
  let per := periodicWords T A
  let prog := Prog.compileExt Binomial4.W pis.length ext
  let k? := kernelFor kernels prog.code
  quotientBlocks T prog (groupRun k? prog.code)
    (pis.toArray ++ (terminal :: chs).toArray.flatMap fun c ↦ (Ext.coeffs c).toArray)
    (extWeightCoords alpha ext.length) fun r0 ↦
      (⟨tr.block r0 T.B, 0, T.B⟩,
        ⟨tr.toCols, pm.toCols, pm.block r0 T.B, perm.toCols, perm.block r0 T.B, r0, T.next,
          seqRows T.next r0 T.B, per, T.first, T.last, T.trans⟩)

/-- `lookupQuotientOfLde` on packed words. -/
def lookupQuotient [Mont32BaseField p] [Binomial4 p] (A : Air F) (ext : List (Lookup.ExtExpr F))
    (pis : List F) (degreeBits logChunks : Nat) (tr : PMat) (prep : Option PMat) (perm : PMat)
    (chs : List EF) (terminal alpha : EF) : Array EF :=
  lookupQuotientWith [] (quotientTables degreeBits logChunks) A ext pis tr prep perm chs terminal
    alpha

/-- The words `a` of a block of `B` with every zero replaced by one. -/
def nonzeroWords (a : @& ByteArray) (B : Nat) : ByteArray := Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
  for k in [0:B] do
    let x := CompPoly.CPolynomial.NTTFast.Packed.Native.read a k
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out k
      (if x == 0 then (1 : F).val else x)
  return out

/-- The words `b` of a block of `B`, with `0` where `a` is zero. -/
def maskZeros (a b : @& ByteArray) (B : Nat) : ByteArray := Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
  for k in [0:B] do
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out k
      (if CompPoly.CPolynomial.NTTFast.Packed.Native.read a k == 0 then 0
        else CompPoly.CPolynomial.NTTFast.Packed.Native.read b k)
  return out

/-- The inverses of a block of `B` words, `0` for zero: batch inversion with the zeros replaced
by one, then masked. -/
def invWords (a : ByteArray) (B : Nat) : ByteArray :=
  maskZeros a (batchInvRange p (nonzeroWords (p := p) a B) 0 B) B

/-- `x · c` on `B` words for a word `c`. -/
def scaleWords (x : @& ByteArray) (c : F) (B : Nat) : ByteArray :=
  Words.mulAddWords p (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B) x c.val B

/-- `Ext4.inv` on planes: with `σ : X ↦ -X`, `a σ(a) = g₀ + g₁ X²`, its norm `g₀² - W g₁²`
inverted in one batch, and `a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`; zero to zero. -/
def invPlanes [Binomial4 p] (a : EVec p) : EVec p :=
  let B := a.n
  let W : F := Binomial4.W
  let m (x y : ByteArray) := Words.mulWords p x y B
  let ad (x y : ByteArray) := Words.addWords p x y B
  let sb (x y : ByteArray) := Words.subWords p x y B
  let c13 := m a.c1 a.c3
  let g0 := Words.mulAddWords p (m a.c0 a.c0) (sb (m a.c2 a.c2) (ad c13 c13)) W.val B
  let c02 := m a.c0 a.c2
  let g1 := Words.mulAddWords p (sb (ad c02 c02) (m a.c1 a.c1)) (m a.c3 a.c3) (-W).val B
  let ni := invWords (p := p) (Words.mulAddWords p (m g0 g0) (m g1 g1) (-W).val B) B
  ⟨B, m (Words.mulAddWords p (m a.c0 g0) (m a.c2 g1) (-W).val B) ni,
    m (sb (scaleWords (m a.c3 g1) W B) (m a.c1 g0)) ni,
    m (sb (m a.c2 g0) (m a.c0 g1)) ni, m (sb (m a.c1 g1) (m a.c3 g0)) ni⟩

/-- `combine b t` on a block of `B` rows, the tuple's values `t` as base words: Horner's rule from
the first. -/
def combineX [Binomial4 p] (B : Nat) (b : EF) : List ByteArray → XVal p
  | [] => .const 0
  | x :: xs => xs.foldl (fun acc y ↦ (XVal.base y).add B (acc.mul B (.const b))) (.base x)

/-- The fractions of lookups on a block of `B` rows (`rowFractions`), lookup `c` given by its
tuples `ts[c]` of expressions whose blocks are `get v`: its tuples `(t, m)` add
`m / (a - combine b t)`, with its pair `(a, b)` of the challenges `chs`, `a` given as the planes
`apl[c]`. -/
def fractionsX [Binomial4 p] {β E : Type} (B : Nat) (get : β → E → ByteArray) (v : β)
    (ts : List (List (List E × E))) (chs : List EF) (apl : Array (EVec p)) :
    List (EVec p) :=
  ts.zipIdx.map fun (l, c) ↦
    l.foldl (fun s (t, m) ↦
      let den := (XVal.ext (apl.getD c (EVec.zeros B))).sub B
        (combineX B (chs.getD (2 * c + 1) 0) (t.map (get v)))
      s.add ((invPlanes (den.planes B)).mulBase (get v m))) (EVec.zeros B)

/-- Row `i` of the permutation trace in base coordinates, written from word `o` of `out`: the
accumulator `acc`, then every lookup's fraction, the planes `fs`. -/
def writeRow (out : ByteArray) (o : Nat) (fs : Array (EVec p)) (acc : EF) (i : Nat) :
    ByteArray := Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out o acc.c0.val
  out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (o + 1) acc.c1.val
  out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (o + 2) acc.c2.val
  out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (o + 3) acc.c3.val
  for c in [0:fs.size] do
    let f := fs.getD c (EVec.zeros 0)
    let oc := o + 4 * (c + 1)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out oc
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read f.c0 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (oc + 1)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read f.c1 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (oc + 2)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read f.c2 i)
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out (oc + 3)
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read f.c3 i)
  return out

/-- A block of `B` rows of the permutation trace in base coordinates, `W` words per row, written
from row `r` of `out` (`writeRow`), the accumulator from `acc`; and the accumulator after it. -/
def writeBlock (out : ByteArray) (r : Nat) (fs : Array (EVec p)) (acc : EF) (B W : Nat) :
    ByteArray × EF := Id.run do
  let mut out := out
  let mut acc := acc
  for i in [0:B] do
    out := writeRow out ((r + i) * W) fs acc i
    acc := fs.foldl (fun a f ↦ a + f.get i) acc
  return (out, acc)

/-- Words `o, …, o + 3` of `out` plus the coordinates of `s`. -/
def shiftRow (out : ByteArray) (o : Nat) (s : EF) : ByteArray :=
  let addAt (out : ByteArray) (k : Nat) (c : F) : ByteArray :=
    CompPoly.CPolynomial.NTTFast.Packed.Native.write out k
      (CompPoly.CPolynomial.NTTFast.Packed.add p
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read out k) c.val)
  addAt (addAt (addAt (addAt out o s.c0) (o + 1) s.c1) (o + 2) s.c2) (o + 3) s.c3

/-- The accumulator columns of `rows` rows of `W` words shifted by `s`. -/
def shiftAccumulator (out : ByteArray) (rows W : Nat) (s : EF) : ByteArray :=
  (List.range rows).foldl (fun out i ↦ shiftRow out (i * W) s) out

/-- The rows of `nb` blocks of `B` rows from block `b0` of the permutation trace of lookups given
by their tuples `ts`, in base coordinates, `W` words per row, with the accumulator from `0` at the
first; and the sum of their fractions. `get (blk r0)` are the expressions' blocks from row `r0`. -/
def rangeRows [Binomial4 p] {β E : Type} (blk : Nat → β) (get : β → E → ByteArray)
    (ts : List (List (List E × E)))
    (chs : List EF) (B W b0 nb : Nat) : ByteArray × EF :=
  let apl := (Array.range ts.length).map fun c ↦ (XVal.const (chs.getD (2 * c) 0)).planes B
  (List.range nb).foldl (fun (out, acc) j ↦
      writeBlock out (j * B) (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray acc B W)
    (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (nb * B * W), 0)

/-- The permutation trace's rows of `blocks` blocks of `B` rows, `W` words per row, as packed
words, and its terminal: in parallel ranges of blocks, the rows with the accumulator from the
range's start (`rangeRows`), then the ranges' accumulators shifted by the sums before them. -/
def assembleRanges [Binomial4 p] {β E : Type} (blk : Nat → β) (get : β → E → ByteArray)
    (ts : List (List (List E × E))) (chs : List EF) (B W blocks : Nat) : ByteArray × EF :=
  let tasks := if blocks < 16 then 1 else 16
  let size := blocks / tasks
  let count (k : Nat) := if k + 1 = tasks then blocks - k * size else size
  let ranges := (Array.range tasks).map fun k ↦ Task.spawn fun _ ↦
    rangeRows blk get ts chs B W (k * size) (count k)
  let starts := ranges.foldl (fun (acc : Array EF × EF) t ↦ (acc.1.push acc.2, acc.2 + t.get.2))
    (#[], 0)
  let words := ((Array.range tasks).map fun k ↦ Task.spawn fun _ ↦
      shiftAccumulator ((ranges.getD k (Task.pure (.empty, 0))).get.1) (count k * B) W
        (starts.1.getD k 0)).foldl (fun acc t ↦ acc ++ t.get)
      (ByteArray.emptyWithCapacity (4 * blocks * B * W))
  (words, starts.2)

/-- A lookup's tuples with every expression replaced by its index among all of them in order, from
`k`, and the next index. -/
def indexLookup {α : Type} : List (List α × α) → Nat → List (List Nat × Nat) × Nat
  | [], k => ([], k)
  | (t, _) :: l, k =>
    let (r, k') := indexLookup l (k + t.length + 1)
    ((List.range' k t.length, k + t.length) :: r, k')

/-- Lookups' tuples with every expression replaced by its index among all of them in order, from
`k` (`indexLookup`). -/
def indexTuples {α : Type} : List (List (List α × α)) → Nat → List (List (List Nat × Nat))
  | [], _ => []
  | l :: ls, k => (indexLookup l k).1 :: indexTuples ls (indexLookup l k).2

theorem blockSize_lt (x : Nat) : 4 * min x 256 < USize.size :=
  Nat.lt_of_lt_of_le (by have := Nat.min_le_right x 256; omega) USize.le_size

/-- Lookups' tuples' expressions in order: every tuple's elements, then its multiplicity. -/
def flatTuples {α : Type} (ts : List (List (List α × α))) : List α :=
  ts.flatMap fun l ↦ l.flatMap fun (t, m) ↦ t ++ [m]

/-- The permutation trace of `A`'s lookups `ls` in base coordinates as packed words, and its
terminal (`permutationOf`): the lookups' expressions as one program (`Prog.compileOuts`) run on
blocks of rows, every lookup's fractions computed block by block (`fractionsX`) with one batch
inversion per tuple, in parallel ranges of blocks (`assembleRanges`). -/
def permutationWords [Mont32BaseField p] [Binomial4 p] (A : Air F) (ls : List (Stark.Lookup F))
    (logN : Nat) (trace : Array F) (pis : List F) (chs : List EF) : ByteArray × EF :=
  let n := 2 ^ logN
  let w := A.width
  let pw := A.preprocessedWidth
  let parts := if n < 4096 then 1 else 16
  let B := min (n / parts) 256
  have hS : 4 * B < USize.size := blockSize_lt (n / parts)
  let blocks := n / B
  let enc := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
  let words := enc trace
  let pwords := enc A.preprocessed
  let next := Array.ofFn (n := n) fun i ↦ (i.val + 1) % n
  let sel (f : Nat → Bool) := enc (Array.ofFn (n := n) fun i ↦ if f i.val then (1 : F) else 0)
  let first := sel (· == 0)
  let last := sel (· + 1 == n)
  let trans := sel (· + 1 < n)
  let tups := ls.map Stark.Lookup.tuples
  let prog := Prog.compileOuts (flatTuples tups)
  let mc := rowMajorCols words w n
  let pc := rowMajorCols pwords pw n
  let blk (r0 : Nat) : Array ByteArray :=
    let tr := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows
    let L : Prog.Loads := ⟨mc, pc, tr pwords pw r0 B, PMat.empty.toCols, .empty, r0, next,
      seqRows next r0 B, #[], first, last, trans⟩
    let v : Prog.View := ⟨tr words w r0 B, 0, B⟩
    let regs := Prog.runBlock p prog.code v L pis.toArray #[] B hS (Array.replicate (4 + prog.regs)
      ⟨CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B, ByteArray.size_zeros _⟩)
    Prog.outWords p prog.outs v regs B
  assembleRanges blk (fun ws k ↦ ws.getD k .empty) (indexTuples tups 0) chs B
      ((ls.length + 1) * 4) blocks

/-- `permutationLdeOf` on packed words: the permutation trace's words (`permutationWords`)
extended by CompPoly's batched coset LDE with plans from `plans`. -/
def permutationLdeWith [Mont32BaseField p] [Binomial4 p]
    (plans : List (Nat × Nat × F × LdePlan p)) (bits : Nat) (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (trace : Array F) (pis : List F) (chs : List EF) :
    PMat × EF :=
  let (words, t) := permutationWords A ls logN trace pis chs
  (ldeWordsWith plans logN bits gen ((ls.length + 1) * 4) #[words], t)

/-- The weight planes of the stored rows `r0, …, r0 + len - 1` for every point `z` of `zs`: the
four coordinate planes of `x_r / (z - x_r)` for each point, in order. -/
def weightPlanes [Mont32BaseField p] [Binomial4 p] (zs : @& Array EF) (xs : @& ByteArray)
    (r0 len : Nat) : Array ByteArray :=
  let xr := slice xs r0 len
  zs.foldl (fun acc z ↦
    let wt := (invDenoms z xr len).mulBase xr
    acc ++ #[wt.c0, wt.c1, wt.c2, wt.c3]) #[]

/-- The column sums `∑_r m[r][j] · x_r / (z - x_r)` over the stored rows `r0, …, r0 + len - 1` of a
packed matrix, within one block of its rows, for every point `z` of `zs`: per point four planes of
a word per column. Each column's rows are dotted with every plane while they are in cache. -/
def weightedColumns [Mont32BaseField p] [Binomial4 p] (m : @& PMat) (zs : @& Array EF)
    (xs : @& ByteArray) (r0 len : Nat) : Array ByteArray :=
  let wts := weightPlanes zs xs r0 len
  let sums := (Array.range m.width).map fun j ↦
    wts.map fun pl ↦ Words.dotAt p (m.colAt j r0).1 (m.colAt j r0).2 pl len
  (Array.range wts.size).map fun i ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := m.width) fun j ↦
      CompPoly.CPolynomial.NTTFast.Packed.ofWord p ((sums.getD j.val #[]).getD i 0))

/-- `openedAt` on packed words, at all points of a matrix: the barycentric weights `x / (z - x)` in
the stored bit-reversed row order, as planes by the norm, and the column sums over parallel row
ranges, each range within one block of the matrix's rows. -/
def openedAt [Mont32BaseField p] [Binomial4 p] (logBlowup : Nat) (m : PMat) (zs : List EF) : List
    (Array EF) :=
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  let w := m.width
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
      (cosetPointsBitRev (gen : F) logH)
  let parts := h / Nat.gcd (if h < 4096 then h else h / 16) m.rows
  let size := h / parts
  let tasks := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    weightedColumns m zs.toArray xs (k * size) (if k + 1 = parts then h - k * size else size)
  let sums := tasks.foldl (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords p a b w)
    (Array.replicate (4 * zs.length) (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w))
  zs.zipIdx.map fun (z, k) ↦
    let factor := Fri.cosetFactor logH gen z
    Array.ofFn (n := w) fun j ↦
      factor * ⟨word (sums.getD (4 * k) .empty) j, word (sums.getD (4 * k + 1) .empty) j,
        word (sums.getD (4 * k + 2) .empty) j, word (sums.getD (4 * k + 3) .empty) j⟩

/-- Rows `r0, …, r0 + len - 1` of a packed matrix, within one block of its rows, batched by the
powers of `α`, given as four coordinate planes `a0, …, a3`: four planes of `len` words in one
buffer, the columns multiply-added into all four four at a time, every column word read once and
every word reduced once per four columns (`Words.mulAdd4x4Into`); a last group short of four
columns repeats the last column with zero powers. -/
def compressRange (p : ℕ) [Mont32Field p] (m : @& PMat) (a0 a1 a2 a3 : @& ByteArray)
    (r0 len : Nat) : Array ByteArray :=
  let read (a : @& ByteArray) (j : Nat) : UInt32 :=
    if j < m.width then CompPoly.CPolynomial.NTTFast.Packed.Native.read a j else 0
  let col (j : Nat) := m.colAt (min j (m.width - 1)) r0
  let out := Merkle.Packed.foldRange (fun out g ↦
    Words.mulAdd4x4Into p out (col (4 * g)).1 (col (4 * g + 1)).1 (col (4 * g + 2)).1
      (col (4 * g + 3)).1 (col (4 * g)).2 (col (4 * g + 1)).2 (col (4 * g + 2)).2
      (col (4 * g + 3)).2 (read a0 (4 * g)) (read a0 (4 * g + 1)) (read a0 (4 * g + 2))
      (read a0 (4 * g + 3)) (read a1 (4 * g)) (read a1 (4 * g + 1)) (read a1 (4 * g + 2))
      (read a1 (4 * g + 3)) (read a2 (4 * g)) (read a2 (4 * g + 1)) (read a2 (4 * g + 2))
      (read a2 (4 * g + 3)) (read a3 (4 * g)) (read a3 (4 * g + 1)) (read a3 (4 * g + 2))
      (read a3 (4 * g + 3)) len)
    ((m.width + 3) / 4) 0 (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (4 * len))
  #[out.extract (4 * 0) (4 * len), out.extract (4 * len) (4 * (2 * len)),
    out.extract (4 * (2 * len)) (4 * (3 * len)), out.extract (4 * (3 * len)) (4 * (4 * len))]

/-- Concatenate parallel pieces of planes. -/
def joinPlanes (p : ℕ) (n : Nat) (pieces : Array (Task (Array ByteArray))) : EVec p :=
  let cat (j : Nat) := pieces.foldl (fun acc t ↦ acc ++ t.get.getD j .empty)
    (ByteArray.emptyWithCapacity (4 * n))
  ⟨n, cat 0, cat 1, cat 2, cat 3⟩

/-- Rows `r0, …, r0 + len - 1` of the batched quotient of one height: for every matrix, its rows
batched by the planes `a` of the powers of `α`, and for every point `(z, yz, offset)` the term
`offset · (yz - comp) / (z - x)`, `xs` the height's points. -/
def reduceRange [Mont32BaseField p] [Binomial4 p]
    (items : @& Array (PMat × EVec p × List (EF × EF × EF))) (xs : @& ByteArray)
    (r0 len : Nat) : EVec p := Id.run do
  let xr := slice xs r0 len
  let mut acc := EVec.zeros len
  -- `1 / (z - x)` once per distinct point.
  let mut invs : List (EF × EVec p) := []
  for (m, a, pts) in items do
    let comp := compressRange p m a.c0 a.c1 a.c2 a.c3 r0 len
    let comp : EVec p := ⟨len, comp.getD 0 .empty, comp.getD 1 .empty, comp.getD 2 .empty,
      comp.getD 3 .empty⟩
    for (z, yz, offset) in pts do
      let inv ← match invs.lookup z with
        | some v => pure v
        | none => do
          let v := invDenoms z xr len
          invs := (z, v) :: invs
          pure v
      acc := acc.add (((EVec.rsub yz comp).mul inv).smul offset)
  return acc

/-- `Fri.reduce` on planes, every height in parallel ranges of rows within one block of every
matrix: rows batched column by column, `1 / (z - x)` by the norm. -/
def reduce [Mont32BaseField p] [Binomial4 p] (alpha : EF)
    (items : List (PMat × List (EF × Array EF))) :
    List (Nat × EVec p) :=
  Id.run do
  -- Per height: the matrices with their points, opened sums and powers of `α`, in order.
  let mut groups : List (Nat × Nat × Array (PMat × EVec p × List (EF × EF × EF))) := []
  for (m, pts) in items do
    let logH := Nat.log2 m.height
    let (cnt, g) := (groups.lookup logH).getD (0, #[])
    let ap := Array.ofFn (n := m.width) fun i ↦ Ext.pow alpha i.val
    let mut cnt := cnt
    let mut terms := []
    for (z, ys) in pts do
      let yz := (List.range m.width).foldl (fun s i ↦ s + ap.getD i 0 * ys.getD i 0) 0
      terms := terms ++ [(z, yz, Ext.pow alpha cnt)]
      cnt := cnt + m.width
    groups := (logH, cnt, g.push (m, EVec.ofArray ap, terms)) ::
      groups.filter (·.1 != logH)
  let out := groups.map fun (logH, _, g) ↦
    let n := 2 ^ logH
    let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
        (cosetPointsBitRev (gen : F) logH)
    let parts := n / g.foldl (fun a (m, _) ↦ Nat.gcd a m.rows) (if n < 4096 then n else n / 16)
    let size := n / parts
    let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      let v := reduceRange g xs (k * size) (if k + 1 = parts then n - k * size else size)
      #[v.c0, v.c1, v.c2, v.c3]
    (logH, joinPlanes p n ts)
  return out.mergeSort fun a b ↦ b.1 ≤ a.1

/-- Words `0, 2, 4, …` and `1, 3, 5, …` of the first `2 n` words of `b`. -/
def deinterleave (b : @& ByteArray) (n : Nat) : ByteArray × ByteArray := Id.run do
  let mut e := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords n
  let mut o := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords n
  for i in [0:n] do
    e := CompPoly.CPolynomial.NTTFast.Packed.Native.write e i
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read b (2 * i))
    o := CompPoly.CPolynomial.NTTFast.Packed.Native.write o i
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read b (2 * i + 1))
  return (e, o)

/-- Pairs `r0, …, r0 + len - 1` of the arity-2 fold of planes `v` at `β`; `twoX` holds `2 x` of
every pair. -/
def fold2Range [Mont32BaseField p] [Binomial4 p] (v : @& EVec p) (twoX : @& ByteArray) (beta : EF)
    (r0 len : Nat) :
    EVec p :=
  let split (b : ByteArray) := deinterleave (slice b (2 * r0) (2 * len)) len
  let (l0, h0) := split v.c0
  let (l1, h1) := split v.c1
  let (l2, h2) := split v.c2
  let (l3, h3) := split v.c3
  let lo : EVec p := ⟨len, l0, l1, l2, l3⟩
  let hi : EVec p := ⟨len, h0, h1, h2, h3⟩
  let inv2x := batchInvRange p twoX r0 len
  ((lo.add hi).smul (Ext.ofBase (2 : F)⁻¹)).add (((lo.sub hi).mulBase inv2x).smul beta)

/-- `Fri.foldPairs` on planes, `(lo + hi) / 2 + β (lo - hi) / (2 x)`, in parallel ranges. -/
def fold2 [Mont32BaseField p] [Binomial4 p] (v : EVec p) (beta : EF) (logRows : Nat) : EVec p :=
  let rows := 2 ^ logRows
  let pw := cosetPoints (1 : F) (logRows + 1)
  let twoX := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    ((bitRevPerm logRows).map fun i ↦ 2 * pw.getD i 0)
  let parts := if rows < 4096 then 1 else 16
  let size := rows / parts
  joinPlanes p rows <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    let f := fold2Range v twoX beta (k * size) (if k + 1 = parts then rows - k * size else size)
    #[f.c0, f.c1, f.c2, f.c3]

/-- `Fri.foldOnce` on planes: the arity-2 fold `fold2`, otherwise every group's `foldRow`, in
parallel ranges of rows. -/
def fold [Mont32BaseField p] [Binomial4 p] (la : Nat) (beta : EF) (v : EVec p) : EVec p :=
  let rows := v.n / 2 ^ la
  if la = 1 then fold2 v beta (Nat.log2 rows) else
    let vs := v.toArray
    EVec.ofArray (parChunks rows (if rows < 1024 then 1 else 16) fun r0 len ↦
      Array.ofFn (n := len) fun i ↦ Fri.foldRow (r0 + i.val) (Nat.log2 rows) la beta
        ((List.range (2 ^ la)).map fun k ↦ vs.getD ((r0 + i.val) * 2 ^ la + k) 0))

/-- Words `i, i + k, i + 2 k, …` of `a`, `count` of them. -/
def strided (a : @& ByteArray) (i k count : Nat) : ByteArray := Id.run do
  let mut out := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords count
  for r in [0:count] do
    out := CompPoly.CPolynomial.NTTFast.Packed.Native.write out r
      (CompPoly.CPolynomial.NTTFast.Packed.Native.read a (r * k + i))
  return out

/-- The matrix of rows of `k` elements, flattened, packed as one block of columns: column
`4 i + c` holds coordinate `c` of the `i`-th element of every row, gathered by parallel tasks. -/
def leaves (k : Nat) (v : EVec p) : PMat :=
  let h := v.n / k
  let plane (c : Nat) : ByteArray := match c with
    | 0 => v.c0
    | 1 => v.c1
    | 2 => v.c2
    | _ => v.c3
  ⟨4 * k, h, h, (CompPoly.Tasks.join (CompPoly.Tasks.spawnAll (4 * k) fun j ↦
    strided (plane (j % 4)) (j / 4) k h)).get⟩

/-- `a + x · b`. -/
def addScaled [Binomial4 p] (a b : EVec p) (x : EF) : EVec p := a.add (b.smul x)

variable [Mont32BaseField p] [Binomial4 p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]

/-- The fast backend. A trace is packed words in chunks of consecutive rows (`rowChunks`). -/
def backend : Backend F EF 24 where
  transcript := transcript
  Trace := Array ByteArray
  M := PMat
  C := Commit
  ldeTrace := ldeWordsWith []
  traceValues t :=
    CompPoly.PackedRepr.decode (CompPoly.CPolynomial.NTTFast.Packed.Native.joinRows t)
  lde := lde
  commit := commit p
  cap := Commit.cap
  openAt := Commit.openAt
  logHeight c := Nat.log2 c.maxHeight
  quotient := quotient
  lookupQuotient := lookupQuotient
  permutation := permutationLdeWith []
  openedAt := openedAt
  V := EVec p
  toArray := EVec.toArray
  ofArray := EVec.ofArray
  size := (·.n)
  reduce := reduce
  fold := fold
  addScaled := addScaled
  leaves := leaves

/-- The fast backend with the extension plans and quotient tables of proofs of instances of the
shapes `shapes` prepared: for every `(logN, logChunks)`, a `2 ^ logN`-row trace with
`2 ^ logChunks` quotient chunks, the trace's extension on `g · ⟨ω_N⟩`, every chunk's and the
quotient's tables, and the kernels of `kernels` whose code is their program's
(`checkedKernels`): an AIR's constraints with a kernel are not compiled again, and every program
runs by a kernel with its code (`kernelFor`). -/
def backendFor (kernels : List (AirKernel p)) (logBlowup : Nat) (shapes : List (Nat × Nat)) :
    Backend F EF 24 :=
  let checked := checkedKernels kernels
  let shapes := shapes.eraseDups
  let tables := shapes.map fun (n, c) ↦ (n, c, quotientTables n c)
  let plans := shapes.flatMap fun (n, c) ↦ ldePlans n logBlowup c
  { backend with
    ldeTrace := ldeWordsWith plans
    lde := ldeWith plans
    permutation := permutationLdeWith plans
    quotient := fun A pis db lc ext prep alpha ↦
      match tables.find? fun (n, c, _) ↦ n == db && c == lc with
      | some (_, _, T) => quotientWith checked T A pis ext prep alpha
      | none => quotient A pis db lc ext prep alpha
    lookupQuotient := fun A ext pis db lc tr prep perm chs t alpha ↦
      match tables.find? fun (n, c, _) ↦ n == db && c == lc with
      | some (_, _, T) =>
        lookupQuotientWith (kernels.map (·.kernel)) T A ext pis tr prep perm chs t alpha
      | none => lookupQuotient A ext pis db lc tr prep perm chs t alpha }

end CompStark.Stark.Fast
