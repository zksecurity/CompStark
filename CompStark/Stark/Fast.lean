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
public import CompPoly.Fields.Montgomery.Native32ExtPlanes
public import CompStark.Mont32.Challenge
public import CompStark.Stark.ProgWords
public import CompStark.Stark.ProgGroup

/-! # The fast prover backend

The kernels of `Backend` on packed Montgomery words, over a Montgomery field `FastField p` with its
domains (`Mont32BaseField`), a fast extension `EF` of it (CompPoly's `FastExt p EF`, of any modulus
and degree `d`, with its inversion of coordinate planes `PlanesInv`), Plonky3's Poseidon2
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
open CompPoly.Array (batchInv)

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
variable {EF : Type} [FastExt p EF]

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

/-- The first passing candidate of batch `b`, `8 b, …, 8 b + 7`, whose permuted word is divisible
by `m`: `group` holds eight copies of the duplexed state as a packed group, and the candidates go
into coordinate `wi`. -/
def grindBatch (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : @& ByteArray)
    (wi m b : Nat) : Option Nat :=
  let W := (List.range 8).foldl (fun W l ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write W
    (8 * wi + l) ((8 * b + l : Nat) : FastField p).val)
    (group.copySlice 0 ByteArray.empty 0 group.size)
  let out := PackedPoseidon2.permute24 p W
  ((List.range 8).find? fun l ↦ 8 * b + l < p &&
    FastField.toNat (word (p := p) out (8 * 15 + l)) % m == 0).map (8 * b + ·)

/-- The first passing candidate of the `nb` batches from `b`, if any. -/
def grindRange (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : @& ByteArray)
    (wi m : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | nb + 1, b =>
    match grindBatch p group wi m b with
    | some c => some c
    | none => grindRange p group wi m nb (b + 1)

/-- The smallest passing candidate from wave `wave` on: each wave splits 1024 batches of eight
candidates among 16 tasks, and the first wave with a passing candidate has the smallest. -/
def grindWaves (p : ℕ) [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]
    (group : ByteArray) (wi m : Nat) :
    Nat → Nat → FastField p
  | 0, _ => 0
  | fuel + 1, wave =>
    let ts := (Array.range 16).map fun k ↦ Task.spawn fun _ ↦
      grindRange p group wi m 64 (1024 * wave + 64 * k)
    match (ts.map Task.get).findSome? id with
    | some c => (c : FastField p)
    | none => grindWaves p group wi m fuel (wave + 1)

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
  grindWaves p group (witnessSlot c) (2 ^ bits) (p / 8192 + 1) 0

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

/-- The number of columns the extension transposes together: a range's transposed rows are freed
once its columns are extended, so the input's transposed copy shrinks while the extension grows. -/
def rangeColumns : Nat := 256

open CompPoly.CPolynomial.NTTFast.Packed.Native (transposeRows columnCoefficients
  gatherColumn cosetBlock) in
/-- The extension by `P` of the `w`-column matrix whose rows are the chunks `ms` of equal heights,
column by column: block `t` of column `j`, the values on coset `bitrev t`, at `t * w + j`. For each
range of `rangeColumns` columns, tasks transpose row ranges of the chunks into columns
(`lineRanges`); every column is one task, its coefficients and then each of its coset blocks, the
last one from the coefficients' buffer. -/
def ldeColumns (P : LdePlan p) (w : Nat) (ms : Array ByteArray) : Array ByteArray :=
  let q := lineRanges P.logH ms.size
  let rows := 2 ^ P.logH / (ms.size * q)
  let blocks := (CompPoly.Tasks.join ((Array.range ((w + rangeColumns - 1) / rangeColumns)).flatMap
    fun r ↦
      let n := min rangeColumns (w - rangeColumns * r)
      let pieces := CompPoly.Tasks.join (CompPoly.Tasks.spawnAll (ms.size * q) fun k ↦
        transposeRows (ms.getD (k / q) .empty) w (rangeColumns * r) n (k % q * rows) rows)
      (Array.range n).map fun j ↦ pieces.bind fun ps ↦ Task.spawn fun _ ↦
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
  let t := CompPoly.CPolynomial.NTTFast.Packed.Native.transposeRows m w 0 w 0 n
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
def powerSeq [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (K : Nat) : Array EF :=
  ((List.range K).foldl (fun (acc, x) _ ↦ (acc.push x, x * alpha)) ((#[] : Array EF), 1)).1

/-- The weights `α ^ (K - 1 - k)` of `K` constraints, `d` coordinates each. -/
def weightCoords [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (K : Nat) : Array F :=
  let pw := powerSeq alpha K
  let d := FastExt.d p EF
  Array.ofFn (n := d * K) fun i ↦
    (Ext.coeffs (pw.getD (K - 1 - i.val / d) 0)).getD (i.val % d) 0

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
@[specialize] def quotientBlocks [Mont32BaseField p] [Mont32.AlgebraId EF]
    (T : QuotientTables p) (prog : Prog F)
    (run : Prog.GroupEnv → ByteArray → ByteArray) (scal wts : Array F)
    (block : Nat → Prog.View × Prog.Loads) : Array EF := Id.run do
  let n := 2 ^ (T.degreeBits + T.logChunks)
  let period := 2 ^ T.logChunks
  let perm := T.perm
  let B := T.B
  let blocks := n / B
  let d := FastExt.d p EF
  let scalW := scal.map (·.val)
  let wtsW := wts.map (·.val)
  let byRow := parChunks blocks (min blocks 16) fun b0 nb ↦ Id.run do
    let mut out := Array.emptyWithCapacity (nb * B)
    if B % 16 = 0 ∧ 4 * (B * (d + prog.regs)) < USize.size then
      let mut st := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (B * (d + prog.regs))
      for blk in [b0:b0 + nb] do
        let r0 := blk * B
        let (v, L) := block r0
        let env := Prog.blockEnv d B v L scalW wtsW
        st := run env (Prog.clearAccs d B st)
        for i in [0:B] do
          let z := T.invZh.getD (perm.getD (r0 + i) 0 % period) 0
          out := out.push (FastExt.ofCoords fun j ↦ z * word st (B * j + i))
    else
      let mut regs : Prog.Regs (4 * B) := Array.replicate (d + prog.regs)
        ⟨CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B, ByteArray.size_zeros _⟩
      for blk in [b0:b0 + nb] do
        let r0 := blk * B
        let (v, L) := block r0
        regs := Prog.runBlock p d prog.code v L scal wts B T.hB (Prog.clearAcc d T.hB B regs)
        for i in [0:B] do
          let z := T.invZh.getD (perm.getD (r0 + i) 0 % period) 0
          out := out.push (FastExt.ofCoords fun j ↦ z * word (Prog.regBuf regs j) i)
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
def quotientWith [Mont32BaseField p] [Mont32.AlgebraId EF] (ks : List (CheckedKernel p))
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
def quotient [Mont32BaseField p] [Mont32.AlgebraId EF] (A : Air F) (pis : List F)
    (degreeBits logChunks : Nat) (ext : PMat) (prep : Option PMat) (alpha : EF) : Array EF :=
  quotientWith [] (quotientTables degreeBits logChunks) A pis ext prep alpha

/-! ### LogUp kernels -/

/-- A block of `B` values of an extension expression: one value for every row (`const`), base
words (`base`), or extension planes (`ext`). Each operation keeps the cheapest kind. -/
inductive XVal (p : ℕ) [Mont32Field p] (EF : Type) [FastExt p EF] where
  | const (c : EF)
  | base (w : ByteArray)
  | ext (v : ExtPlanes p EF)

/-- Plane `0` of planes replaced by `f` of it. -/
def mapPlane0 (f : ByteArray → ByteArray) (v : ExtPlanes p EF) : ExtPlanes p EF :=
  ⟨v.n, Vector.ofFn fun k ↦ if k.val = 0 then f v.c[k] else v.c[k]⟩

namespace XVal

/-- `B` copies of the word `c`. -/
abbrev rep (c : F) (B : Nat) : ByteArray := Words.replicateWord c.val B

/-- The planes of a block of `B` values. -/
def planes (B : Nat) : XVal p EF → ExtPlanes p EF
  | const c => ⟨B, Vector.ofFn fun k ↦ rep (FastExt.coord c k) B⟩
  | base w => ⟨B, Vector.ofFn fun k ↦
      if k.val = 0 then w else CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B⟩
  | ext v => v

/-- Base words times an extension scalar. -/
def scaleBase (B : Nat) (w : ByteArray) (c : EF) : ExtPlanes p EF :=
  let z := CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B
  ⟨B, Vector.ofFn fun k ↦ Words.mulAddWords p z w (FastExt.coord c k).val B⟩

def add (B : Nat) : XVal p EF → XVal p EF → XVal p EF
  | const a, const b => const (a + b)
  | base a, base b => base (Words.addWords p a b B)
  | ext v, base w => ext (mapPlane0 (fun x ↦ Words.addWords p x w B) v)
  | base w, ext v => ext (mapPlane0 (fun x ↦ Words.addWords p w x B) v)
  | x, y => ext ((x.planes B).add (y.planes B))

def sub (B : Nat) : XVal p EF → XVal p EF → XVal p EF
  | const a, const b => const (a - b)
  | base a, base b => base (Words.subWords p a b B)
  | ext v, base w => ext (mapPlane0 (fun x ↦ Words.subWords p x w B) v)
  | x, y => ext ((x.planes B).sub (y.planes B))

def mul (B : Nat) : XVal p EF → XVal p EF → XVal p EF
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

/-- The weights of `K` extension constraints, coordinate `j` of constraint `k` weighted by
`X ^ j α ^ (K - 1 - k)`, `d` coordinates each. -/
def extWeightCoords [Mont32BaseField p] [Mont32.AlgebraId EF] (alpha : EF) (K : Nat) : Array F :=
  let d := FastExt.d p EF
  Array.ofFn (n := d * d * K) fun i ↦
    (Ext.coeffs (FastExt.pow FastExt.gen (i.val / d % d) * Ext.pow alpha (K - 1 - i.val / (d * d))
      )).getD (i.val % d) 0

/-- `lookupQuotientOfLde` on packed words with the shape's tables `T`, as `quotientWith`: the
extension constraints' program (`Prog.compileExt`, its scalars the public values, the terminal
and the challenges) on blocks of rows (`quotientBlocks`). -/
def lookupQuotientWith [Mont32BaseField p] [Mont32.AlgebraId EF]
    (kernels : List (Prog.GroupKernel p))
    (T : QuotientTables p) (A : Air F) (ext : List (Lookup.ExtExpr F)) (pis : List F) (tr : PMat)
    (prep : Option PMat) (perm : PMat) (chs : List EF) (terminal alpha : EF) : Array EF :=
  let pm := prep.getD PMat.empty
  let per := periodicWords T A
  let prog := Prog.compileExt (FastExt.params EF) pis.length ext
  let k? := kernelFor kernels prog.code
  quotientBlocks T prog (groupRun k? prog.code)
    (pis.toArray ++ (terminal :: chs).toArray.flatMap fun c ↦ (Ext.coeffs c).toArray)
    (extWeightCoords alpha ext.length) fun r0 ↦
      (⟨tr.block r0 T.B, 0, T.B⟩,
        ⟨tr.toCols, pm.toCols, pm.block r0 T.B, perm.toCols, perm.block r0 T.B, r0, T.next,
          seqRows T.next r0 T.B, per, T.first, T.last, T.trans⟩)

/-- `lookupQuotientOfLde` on packed words. -/
def lookupQuotient [Mont32BaseField p] [Mont32.AlgebraId EF] (A : Air F)
    (ext : List (Lookup.ExtExpr F))
    (pis : List F) (degreeBits logChunks : Nat) (tr : PMat) (prep : Option PMat) (perm : PMat)
    (chs : List EF) (terminal alpha : EF) : Array EF :=
  lookupQuotientWith [] (quotientTables degreeBits logChunks) A ext pis tr prep perm chs terminal
    alpha

/-- `combine b t` on a block of `B` rows, the tuple's values `t` as base words: Horner's rule from
the first. -/
def combineX (B : Nat) (b : EF) : List ByteArray → XVal p EF
  | [] => .const 0
  | x :: xs => xs.foldl (fun acc y ↦ (XVal.base y).add B (acc.mul B (.const b))) (.base x)

/-- The fractions of lookups on a block of `B` rows (`rowFractions`), lookup `c` given by its
tuples `ts[c]` of expressions whose blocks are `get v`: its tuples `(t, m)` add
`m / (a - combine b t)`, with its pair `(a, b)` of the challenges `chs`, `a` given as the planes
`apl[c]`; the denominators inverted by the extension's inversion of planes (`PlanesInv`). -/
def fractionsX [PlanesInv p EF] {β E : Type} (B : Nat) (get : β → E → ByteArray) (v : β)
    (ts : List (List (List E × E))) (chs : List EF) (apl : Array (ExtPlanes p EF)) :
    List (ExtPlanes p EF) :=
  ts.zipIdx.map fun (l, c) ↦
    l.foldl (fun s (t, m) ↦
      let den := (XVal.ext (apl.getD c (ExtPlanes.zeros B))).sub B
        (combineX B (chs.getD (2 * c + 1) 0) (t.map (get v)))
      s.add ((PlanesInv.inv (den.planes B)).mulBase (get v m))) (ExtPlanes.zeros B)

/-- Row `i` of the permutation trace in base coordinates, written from word `o` of `out`: the
accumulator `acc`, then every lookup's fraction, the planes `fs`, `d` coordinates each. -/
def writeRow (out : ByteArray) (o : Nat) (fs : Array (ExtPlanes p EF)) (acc : EF) (i : Nat) :
    ByteArray := Id.run do
  let d := FastExt.d p EF
  let mut out := (List.finRange d).foldl (fun out (k : Fin d) ↦
    CompPoly.CPolynomial.NTTFast.Packed.Native.write out (o + k) (FastExt.coord acc k).val) out
  for c in [0:fs.size] do
    let f := fs.getD c (ExtPlanes.zeros 0)
    let oc := o + d * (c + 1)
    out := (List.finRange d).foldl (fun out (k : Fin d) ↦
      CompPoly.CPolynomial.NTTFast.Packed.Native.write out (oc + k)
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read f.c[k] i)) out
  return out

/-- A block of `B` rows of the permutation trace in base coordinates, `W` words per row, written
from row `r` of `out` (`writeRow`), the accumulator from `acc`; and the accumulator after it. -/
def writeBlock (out : ByteArray) (r : Nat) (fs : Array (ExtPlanes p EF)) (acc : EF) (B W : Nat) :
    ByteArray × EF := Id.run do
  let mut out := out
  let mut acc := acc
  for i in [0:B] do
    out := writeRow out ((r + i) * W) fs acc i
    acc := fs.foldl (fun a f ↦ a + f.get i) acc
  return (out, acc)

/-- Words `o, …, o + d - 1` of `out` plus the coordinates of `s`. -/
def shiftRow (out : ByteArray) (o : Nat) (s : EF) : ByteArray :=
  (List.finRange (FastExt.d p EF)).foldl (fun out (k : Fin (FastExt.d p EF)) ↦
    CompPoly.CPolynomial.NTTFast.Packed.Native.write out (o + k)
      (CompPoly.CPolynomial.NTTFast.Packed.add p
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read out (o + k)) (FastExt.coord s k).val)) out

/-- The accumulator columns of `rows` rows of `W` words shifted by `s`. -/
def shiftAccumulator (out : ByteArray) (rows W : Nat) (s : EF) : ByteArray :=
  (List.range rows).foldl (fun out i ↦ shiftRow out (i * W) s) out

/-- The rows of `nb` blocks of `B` rows from block `b0` of the permutation trace of lookups given
by their tuples `ts`, in base coordinates, `W` words per row, with the accumulator from `0` at the
first; and the sum of their fractions. `get (blk r0)` are the expressions' blocks from row `r0`. -/
def rangeRows [PlanesInv p EF] {β E : Type} (blk : Nat → β) (get : β → E → ByteArray)
    (ts : List (List (List E × E)))
    (chs : List EF) (B W b0 nb : Nat) : ByteArray × EF :=
  let apl := (Array.range ts.length).map fun c ↦
    (XVal.const (p := p) (chs.getD (2 * c) 0)).planes B
  (List.range nb).foldl (fun (out, acc) j ↦
      writeBlock out (j * B) (fractionsX B get (blk ((b0 + j) * B)) ts chs apl).toArray acc B W)
    (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (nb * B * W), 0)

/-- The permutation trace's rows of `blocks` blocks of `B` rows, `W` words per row, as packed
words, and its terminal: in parallel ranges of blocks, the rows with the accumulator from the
range's start (`rangeRows`), then the ranges' accumulators shifted by the sums before them. -/
def assembleRanges [PlanesInv p EF] {β E : Type} (blk : Nat → β) (get : β → E → ByteArray)
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
def permutationWords [Mont32BaseField p] [PlanesInv p EF] (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (trace : Array F) (pis : List F) (chs : List EF) :
    ByteArray × EF :=
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
    let L : Prog.Loads := ⟨mc, pc, tr pwords pw 0 pw r0 B, PMat.empty.toCols, .empty, r0, next,
      seqRows next r0 B, #[], first, last, trans⟩
    let v : Prog.View := ⟨tr words w 0 w r0 B, 0, B⟩
    let regs := Prog.runBlock p 0 prog.code v L pis.toArray #[] B hS (Array.replicate prog.regs
      ⟨CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords B, ByteArray.size_zeros _⟩)
    Prog.outWords p 0 prog.outs v regs B
  assembleRanges blk (fun ws k ↦ ws.getD k .empty) (indexTuples tups 0) chs B
      ((ls.length + 1) * FastExt.d p EF) blocks

/-- `permutationLdeOf` on packed words: the permutation trace's words (`permutationWords`)
extended by CompPoly's batched coset LDE with plans from `plans`. -/
def permutationLdeWith [Mont32BaseField p] [PlanesInv p EF]
    (plans : List (Nat × Nat × F × LdePlan p)) (bits : Nat) (A : Air F)
    (ls : List (Stark.Lookup F)) (logN : Nat) (trace : Array F) (pis : List F) (chs : List EF) :
    PMat × EF :=
  let (words, t) := permutationWords A ls logN trace pis chs
  (ldeWordsWith plans logN bits gen ((ls.length + 1) * FastExt.d p EF) #[words], t)

/-- Words `r0, …, r0 + len - 1` of every plane. -/
def slicePlanes (v : @& ExtPlanes p EF) (r0 len : Nat) : ExtPlanes p EF :=
  ⟨len, v.c.map fun b ↦ slice b r0 len⟩

/-- `1 / (z - x)` on the stored points `x` of height `2 ^ logN`, in parallel ranges. -/
def denomPlanes [Mont32BaseField p] (z : EF) (logN : Nat) : ExtPlanes p EF :=
  let n := 2 ^ logN
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (cosetPointsBitRev (gen : F) logN)
  let parts := if n < 4096 then 1 else 16
  let size := n / parts
  ExtPlanes.join n <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    let len := if k + 1 = parts then n - k * size else size
    (ExtPlanes.invDenoms z (slice xs (k * size) len) len).c.toArray

/-- The tallest log height of the matrices of `items` opened at `z`. -/
def tallest (items : List (PMat × List EF)) (z : EF) : Nat :=
  items.foldl (fun a (m, zs) ↦ if zs.contains z then max a (Nat.log2 m.height) else a) 0

/-- `1 / (z - x)` for every distinct point `z` of the matrices `items`, on the stored points `x` of
the tallest height `2 ^ logN` it is opened at (`denomPlanes`): `(z, logN, planes)`. The stored
points of a smaller height are a prefix of these. -/
def denoms [Mont32BaseField p] (items : List (PMat × List EF)) : List (EF × Nat × ExtPlanes p EF) :=
  (items.flatMap (·.2)).eraseDups.map fun z ↦
    (z, tallest items z, denomPlanes z (tallest items z))

/-- The planes of `1 / (z - x)` of the point `z` in `invs`. -/
def denomsOf (invs : @& List (EF × Nat × ExtPlanes p EF)) (z : EF) : ExtPlanes p EF :=
  ((invs.lookup z).map (·.2)).getD (ExtPlanes.zeros 0)

/-- The weight planes of the stored rows `r0, …, r0 + len - 1` for every point `z` of `zs`: the
`d` coordinate planes of `x_r / (z - x_r)` for each point, in order, from the planes of
`1 / (z - x)` in `invs`. -/
def weightPlanes (invs : @& List (EF × Nat × ExtPlanes p EF)) (zs : @& Array EF)
    (xs : @& ByteArray) (r0 len : Nat) : Array ByteArray :=
  let xr := slice xs r0 len
  zs.foldl (fun acc z ↦
    let wt := (slicePlanes (denomsOf invs z) r0 len).mulBase xr
    acc ++ wt.c.toArray) #[]

/-- The column sums `∑_r m[r][j] · x_r / (z - x_r)` over the stored rows `r0, …, r0 + len - 1` of a
packed matrix, within one block of its rows, for every point `z` of `zs`: per point `d` planes of
a word per column. Each column's rows are dotted with every plane while they are in cache. -/
def weightedColumns (invs : @& List (EF × Nat × ExtPlanes p EF)) (m : @& PMat) (zs : @& Array EF)
    (xs : @& ByteArray) (r0 len : Nat) : Array ByteArray :=
  let wts := weightPlanes invs zs xs r0 len
  let sums := (Array.range m.width).map fun j ↦
    wts.map fun pl ↦ Words.dotAt p (m.colAt j r0).1 (m.colAt j r0).2 pl len
  (Array.range wts.size).map fun i ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    (Array.ofFn (n := m.width) fun j ↦
      CompPoly.CPolynomial.NTTFast.Packed.ofWord p ((sums.getD j.val #[]).getD i 0))

/-- `openedAt` on packed words, at all points of a matrix: the barycentric weights `x / (z - x)` in
the stored bit-reversed row order, from the planes of `1 / (z - x)` in `invs`, and the column sums
over parallel row ranges, each range within one block of the matrix's rows. -/
def openedAt [Mont32BaseField p] [Mont32.AlgebraId EF] (invs : List (EF × Nat × ExtPlanes p EF))
    (logBlowup : Nat) (m : PMat) (zs : List EF) : List (Array EF) :=
  let d := FastExt.d p EF
  let logH := Nat.log2 m.height - logBlowup
  let h := 2 ^ logH
  let w := m.width
  let xs := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
      (cosetPointsBitRev (gen : F) logH)
  let parts := h / Nat.gcd (if h < 4096 then h else h / 16) m.rows
  let size := h / parts
  let tasks := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    weightedColumns invs m zs.toArray xs (k * size) (if k + 1 = parts then h - k * size else size)
  let sums := tasks.foldl (fun acc t ↦ (acc.zip t.get).map fun (a, b) ↦ Words.addWords p a b w)
    (Array.replicate (d * zs.length) (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords w))
  zs.zipIdx.map fun (z, k) ↦
    let factor := Fri.cosetFactor logH gen z
    Array.ofFn (n := w) fun j ↦
      factor * FastExt.ofCoords fun c ↦ word (sums.getD (d * k + c) .empty) j

/-- Rows `r0, …, r0 + len - 1` of a packed matrix, within one block of its rows, batched by the
four coordinate planes `a 0, …, a 3`: four planes of `len` words in one buffer, the columns
multiply-added into all four four at a time, every column word read once and every word reduced
once per four columns (`Words.mulAdd4x4Into`); a last group short of four columns repeats the last
column with zero powers. -/
def compress4 (p : ℕ) [Mont32Field p] (m : @& PMat) (a : Nat → Nat → UInt32) (r0 len : Nat) :
    ByteArray :=
  let col (j : Nat) := m.colAt (min j (m.width - 1)) r0
  Merkle.Packed.foldRange (fun out g ↦
    Words.mulAdd4x4Into p out (col (4 * g)).1 (col (4 * g + 1)).1 (col (4 * g + 2)).1
      (col (4 * g + 3)).1 (col (4 * g)).2 (col (4 * g + 1)).2 (col (4 * g + 2)).2
      (col (4 * g + 3)).2 (a 0 (4 * g)) (a 0 (4 * g + 1)) (a 0 (4 * g + 2))
      (a 0 (4 * g + 3)) (a 1 (4 * g)) (a 1 (4 * g + 1)) (a 1 (4 * g + 2))
      (a 1 (4 * g + 3)) (a 2 (4 * g)) (a 2 (4 * g + 1)) (a 2 (4 * g + 2))
      (a 2 (4 * g + 3)) (a 3 (4 * g)) (a 3 (4 * g + 1)) (a 3 (4 * g + 2))
      (a 3 (4 * g + 3)) len)
    ((m.width + 3) / 4) 0 (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords (4 * len))

/-- Rows `r0, …, r0 + len - 1` of a packed matrix, within one block of its rows, batched into one
coordinate plane by the column weights `a j`: the columns multiply-added four at a time, every word
reduced once per four columns (`Words.mulAdd4Into`); a last group short of four columns repeats the
last column with zero weights. -/
def compress1 (p : ℕ) [Mont32Field p] (m : @& PMat) (a : Nat → UInt32) (r0 len : Nat) :
    ByteArray :=
  let col (j : Nat) := m.colAt (min j (m.width - 1)) r0
  Merkle.Packed.foldRange (fun out g ↦
    Words.mulAdd4Into p out (col (4 * g)).1 (col (4 * g + 1)).1 (col (4 * g + 2)).1
      (col (4 * g + 3)).1 (col (4 * g)).2 (col (4 * g + 1)).2 (col (4 * g + 2)).2
      (col (4 * g + 3)).2 (a (4 * g)) (a (4 * g + 1)) (a (4 * g + 2)) (a (4 * g + 3)) len)
    ((m.width + 3) / 4) 0 (CompPoly.CPolynomial.NTTFast.Packed.Native.zeroWords len)

/-- Word `j` of plane `c` of the planes `a`, zero past the planes or the matrix's columns. -/
@[inline] def planeWord (m : @& PMat) (a : @& Array ByteArray) (c j : Nat) : UInt32 :=
  if c < a.size ∧ j < m.width then
    CompPoly.CPolynomial.NTTFast.Packed.Native.read (a.getD c .empty) j
  else 0

/-- Rows `r0, …, r0 + len - 1` of a packed matrix, within one block of its rows, batched by the
coordinate planes `a` of the powers of `α`: the planes four at a time (`compress4`), the last up
to three one at a time (`compress1`). -/
def compressRange (p : ℕ) [Mont32Field p] (m : @& PMat) (a : @& Array ByteArray) (r0 len : Nat) :
    Array ByteArray :=
  (Array.range ((a.size + 3) / 4)).flatMap fun q ↦
    if min 4 (a.size - 4 * q) = 4 then
      let out := compress4 p m (fun c j ↦ planeWord m a (4 * q + c) j) r0 len
      (Array.range (min 4 (a.size - 4 * q))).map fun c ↦ out.extract (4 * (c * len))
        (4 * ((c + 1) * len))
    else
      (Array.range (min 4 (a.size - 4 * q))).map fun c ↦
        compress1 p m (planeWord m a (4 * q + c)) r0 len

/-- `sums` with `(y, c)` added to the sums of the point `z`, a new point last. -/
def addToPoint (z y : EF) (c : ExtPlanes p EF) :
    List (EF × EF × ExtPlanes p EF) → List (EF × EF × ExtPlanes p EF)
  | [] => [(z, y, c)]
  | e :: es => if e.1 == z then (z, e.2.1 + y, e.2.2.add c) :: es else e :: addToPoint z y c es

/-- Rows `r0, …, r0 + len - 1` of the batched quotient of one height: for every matrix, its rows
batched by the planes `a` of the powers of `α`, and for every point `(z, yz, offset)` of it,
`offset · yz` and `offset · comp` added to the sums `Y` and `D` of `z`; then `(Y - D) / (z - x)`
summed over the points, `1 / (z - x)` from `invs`. -/
def reduceRange (invs : @& List (EF × Nat × ExtPlanes p EF))
    (items : @& Array (PMat × ExtPlanes p EF × List (EF × EF × EF))) (r0 len : Nat) :
    ExtPlanes p EF := Id.run do
  let mut sums : List (EF × EF × ExtPlanes p EF) := []
  for (m, a, pts) in items do
    let comp := compressRange p m a.c.toArray r0 len
    let comp : ExtPlanes p EF := ⟨len, Vector.ofFn fun k ↦ comp.getD k .empty⟩
    for (z, yz, offset) in pts do
      sums := addToPoint z (offset * yz) (comp.smul offset) sums
  return sums.foldl (fun acc (z, y, c) ↦
    acc.add ((ExtPlanes.rsub y c).mul (slicePlanes (denomsOf invs z) r0 len))) (ExtPlanes.zeros len)

/-- `Fri.reduce` on planes, every height in parallel ranges of rows within one block of every
matrix: rows batched column by column, `1 / (z - x)` from `invs`. -/
def reduce [Mont32BaseField p] [Mont32.AlgebraId EF] (invs : List (EF × Nat × ExtPlanes p EF))
    (alpha : EF)
    (items : List (PMat × List (EF × Array EF))) :
    List (Nat × ExtPlanes p EF) :=
  Id.run do
  -- Per height: the matrices with their points, opened sums and powers of `α`, in order.
  let mut groups : List (Nat × Nat × Array (PMat × ExtPlanes p EF × List (EF × EF × EF))) := []
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
    groups := (logH, cnt, g.push (m, ExtPlanes.ofArray ap, terms)) ::
      groups.filter (·.1 != logH)
  let out := groups.map fun (logH, _, g) ↦
    let n := 2 ^ logH
    let parts := n / g.foldl (fun a (m, _) ↦ Nat.gcd a m.rows) (if n < 4096 then n else n / 16)
    let size := n / parts
    let ts := (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
      (reduceRange invs g (k * size) (if k + 1 = parts then n - k * size else size)).c.toArray
    (logH, ExtPlanes.join n ts)
  return out.mergeSort fun a b ↦ b.1 ≤ a.1

/-- The opened values and the batched reduction on planes, `1 / (z - x)` computed once per point
on its tallest height (`denoms`) for both. -/
def openings [Mont32BaseField p] [Mont32.AlgebraId EF] (b : Nat)
    (rounds : List (List (PMat × List EF))) :
    List (List (List (Array EF))) × (EF → List (Nat × ExtPlanes p EF)) :=
  let invs := denoms rounds.flatten
  let ov := rounds.map (·.map fun x ↦ openedAt invs b x.1 x.2)
  (ov, fun alpha ↦ reduce invs alpha (Fri.openItems rounds ov))

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
def fold2Range (v : @& ExtPlanes p EF) (twoX : @& ByteArray) (beta : EF) (r0 len : Nat) :
    ExtPlanes p EF :=
  let split (b : ByteArray) := deinterleave (slice b (2 * r0) (2 * len)) len
  let halves := v.c.map split
  let lo : ExtPlanes p EF := ⟨len, halves.map (·.1)⟩
  let hi : ExtPlanes p EF := ⟨len, halves.map (·.2)⟩
  let inv2x := Words.batchInvRange p twoX r0 len
  ((lo.add hi).mulBase (Words.replicateWord ((2 : F)⁻¹).val len)).add (((lo.sub hi).mulBase inv2x).smul beta)

/-- `Fri.foldPairs` on planes, `(lo + hi) / 2 + β (lo - hi) / (2 x)`, in parallel ranges. -/
def fold2 [Mont32BaseField p] (v : ExtPlanes p EF) (beta : EF) (logRows : Nat) : ExtPlanes p EF :=
  let rows := 2 ^ logRows
  let pw := cosetPoints (1 : F) (logRows + 1)
  let twoX := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    ((bitRevPerm logRows).map fun i ↦ 2 * pw.getD i 0)
  let parts := if rows < 4096 then 1 else 16
  let size := rows / parts
  ExtPlanes.join rows <| (Array.range parts).map fun k ↦ Task.spawn fun _ ↦
    (fold2Range v twoX beta (k * size) (if k + 1 = parts then rows - k * size else size)).c.toArray

/-- `Fri.foldOnce` on planes: the arity-2 fold `fold2`, otherwise every group's `foldRow`, in
parallel ranges of rows. -/
def fold [Mont32BaseField p] [Mont32.AlgebraId EF] (la : Nat) (beta : EF) (v : ExtPlanes p EF) :
    ExtPlanes p EF :=
  let rows := v.n / 2 ^ la
  if la = 1 then fold2 v beta (Nat.log2 rows) else
    let vs := v.toArray
    ExtPlanes.ofArray (parChunks rows (if rows < 1024 then 1 else 16) fun r0 len ↦
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
`d i + c` holds coordinate `c` of the `i`-th element of every row, gathered by parallel tasks. -/
def leaves (k : Nat) (v : ExtPlanes p EF) : PMat :=
  let d := FastExt.d p EF
  let h := v.n / k
  ⟨d * k, h, h, (CompPoly.Tasks.join (CompPoly.Tasks.spawnAll (d * k) fun j ↦
    strided (v.c.toArray.getD (j % d) .empty) (j / d) k h)).get⟩

/-- `a + x · b`. -/
def addScaled (a b : ExtPlanes p EF) (x : EF) : ExtPlanes p EF := a.add (b.smul x)

variable [Mont32BaseField p] [Mont32.AlgebraId EF] [PlanesInv p EF] [Poseidon2Field (FastField p)]
  [PackedPoseidon2 p]

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
  V := ExtPlanes p EF
  toArray := ExtPlanes.toArray
  ofArray := ExtPlanes.ofArray
  size := (·.n)
  openings := Fast.openings
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
