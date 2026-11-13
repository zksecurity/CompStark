/-
Copyright (c) 2026 zkSecurity.
Adapted from leanEthereum/leanMultisig (Apache-2.0), revision
9d8bce818aa7c7e18e67026e522a9b1539d0a57d, crates/keccak_gkr/src/{witness,prover,open,protocol}.rs.
-/
module

public import Mathlib.Data.Erased
public import CompStark.Keccak.GkrProver.Kernels
public import CompStark.Keccak.GkrProver.Rmfe
public import CompStark.Keccak.Duplex
public import CompStark.BinaryFields.Basic

/-! Word-backed two-segment Keccak GKR messages and retained opening claims. -/

set_option maxRecDepth 32768
set_option compiler.maxRecInline 0

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak BF64
open scoped BigOperators

/-- The proven three-word extension-field carrier. -/
abbrev W := WordExt3

/-- Embed a polynomial-basis lane as the constant extension coefficient. -/
@[inline] def lane (w : UInt64) : W := ⟨⟨w⟩, ⟨0⟩, ⟨0⟩⟩

/-- Row shift with little-endian slices and `x+5*y` lanes. -/
@[inline] def shift (j k : Nat) : Nat :=
  64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64

/-- Fill both Boolean equality blocks with one shared-scalar product per source entry. -/
def eqTableStepLoop (table : Array W) (r : W) : Nat → Array W → Array W
  | 0, out => out
  | n+1, out =>
    let a := table[n]!
    let b := WordExt3.mul r a
    eqTableStepLoop table r n ((out.set! n (WordExt3.add a b)).set! (table.size+n) b)

/-- Fill a large equality block with one multiplier prepared for its entire coordinate. -/
def eqTablePreparedLoop (table : Array W) (map : CompStark.Sumcheck.Prepared) : Nat → Array W → Array W
  | 0, out => out
  | n+1, out =>
    let a := table[n]!
    let b := map.mul a
    eqTablePreparedLoop table map n ((out.set! n (WordExt3.add a b)).set! (table.size+n) b)

/-- Extend an equality table by one Boolean coordinate with a single scalar product per entry. -/
def eqTableStep (table : Array W) (r : W) : Array W :=
  let out := Array.replicate (2*table.size) (lane 0)
  if 1024 ≤ table.size then
    eqTablePreparedLoop table (CompStark.Sumcheck.prepare r) table.size out
  else eqTableStepLoop table r table.size out

/-- All Boolean equality weights, in little-endian variable order. -/
def eqTable (point : Array W) : Array W := Id.run do
  let mut out := #[lane 1]
  for r in point do out := eqTableStep out r
  return out

/-- Horner evaluation, constant coefficient first. -/
def evaluate (coeffs : Array W) (r : W) : W :=
  coeffs.foldr (fun c acc => c+r*acc) 0

/-- One array coordinate folded with a multiplier shared by all tables in a round. -/
@[inline] def foldArrayCell (table : Array W) (width : Nat)
    (map : CompStark.Sumcheck.Prepared) (i : Nat) : W :=
  let offset := 2*(i/width)*width+i%width
  let a := table[offset]!
  WordExt3.add a (map.mul (WordExt3.add a table[offset+width]!))

/-- Descending scalar loop for a prepared array fold. -/
def foldArrayLoop (table : Array W) (width : Nat) (map : CompStark.Sumcheck.Prepared) :
    Nat → Array W → Array W
  | 0, out => out
  | n+1, out => foldArrayLoop table width map n (out.set! n (foldArrayCell table width map n))

/-- Fold an array using a multiplier prepared once for every table sharing the round challenge. -/
def foldArrayShared (table : Array W) (width : Nat) (map : CompStark.Sumcheck.Prepared) : Array W :=
  let count := table.size/(2*width)*width
  foldArrayLoop table width map count (Array.replicate count (lane 0))

/-- Dot product of equally shaped field vectors. -/
def dot (a b : Array W) : W := Id.run do
  let mut out : W := 0
  for i in [:a.size] do out := out+a[i]!*b[i]!
  return out

/-- Sum of a field buffer. -/
def sum (a : Array W) : W := a.foldl (·+·) 0

/-- Subset sums of sixteen entries, indexed by a packed Boolean assignment. -/
def subsets (values : Array W) : Array W := Id.run do
  let mut out := #[lane 0]
  for value in values do
    out := out ++ out.map (·+value)
  return out

/-- Successive extension powers evaluated entirely with the certified word kernel. -/
def wordPower (s : W) : Nat → W
  | 0 => lane 1
  | n+1 => WordExt3.mul s (wordPower s n)

/-- The word power kernel computes the field power. -/
theorem wordPower_eq (s : W) (n : Nat) : wordPower s n = s^n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [wordPower, ih]
    change s*s^n = s^(n+1)
    exact (pow_succ' s n).symm

/-- Sum a dimension-indexed word vector with explicit word addition and identity. -/
def wordSum : (n : Nat) → (Fin n → W) → W
  | 0, _ => lane 0
  | n+1, f => WordExt3.add (f 0) (wordSum n (fun i => f i.succ))

/-- The explicit word sum computes the ring sum. -/
theorem wordSum_eq (n : Nat) (f : Fin n → W) : wordSum n f = ∑ i, f i := by
  induction n with
  | zero => simp only [wordSum, Fin.sum_univ_zero]; rfl
  | succ n ih =>
    rw [wordSum, Fin.sum_univ_succ, ih]
    rfl

/-- Evaluate every RMFE unit column at the layer challenge. -/
def instanceWeights (s : W) : Array W :=
  let powers := Array.ofFn fun c : Fin 24 => wordPower s c.val
  Array.ofFn fun i : Fin 16 =>
    let bits := embeddingColumns[i.val]!
    wordSum 24 fun c => if bits.testBit c.val then powers[c.val]! else lane 0

/-- A sliced round occupies one word per position and group of 64 instances. -/
structure SlicedWitness where
  /-- Logarithmic number of padded permutations, at least nine. -/
  nLog : Nat
  /-- Input bits followed by each round's pre-chi bits. -/
  layers : Array (Array UInt64)
  /-- Final output lanes, in slot-major order. -/
  outputs : Array UInt64

/-- Materialized lane rotations share the protocol's finite lookup table. -/
def rotations : Array Nat := Array.ofFn Gkr.rho

/-- Materialized public round constants, in zero-indexed round order. -/
def constants : Array UInt64 := Array.ofFn fun r : Fin 24 => (Gkr.roundConstants r).toUInt64

/-- Theta, rho and pi on 64 simultaneous states per word. -/
def linearSlices (state : Array UInt64) (groups : Nat) : Array UInt64 :=
  let columns := Array.ofFn fun i : Fin (320*groups) =>
    let c := i.val/groups
    let g := i.val%groups
    state[c*groups+g]! ^^^ state[(c+320)*groups+g]! ^^^
      state[(c+640)*groups+g]! ^^^ state[(c+960)*groups+g]! ^^^ state[(c+1280)*groups+g]!
  Array.ofFn fun i : Fin (1600*groups) =>
    let j := i.val/groups
    let g := i.val%groups
    let l := (Gkr.inversePi (j/64)).val
    let z := (j%64+64-rotations[l]!)%64
    state[(64*l+z)*groups+g]! ^^^
      columns[(64*((l%5+4)%5)+z)*groups+g]! ^^^
      columns[(64*((l%5+1)%5)+(z+63)%64)*groups+g]!

/-- Chi and the numbered iota constant on a sliced state. -/
def chiSlices (state : Array UInt64) (groups round : Nat) : Array UInt64 :=
  Array.ofFn fun i : Fin (1600*groups) =>
    let j := i.val/groups
    let g := i.val%groups
    let a := state[i.val]! ^^^
      (~~~state[shift j 1*groups+g]! &&& state[shift j 2*groups+g]!)
    if j < 64 && (constants[round%24]!.toNat).testBit j then ~~~a else a

/-- Slice the input lanes, run all 24 rounds, and retain each pre-chi state. -/
def buildWitness (nLog : Nat) (committed : Array UInt64) : SlicedWitness := Id.run do
  let n := 2^nLog
  let groups := n/64
  let mut state := Array.replicate (1600*groups) (0 : UInt64)
  for l in [:25] do
    for z in [:64] do
      for g in [:groups] do
        let mut word : UInt64 := 0
        for b in [:64] do
          word := word ||| (((committed[l*n+64*g+b]! >>> z.toUInt64) &&& 1) <<< b.toUInt64)
        state := state.set! ((64*l+z)*groups+g) word
  let mut layers := #[state]
  for r in [:24] do
    let preChi := linearSlices state groups
    layers := layers.push preChi
    state := chiSlices preChi groups r
  let outputs := Array.ofFn fun i : Fin (25*n) => Id.run do
    let l := i.val/n
    let b := i.val%n
    let mut word : UInt64 := 0
    for z in [:64] do
      word := word ||| (((state[(64*l+z)*groups+b/64]! >>> (b%64).toUInt64) &&& 1) <<< z.toUInt64)
    return word
  return ⟨nLog, layers, outputs⟩

/-- One sixteen-instance assignment from a sliced pre-chi state. -/
@[inline] def packBits (w : SlicedWitness) (d row j : Nat) : Nat :=
  let packs := 2^(w.nLog-4)
  let b := row%packs
  let m := row/packs
  let state := w.layers[12*(m+1)-d]!
  ((state[j*(2^w.nLog/64)+b/4]! >>> (16*(b%4)).toUInt64) &&& 65535).toNat

/-- One transcript operation of the writer: a written scalar or a drawn challenge. -/
inductive WriterEvent where
  /-- A scalar absorbed with domain tag one. -/
  | write (a : W)
  /-- A challenge squeezed. -/
  | sample

/-- Mutable transcript transport, retaining every challenge for conformance checks. -/
structure Writer where
  /-- Pending scalar framing and carried Keccak capacity. -/
  state : CompStark.Keccak.Duplex.State ⟨16, by decide, by decide⟩ Unit
  /-- Sent scalars, excluding challenges and reconstructed coefficients. -/
  stream : Array W := #[]
  /-- Challenges in squeeze order. -/
  challenges : Array W := #[]
  /-- Every write and sample in order, erased at run time. -/
  log : Erased (List WriterEvent) := Erased.mk []

/-- Seed with the two fixed statement digests, without absorbing derived lane claims. -/
def Writer.seed (iv input : Array UInt64) : Writer := Id.run do
  let s := CompStark.Keccak.f1600 (Array.ofFn fun i : Fin 25 =>
    if i.val < 4 then iv[i.val]! else if i.val < 8 then input[i.val-4]! else 0)
  let cleared := s.mapIdx fun i a => if i < 16 then 0 else a
  return ⟨⟨cleared, by simp only [cleared, Array.size_mapIdx, s, CompStark.Keccak.Duplex.fast_width],
    0, by decide, ()⟩, #[], #[], Erased.mk []⟩

/-- Transmit and bind one scalar with domain tag one. -/
def Writer.write (writer : Writer) (a : W) : Writer :=
  let lanes := #[a.c0.val, a.c1.val, a.c2.val, 1]
  { writer with
    state := CompStark.Keccak.Duplex.absorb _ (fun _ _ _ => ()) writer.state lanes
    stream := writer.stream.push a
    log := writer.log.map (· ++ [.write a]) }

/-- Transmit a buffer in scalar order. -/
def Writer.writeAll (writer : Writer) (a : Array W) : Writer := a.foldl Writer.write writer

/-- Each sample permutes independently and returns its first three output lanes. -/
def Writer.sample (writer : Writer) : W × Writer :=
  let (out, state) := CompStark.Keccak.Duplex.sample _ (fun _ _ _ => ()) writer.state 3 (by decide)
  let a : W := ⟨⟨out[0]!⟩, ⟨out[1]!⟩, ⟨out[2]!⟩⟩
  (a, { writer with
    state := state
    challenges := writer.challenges.push a
    log := writer.log.map (· ++ [.sample]) })

/-- Draw separate permutations for a vector of field challenges. -/
def Writer.sampleMany (writer : Writer) (n : Nat) : Array W × Writer := Id.run do
  let mut writer := writer
  let mut out := #[]
  for _ in [:n] do
    let (r, next) := writer.sample
    writer := next
    out := out.push r
  return (out, writer)

/-- Numeric form of the protocol's running weighted claim. -/
structure Claim where
  /-- Claimed field value. -/
  value : W
  /-- Sixteen instance weights. -/
  mu : Array W
  /-- Pack coordinates followed by segment coordinate. -/
  point : Array W
  /-- The 1600 position weights. -/
  weights : Array W

/-- Position weights retained as three consecutive scalar words. -/
def weightDigits (weights : Array W) : FixedWords 4800 := Id.run do
  let mut out := zeroWords 4800
  for j in [:1600] do
    let w := weights[j]!
    out := writeWord out (3*j) w.c0.val
    out := writeWord out (3*j+1) w.c1.val
    out := writeWord out (3*j+2) w.c2.val
  return out

/-- Add a position's three weight words to the bucket selected by one polynomial digit. -/
@[inline] def scatterDigit (buckets : FixedWords (6*256*3)) (digit : USize)
    (value w0 w1 w2 : UInt64) : FixedWords (6*256*3) :=
  let offset := 3*(256*digit+(value &&& 255).toUSize)
  let buckets := writeUWord buckets offset (readUWord buckets offset ^^^ w0)
  let buckets := writeUWord buckets (offset+1) (readUWord buckets (offset+1) ^^^ w1)
  writeUWord buckets (offset+2) (readUWord buckets (offset+2) ^^^ w2)

/-- Scatter all six digits with scalar tail-recursive loop state. -/
def scatterPayload (payload : FixedWords 1600) (weights : FixedWords 4800)
    (j : Nat) (buckets : FixedWords (6*256*3)) : FixedWords (6*256*3) :=
  if _h : j < 1600 then
    let i := j.toUSize
    let p := readUWord payload i
    let w0 := readUWord weights (3*i)
    let w1 := readUWord weights (3*i+1)
    let w2 := readUWord weights (3*i+2)
    let buckets := scatterDigit buckets 0 p w0 w1 w2
    let buckets := scatterDigit buckets 1 (p >>> 8) w0 w1 w2
    let buckets := scatterDigit buckets 2 (p >>> 16) w0 w1 w2
    let buckets := scatterDigit buckets 3 (p >>> 24) w0 w1 w2
    let buckets := scatterDigit buckets 4 (p >>> 32) w0 w1 w2
    let buckets := scatterDigit buckets 5 (p >>> 40) w0 w1 w2
    scatterPayload payload weights (j+1) buckets
  else buckets
termination_by 1600-j

/-- A reduced bucket column, with the folded source buffer retained for the next bit. -/
structure BucketColumn where
  /-- Folded digit buckets. -/
  buckets : FixedWords (6*256*3)
  /-- Constant extension coordinate. -/
  c0 : UInt64
  /-- Linear extension coordinate. -/
  c1 : UInt64
  /-- Quadratic extension coordinate. -/
  c2 : UInt64

/-- Reduce a digit bit with scalar loop state and no iteration closures. -/
def reduceBucketColumn (digit width : USize) : Nat → FixedWords (6*256*3) →
    UInt64 → UInt64 → UInt64 → BucketColumn
  | 0, buckets, c0, c1, c2 => ⟨buckets,c0,c1,c2⟩
  | n+1, buckets, c0, c1, c2 =>
    let low := 3*(256*digit+n.toUSize)
    let high := low+3*width
    let h0 := readUWord buckets high
    let h1 := readUWord buckets (high+1)
    let h2 := readUWord buckets (high+2)
    let buckets := writeUWord buckets low (readUWord buckets low ^^^ h0)
    let buckets := writeUWord buckets (low+1) (readUWord buckets (low+1) ^^^ h1)
    let buckets := writeUWord buckets (low+2) (readUWord buckets (low+2) ^^^ h2)
    reduceBucketColumn digit width n buckets (c0 ^^^ h0) (c1 ^^^ h1) (c2 ^^^ h2)

/-- Sum binary polynomial payloads by their six byte digits, retaining extension-weight XORs. -/
def weightedPayload (payload : FixedWords 1600) (weights : FixedWords 4800) : PackedE := Id.run do
  let mut buckets := scatterPayload payload weights 0 (zeroWords (6*256*3))
  let mut out := PackedE.zeros 47
  let mut digit : USize := 0
  while digit < 6 do
    let mut width : USize := 128
    let mut bit : USize := 7
    while width != 0 do
      let column := reduceBucketColumn digit width width.toNat buckets 0 0 0
      buckets := column.buckets
      if (8*digit+bit).toNat < 47 then
        out := out.set (8*digit+bit).toNat ⟨⟨column.c0⟩,⟨column.c1⟩,⟨column.c2⟩⟩
      width := width >>> 1
      bit := bit-1
    digit := digit+1
  return out

/-- Machine-indexed row shifts on the 1600 little-endian positions. -/
@[inline] def shiftU (j k : USize) : USize :=
  64*((j/64%5+k)%5+5*(j/64/5))+j%64

/-- Generate one row's binary products with scalar recursive loop state. -/
def productPayload (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (maps : RmfeProducts) (j : Nat) (out : FixedWords 1600) : FixedWords 1600 :=
  if _h : j < 1600 then
    let k := j.toUSize
    let a := (state[(k*groups+offset).toNat]! >>> bits) &&& 65535
    let b := (state[(shiftU k 1*groups+offset).toNat]! >>> bits) &&& 65535
    let c := (state[(shiftU k 2*groups+offset).toNat]! >>> bits) &&& 65535
    let p := maps.ones (a ^^^ c) ^^^ maps.mul b c
    productPayload state groups offset bits maps (j+1) (writeUWord out k p)
  else out
termination_by 1600-j

/-- The product message and each pack's position-weighted polynomial. -/
structure ProductData where
  /-- The 47 coefficients transmitted to the verifier. -/
  message : Array W
  /-- Unbatched polynomials in segment-major pack order. -/
  packs : Array PackedE

/-- Horner evaluation of a packed prefix with one shared prepared challenge. -/
def evaluatePackedLoop (coeffs : PackedE) (map : CompStark.Sumcheck.Prepared) : Nat → W → W
  | 0, acc => acc
  | n+1, acc => evaluatePackedLoop coeffs map n (WordExt3.add (coeffs.get n) (map.mul acc))

/-- The 47 product coefficients and the retained polynomials for binary tensor points. -/
def product (w : SlicedWitness) (d : Nat) (claim : Claim) (maps : RmfeProducts) : ProductData := Id.run do
  let packs := 2^(w.nLog-4)
  let groups := 2^w.nLog/64
  let eq := eqTable claim.point
  let digits := weightDigits claim.weights
  let mut result := Array.replicate 47 (lane 0)
  let mut retained := #[]
  for m in [:2] do
    let state := w.layers[12*(m+1)-d]!
    for b in [:packs] do
      let payload := productPayload state groups.toUSize (b/4).toUSize
        (16*(b%4)).toUInt64 maps 0 (zeroWords 1600)
      let coeffs := weightedPayload payload digits
      retained := retained.push coeffs
      let weight := eq[m*packs+b]!
      for k in [:47] do
        result := result.set! k (WordExt3.add result[k]! (WordExt3.mul weight (coeffs.get k)))
  return ⟨result, retained⟩

/-- Reuse the product polynomials at the sixteen binary early-round assignments. -/
def binaryValues (polynomials : Array PackedE) (point : Array W)
    (map : CompStark.Sumcheck.Prepared) : Array W := Id.run do
  let eq := eqTable (point.extract 4 point.size)
  let mut values := Array.replicate 16 (lane 0)
  for b in [:polynomials.size] do
    let coeffs := polynomials[b]!
    let value := evaluatePackedLoop coeffs map coeffs.size (lane 0)
    let i := b%16
    values := values.set! i (WordExt3.add values[i]! (WordExt3.mul eq[b/16]! value))
  return values

/-- Byte-subset tables for the sixteen packs after binding the first four coordinates. -/
def foldedPackMaps (mu point : Array W) : Array (Array W × Array W) :=
  let eq := eqTable point
  Array.ofFn fun q : Fin 16 =>
    let values := mu.map fun x => WordExt3.mul eq[q.val]! x
    (subsets (values.extract 0 8), subsets (values.extract 8 16))

/-- Evaluate and fold sixteen binary packs before allocating the retained extension table. -/
def packedTable (w : SlicedWitness) (d : Nat) (mu point : Array W) : PackedE := Id.run do
  let maps := foldedPackMaps mu point
  let packs := 2^(w.nLog-4)
  let groups := 2^w.nLog/64
  let rows := packs/16
  let mut out := PackedE.zeros (2*rows*1600)
  for m in [:2] do
    let state := w.layers[12*(m+1)-d]!
    for b in [:rows] do
      let offset := (m*rows+b)*1600
      for j in [:1600] do
        let mut value := lane 0
        for q in [:16] do
          let bits := state[j*groups+4*b+q/4]! >>> (16*(q%4)).toUInt64
          let (low,high) := maps[q]!
          value := WordExt3.add value (WordExt3.add low[(bits &&& 255).toNat]!
            high[((bits >>> 8) &&& 255).toNat]!)
        out := out.set (offset+j) value
  return out

/-- Ternary tensor coordinates: a Boolean pack, or the two lower-index endpoints of an infinity digit. -/
def ternaryPlan : Array (Nat × Nat) := Array.ofFn fun q : Fin 81 => Id.run do
  let mut binary := 0
  let mut divisor := 1
  let mut power := 1
  for _ in [:4] do
    let digit := q.val/divisor%3
    if digit = 2 then return (q.val-2*divisor, q.val-divisor)
    binary := binary+digit*power
    divisor := divisor*3
    power := power*2
  return (binary,81)

/-- Binary-point flags in the native ternary plan. -/
def ternaryBinary : ByteArray := ⟨Array.ofFn fun q : Fin 81 =>
  if (ternaryPlan[q.val]!).2 = 81 then (1 : UInt8) else 0⟩

/-- Fill a contiguous ternary row with machine-indexed scalar loop state. -/
def mixedRow (state : Array UInt64) (groups offset : USize) (bits : UInt64)
    (lo hi target : USize) (binary : Bool) (j : USize) (out : FixedDWords (81*1600)) : FixedDWords (81*1600) :=
  if _h : j < 1600 then
    let value := if binary then
      ((state[(j*groups+offset).toNat]! >>> bits) &&& 65535).toUInt32
    else readUDWord out (lo+j) ^^^ readUDWord out (hi+j)
    mixedRow state groups offset bits lo hi target binary (j+1) (writeUDWord out (target+j) value)
  else out
termination_by 1600-j.toNat
decreasing_by
  have hj : j.toNat < 1600 := by simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 1600 < 2^32) USize.le_size)] using _h
  rw [USize.toNat_add]
  have hs := USize.le_size
  have hn : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [hn]
  change 1600-((j.toNat+1)%USize.size) < 1600-j.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Raw sixteen-bit assignments on the four-coordinate ternary tensor. -/
def mixedEmbeddings (state : Array UInt64) (groups base : Nat) : FixedDWords (81*1600) := Id.run do
  let mut out := zeroDWords (81*1600)
  for q in [:81] do
    let (lo,hi) := ternaryPlan[q]!
    let b := base+lo
    out := mixedRow state groups.toUSize (b/4).toUSize (16*(b%4)).toUInt64
      (1600*lo).toUSize (1600*hi).toUSize (1600*q).toUSize (hi==81) 0 out
  return out

/-- A coordinate of a bounded three-word block is inside the position-map buffer. -/
theorem weightBlockBound (base count k c : USize)
    (hb : base.toNat+3*count.toNat ≤ 7372800) (hk : k.toNat < count.toNat)
    (hc : c.toNat < 3) : base+3*k+c < (7372800 : USize) := by
  have hs := USize.le_size
  have h3 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  have hn : (7372800 : USize).toNat = 7372800 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  simp only [USize.lt_iff_toNat_lt, USize.toNat_add, USize.toNat_mul, h3, hn]
  change ((base.toNat+(3*k.toNat)%USize.size)%USize.size+c.toNat)%USize.size < 7372800
  have hm := Nat.mod_le (3*k.toNat) USize.size
  have ha := Nat.mod_le (base.toNat+(3*k.toNat)%USize.size) USize.size
  have hz := Nat.mod_le ((base.toNat+(3*k.toNat)%USize.size)%USize.size+c.toNat) USize.size
  omega

/-- Extend one byte table with machine loop state and erased access bounds. -/
def extendWeightByte (n source target : USize) (c0 c1 c2 : UInt64)
    (out : FixedWords (1600*6*256*3))
    (hs : source.toNat+3*n.toNat ≤ 7372800)
    (ht : target.toNat+3*n.toNat ≤ 7372800) : FixedWords (1600*6*256*3) :=
  if hn : n = 0 then out else
    have hn1 : (1 : USize) ≤ n := by
      rw [USize.le_iff_toNat_le, USize.toNat_one]
      have : n.toNat ≠ 0 := by intro h; apply hn; exact USize.toNat_inj.mp h
      omega
    have hk : (n-1).toNat < n.toNat := by
      rw [USize.toNat_sub_of_le _ _ hn1, USize.toNat_one]
      have : 1 ≤ n.toNat := by simpa only [USize.le_iff_toNat_le, USize.toNat_one] using hn1
      omega
    let k := n-1
    let p0 := weightBlockBound source n k 0 hs hk (usize_toNat_lt (by decide) (by decide))
    let p1 := weightBlockBound source n k 1 hs hk (usize_toNat_lt (by decide) (by decide))
    let p2 := weightBlockBound source n k 2 hs hk (usize_toNat_lt (by decide) (by decide))
    let q0 := weightBlockBound target n k 0 ht hk (usize_toNat_lt (by decide) (by decide))
    let q1 := weightBlockBound target n k 1 ht hk (usize_toNat_lt (by decide) (by decide))
    let q2 := weightBlockBound target n k 2 ht hk (usize_toNat_lt (by decide) (by decide))
    let out := setUWord out (target+3*k+0) q0 (getUWord out (source+3*k+0) p0 ^^^ c0)
    let out := setUWord out (target+3*k+1) q1 (getUWord out (source+3*k+1) p1 ^^^ c1)
    let out := setUWord out (target+3*k+2) q2 (getUWord out (source+3*k+2) p2 ^^^ c2)
    extendWeightByte k source target c0 c1 c2 out (by dsimp [k]; omega) (by dsimp [k]; omega)
termination_by n.toNat

/-- Position-weighted powers formed with one shared prepared challenge. -/
def successiveWeights (map : CompStark.Sumcheck.Prepared) : Nat → W → List W
  | 0, _ => []
  | n+1, a => a :: successiveWeights map n (map.mul a)

/-- Every prepared recurrence entry is the exact weighted field power. -/
theorem successiveWeights_eq (s a : W) (n : Nat) :
    successiveWeights (CompStark.Sumcheck.prepare s) n a = List.ofFn (fun i : Fin n => a*s^i.val) := by
  induction n generalizing a with
  | zero => simp only [successiveWeights, List.ofFn_zero]
  | succ n ih =>
    rw [successiveWeights, ih, List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Fin.val_zero, pow_zero, mul_one]
    · apply congrArg (fun f : Fin n → W => List.ofFn f)
      funext i
      rw [CompStark.Sumcheck.prepared_mul_eq]
      change s*a*s^i.val = a*s^(i.val+1)
      rw [pow_succ']
      exact (mul_assoc s a _).trans (mul_left_comm s a _)

/-- Position-map byte bases are exact machine-linear offsets. -/
theorem weightSource_eq (j byte : Nat) :
    (4608*j.toUSize+768*byte.toUSize : USize) = (3*(1536*j+256*byte)).toUSize := by
  have h : 3*(1536*j+256*byte) = 4608*j+768*byte := by omega
  rw [h]
  simp only [Nat.toUSize, USize.ofNat_add, USize.ofNat_mul]
  rfl

/-- A bounded machine shift is the exact subset-table width. -/
theorem weightWidth_eq (bit : Nat) (hb : bit < 8) :
    ((1 : USize) <<< bit.toUSize) = (2^bit).toUSize := by
  apply USize.toNat_inj.mp
  have hb' : bit < USize.size := by have := USize.le_size; omega
  have hp : bit < System.Platform.numBits := lt_of_lt_of_le hb System.Platform.eight_le_numBits
  rw [USize.toNat_shiftLeft, USize.toNat_one, USize.toNat_ofNat_of_lt' hb',
    Nat.mod_eq_of_lt hp, Nat.shiftLeft_eq, one_mul]
  rfl

/-- Linear maps from a 48-bit binary polynomial to its position-weighted evaluation at `s`. -/
def prepareWeightMaps (weights : Array W) (challenge : CompStark.Sumcheck.Prepared) : FixedWords (1600*6*256*3) := Id.run do
  let mut out := zeroWords (1600*6*256*3)
  for hj : j in [:1600] do
    let basis := (successiveWeights challenge 48 weights[j]!).toArray
    for hb : byte in [:6] do
      let source : USize := 4608*j.toUSize+768*byte.toUSize
      for hbit : bit in [:8] do
        let value := basis[8*byte+bit]!
        let width : USize := (1 : USize) <<< bit.toUSize
        have hj : j < 1600 := hj.upper
        have hb : byte < 6 := hb.upper
        have hbit : bit < 8 := hbit.upper
        have hwidth : width = (2^bit).toUSize := weightWidth_eq bit hbit
        have hsourceEq : source = (3*(1536*j+256*byte)).toUSize := weightSource_eq j byte
        have hw : 2^bit ≤ 128 := by
          change 2^bit ≤ 2^7
          exact Nat.pow_le_pow_right (by decide) (show bit ≤ 7 by omega)
        have hsmall : 3*(1536*j+256*byte)+6*2^bit ≤ 7372800 := by omega
        have hs : source.toNat+3*width.toNat ≤ 7372800 := by
          rw [hsourceEq, hwidth]
          rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega),
            USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
          omega
        have ht : (source+3*width).toNat+3*width.toNat ≤ 7372800 := by
          have hw' : width.toNat ≤ 128 := by
            rw [hwidth]
            rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
            exact hw
          have hsource : source.toNat+6*width.toNat ≤ 7372800 := by
            rw [hsourceEq, hwidth]
            rw [USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega),
              USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
            exact hsmall
          rw [USize.toNat_add, USize.toNat_mul]
          have h3 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
          rw [h3]
          change (source.toNat+(3*width.toNat)%USize.size)%USize.size+3*width.toNat ≤ 7372800
          have hm := Nat.mod_le (3*width.toNat) USize.size
          have ha := Nat.mod_le (source.toNat+(3*width.toNat)%USize.size) USize.size
          omega
        out := extendWeightByte width source (source+3*width)
          value.c0.val value.c1.val value.c2.val out hs ht
  return out

/-- A byte coordinate fits the prepared-map buffer on both machine widths. -/
theorem mapIndexBound (base : USize) (hb : base.toNat ≤ 7372800-768)
    (digit : UInt8) (c : USize) (hc : c.toNat < 3) :
    base+3*digit.toUSize+c < (7372800 : USize) := by
  have hd := digit.toNat_lt
  have hs := USize.le_size
  have h3 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  have hn : (7372800 : USize).toNat = 7372800 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  simp only [USize.lt_iff_toNat_lt, USize.toNat_add, USize.toNat_mul, UInt8.toNat_toUSize, h3, hn]
  change ((base.toNat+(3*digit.toNat)%USize.size)%USize.size+c.toNat)%USize.size < 7372800
  have h1 : 3*digit.toNat < USize.size := by omega
  have h2 : base.toNat+3*digit.toNat < USize.size := by omega
  have h3 : base.toNat+3*digit.toNat+c.toNat < USize.size := by omega
  simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  omega

/-- Every byte block stays inside its position map. -/
theorem mapBaseBound (base : USize) (hb : base.toNat ≤ 7372800-4608)
    (byte : USize) (hk : byte.toNat < 6) :
    (base+768*byte).toNat ≤ 7372800-768 := by
  have hs := USize.le_size
  have h768 : (768 : USize).toNat = 768 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_add, USize.toNat_mul, h768]
  have hm : 768*byte.toNat < USize.size := by omega
  rw [Nat.mod_eq_of_lt hm]
  exact le_trans (Nat.mod_le _ _) (by omega)

/-- Read one prepared byte using only machine offsets and erased bounds proofs. -/
@[inline] def weightByte (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (byte : USize) (hk : byte.toNat < 6)
    (c : USize) (hc : c.toNat < 3) (digit : UInt8) : UInt64 :=
  getUWord maps (base+768*byte+3*digit.toUSize+c) (mapIndexBound _ (mapBaseBound base hb byte hk) digit c hc)

/-- The prepared byte read equals the checked packed-buffer read at the same coordinate. -/
theorem weightByte_eq (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (byte : USize) (hk : byte.toNat < 6)
    (c : USize) (hc : c.toNat < 3) (digit : UInt8) :
    weightByte maps base hb byte hk c hc digit =
      readUWord maps (base+768*byte+3*digit.toUSize+c) :=
  getUWord_eq_readUWord maps _ _

/-- Evaluate one extension coordinate using six proved machine-indexed reads. -/
@[inline] def evalWeightCoordinate (maps : FixedWords (1600*6*256*3)) (base : USize)
    (hb : base.toNat ≤ 7372800-4608) (c : USize) (hc : c.toNat < 3) (p : UInt64) : UInt64 :=
  weightByte maps base hb 0 (usize_toNat_lt (by decide) (by decide)) c hc p.toUInt8 ^^^
  weightByte maps base hb 1 (usize_toNat_lt (by decide) (by decide)) c hc (p >>> 8).toUInt8 ^^^
  weightByte maps base hb 2 (usize_toNat_lt (by decide) (by decide)) c hc (p >>> 16).toUInt8 ^^^
  weightByte maps base hb 3 (usize_toNat_lt (by decide) (by decide)) c hc (p >>> 24).toUInt8 ^^^
  weightByte maps base hb 4 (usize_toNat_lt (by decide) (by decide)) c hc (p >>> 32).toUInt8 ^^^
  weightByte maps base hb 5 (usize_toNat_lt (by decide) (by decide)) c hc (p >>> 40).toUInt8

/-- Row-major tensor coordinates stay in bounds on both machine widths. -/
theorem tensorWordIndex (q : Nat) (hq : q < 81) (width : Fin 1601)
    (j : USize) (hj : j.toNat < width.val) :
    width.val.toUSize*q.toUSize+j < (81*width.val).toUSize := by
  have hs := USize.le_size
  have hw := width.isLt
  have hq' : q.toUSize.toNat = q := by rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]
  have hw' : width.val.toUSize.toNat = width.val := by rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]
  have hn' : (81*width.val).toUSize.toNat = 81*width.val := by rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]
  have hprod : width.val*q < USize.size := by nlinarith
  have hsum : width.val*q+j.toNat < USize.size := by nlinarith
  rw [USize.lt_iff_toNat_lt, USize.toNat_add, USize.toNat_mul, hw', hq', hn',
    Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]
  nlinarith

/-- Load a ternary tensor coordinate with its bounds proved outside the native read. -/
@[inline] def tensorWord (mixed : FixedDWords (81*1600)) (q : USize) (hq : q.toNat < 81)
    (j : USize) (hj : j.toNat < 1600) : UInt64 :=
  (getUDWord mixed (1600*q+j) (by
    have hn : USize.ofNat 1600 = 1600 := by
      apply USize.toNat_inj.mp
      rw [USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
      exact (USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)).symm
    simpa only [Nat.toUSize, USize.ofNat_toNat, hn] using tensorWordIndex q.toNat hq ⟨1600,by decide⟩ j hj)).toUInt64

/-- The native tensor read equals its checked row-major buffer coordinate. -/
theorem tensorWord_eq (mixed : FixedDWords (81*1600)) (q : USize) (hq : q.toNat < 81)
    (j : USize) (hj : j.toNat < 1600) :
    tensorWord mixed q hq j hj = (readUDWord mixed (1600*q+j)).toUInt64 :=
  congrArg UInt32.toUInt64 (getUDWord_eq_readUDWord mixed _ _)

/-- Accumulate one extension coordinate with proved in-bounds scalar loads and stores. -/
@[inline] def accumulateTensor (q : USize) (hq : q.toNat < 81) (out : FixedWords 243)
    (c : USize) (hc : c.toNat < 3) (value : UInt64) : FixedWords 243 :=
  let i := 3*q+c
  have bound : 3*q+c < (243 : Nat).toUSize := by
    have hn : USize.ofNat 3 = 3 := by
      apply USize.toNat_inj.mp
      rw [USize.toNat_ofNat_of_lt' (lt_of_lt_of_le (by decide) USize.le_size)]
      exact (USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)).symm
    simpa only [Nat.toUSize, USize.ofNat_toNat, hn] using tensorWordIndex q.toNat hq ⟨3,by decide⟩ c hc
  setUWord out i bound (getUWord out i bound ^^^ value)

/-- The native tensor accumulator equals the checked XOR update at the same coordinate. -/
theorem accumulateTensor_eq (q : USize) (hq : q.toNat < 81) (out : FixedWords 243)
    (c : USize) (hc : c.toNat < 3) (value : UInt64) :
    accumulateTensor q hq out c hc value =
      writeUWord out (3*q+c) (readUWord out (3*q+c) ^^^ value) := by
  simp only [accumulateTensor, setUWord_eq_writeUWord]
  rw [getUWord_eq_readUWord]

/-- Accumulate all ternary products of one position using only word products and prepared linear maps. -/
def earlyPosition (maps : FixedWords (1600*6*256*3)) (mixed : FixedDWords (81*1600))
    (products : RmfeProducts) (j1 j2 : USize)
    (hj1 : j1.toNat < 1600) (hj2 : j2.toNat < 1600) (base : USize) (hb : base.toNat ≤ 7372800-4608) (q : USize) (out : FixedWords 243) : FixedWords 243 :=
  if hq : q < 81 then
    have hq' : q.toNat < 81 := by simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 81 < 2^32) USize.le_size)] using hq
    let out := if (ternaryBinary.uget q (by simpa only [ternaryBinary, ByteArray.size, Array.size_ofFn] using hq')) = 1 then out else
      let b := tensorWord mixed q hq' j1 hj1
      let c := tensorWord mixed q hq' j2 hj2
      let p := products.mul b c
      let a0 := evalWeightCoordinate maps base hb 0 (usize_toNat_lt (by decide) (by decide)) p
      let a1 := evalWeightCoordinate maps base hb 1 (usize_toNat_lt (by decide) (by decide)) p
      let a2 := evalWeightCoordinate maps base hb 2 (usize_toNat_lt (by decide) (by decide)) p
      let out := accumulateTensor q hq' out 0 (usize_toNat_lt (by decide) (by decide)) a0
      let out := accumulateTensor q hq' out 1 (usize_toNat_lt (by decide) (by decide)) a1
      accumulateTensor q hq' out 2 (usize_toNat_lt (by decide) (by decide)) a2
    earlyPosition maps mixed products j1 j2 hj1 hj2 base hb (q+1) out
  else out
termination_by 81-q.toNat
decreasing_by
  have _hq' : q.toNat < 81 := by simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 81 < 2^32) USize.le_size)] using hq
  have hn : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_add, hn]
  change 81-((q.toNat+1)%USize.size) < 81-q.toNat
  rw [Nat.mod_eq_of_lt (by have := USize.le_size; omega)]
  omega

/-- The first four pack variables' quadratic tensor through shared position evaluation maps. -/
def earlyValues (w : SlicedWitness) (d : Nat) (claim : Claim)
    (maps : FixedWords (1600*6*256*3)) (products : RmfeProducts) (binary : Array W) : Array W := Id.run do
  let packs := 2^(w.nLog-4)
  let groups := 2^w.nLog/64
  let eq := eqTable (claim.point.extract 4 claim.point.size)
  let mut values := Array.ofFn fun q : Fin 81 =>
    let (b,hi) := ternaryPlan[q.val]!
    if hi = 81 then binary[b]! else lane 0
  for m in [:2] do
    let state := w.layers[12*(m+1)-d]!
    for block in [:packs/16] do
      let mixed := mixedEmbeddings state groups (16*block)
      let mut sums := zeroWords 243
      for hj : j in [:1600] do
        have hj : j < 1600 := hj.upper
        have hb : (4608*j).toUSize.toNat ≤ 7372800-4608 := by
          rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
          omega
        have hs (k : Nat) : (shift j k).toUSize.toNat < 1600 := by
          have bound : shift j k < 1600 := (Gkr.along ⟨j,hj⟩ k).isLt
          rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)]
          exact bound
        sums := earlyPosition maps mixed products (shift j 1).toUSize
          (shift j 2).toUSize (hs 1) (hs 2) (4608*j).toUSize hb 0 sums
      let weight := eq[m*(packs/16)+block]!
      for q in [:81] do
        if ternaryBinary[q]! = 0 then
          let value : W := ⟨⟨readWord sums (3*q)⟩, ⟨readWord sums (3*q+1)⟩, ⟨readWord sums (3*q+2)⟩⟩
          values := values.set! q (WordExt3.add values[q]! (WordExt3.mul weight value))
  return values

/-- Contract the bound ternary coordinates using their quadratic interpolation. -/
def bindEarly (values : Array W) (point : Array W) : Array W := Id.run do
  let mut values := values
  for r in point do
    values := Array.ofFn fun i : Fin (values.size/3) =>
      let a := values[3*i.val]!
      let b := values[3*i.val+1]!
      let c := values[3*i.val+2]!
      a+r*(a+b+c+r*c)
  return values

/-- Current cofactor coefficients from the contracted four-variable tensor. -/
def earlyRound (values entering bound : Array W) : Array W := Id.run do
  let values := bindEarly values bound
  let eq := eqTable (entering.extract (bound.size+1) 4)
  let mut h0 := lane 0
  let mut h1 := lane 0
  let mut h2 := lane 0
  for row in [:eq.size] do
    let mut index := 0
    let mut power := 3
    for bit in [:3-bound.size] do
      index := index+((row/2^bit)%2)*power
      power := power*3
    h0 := h0+eq[row]!*values[index]!
    h1 := h1+eq[row]!*values[index+1]!
    h2 := h2+eq[row]!*values[index+2]!
  return #[h0,h0+h1+h2,h2]

/-- Weighted linear part of chi after shifting its first input onto the third. -/
def packConstants (weights : Array W) (kappa : W) : Array W :=
  Array.ofFn fun j : Fin 1600 => WordExt3.mul kappa
    (WordExt3.add weights[j.val]! weights[shift j.val 2]!)

/-- Three extension coefficients retained only at a row boundary. -/
structure RowCoefficients where
  /-- Constant coefficient. -/
  zero : W
  /-- Linear coefficient. -/
  linear : W
  /-- Quadratic coefficient. -/
  infinity : W

/-- One pack row with unboxed scalar accumulators and no mutable loop tuple. -/
def packRow (table : PackedE) (weights constants : Array W) (row j : Nat)
    (z0 z1 z2 l0 l1 l2 i0 i1 i2 : UInt64) : RowCoefficients :=
  if _h : j < 1600 then
    let b := table.get (3200*row+shift j 1)
    let db := WordExt3.add b (table.get (3200*row+1600+shift j 1))
    let c := table.get (3200*row+shift j 2)
    let dc := WordExt3.add c (table.get (3200*row+1600+shift j 2))
    let q0 := WordExt3.add (WordExt3.mul weights[j]! b) constants[j]!
    let q1 := WordExt3.mul weights[j]! db
    let p0 := WordExt3.mul q0 c
    let p2 := WordExt3.mul q1 dc
    let p1 := WordExt3.add (WordExt3.mul (WordExt3.add q0 q1) (WordExt3.add c dc))
      (WordExt3.add p0 p2)
    packRow table weights constants row (j+1)
      (z0 ^^^ p0.c0.val) (z1 ^^^ p0.c1.val) (z2 ^^^ p0.c2.val)
      (l0 ^^^ p1.c0.val) (l1 ^^^ p1.c1.val) (l2 ^^^ p1.c2.val)
      (i0 ^^^ p2.c0.val) (i1 ^^^ p2.c1.val) (i2 ^^^ p2.c2.val)
  else ⟨⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩, ⟨⟨l0⟩,⟨l1⟩,⟨l2⟩⟩, ⟨⟨i0⟩,⟨i1⟩,⟨i2⟩⟩⟩
termination_by 1600-j

/-- One pack row's constant and leading coefficients, with scalar word accumulators. -/
def packRowEndpoints (table : PackedE) (weights constants : Array W) (row j : Nat)
    (z0 z1 z2 i0 i1 i2 : UInt64) : W × W :=
  if _h : j < 1600 then
    let b := table.get (3200*row+shift j 1)
    let db := WordExt3.add b (table.get (3200*row+1600+shift j 1))
    let c := table.get (3200*row+shift j 2)
    let dc := WordExt3.add c (table.get (3200*row+1600+shift j 2))
    let q0 := WordExt3.add (WordExt3.mul weights[j]! b) constants[j]!
    let q1 := WordExt3.mul weights[j]! db
    let p0 := WordExt3.mul q0 c
    let p2 := WordExt3.mul q1 dc
    packRowEndpoints table weights constants row (j+1)
      (z0 ^^^ p0.c0.val) (z1 ^^^ p0.c1.val) (z2 ^^^ p0.c2.val)
      (i0 ^^^ p2.c0.val) (i1 ^^^ p2.c1.val) (i2 ^^^ p2.c2.val)
  else (⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩, ⟨⟨i0⟩,⟨i1⟩,⟨i2⟩⟩)
termination_by 1600-j

/-- Materialized chi shifts for the tail's two nonlinear inputs. -/
def packShifts (k : Nat) : Array Nat := Array.ofFn fun j : Fin 1600 => shift j.val k

/-- Machine-indexed endpoint accumulation with all packed reads proved in bounds. -/
def packRowEndpointsNative (table : PackedE) (weights constants : Array W) (row : Nat)
    (bound : 3200*row+3200 ≤ table.size) (j : USize)
    (z0 z1 z2 i0 i1 i2 : UInt64) : W × W :=
  if hj : j < 1600 then
    have hj' : j.toNat < 1600 := by
      simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 1600 < 2^32) USize.le_size)] using hj
    let j1 := (packShifts 1).uget j (by simpa only [packShifts,Array.size_ofFn] using hj')
    let j2 := (packShifts 2).uget j (by simpa only [packShifts,Array.size_ofFn] using hj')
    have hs (k : Nat) : ((packShifts k).uget j (by simpa only [packShifts,Array.size_ofFn] using hj')) < 1600 := by
      have h := (Gkr.along ⟨j.toNat,hj'⟩ k).isLt
      change shift j.toNat k < 1600 at h
      simpa only [packShifts,Array.uget,Array.getElem_ofFn] using h
    let b := WordExt3.read table.data ⟨3200*row+j1, by have := hs 1; omega⟩
    let db := WordExt3.add b (WordExt3.read table.data ⟨3200*row+1600+j1, by have := hs 1; omega⟩)
    let c := WordExt3.read table.data ⟨3200*row+j2, by have := hs 2; omega⟩
    let dc := WordExt3.add c (WordExt3.read table.data ⟨3200*row+1600+j2, by have := hs 2; omega⟩)
    let q0 := WordExt3.add (WordExt3.mul weights[j.toNat]! b) constants[j.toNat]!
    let q1 := WordExt3.mul weights[j.toNat]! db
    let p0 := WordExt3.mul q0 c
    let p2 := WordExt3.mul q1 dc
    packRowEndpointsNative table weights constants row bound (j+1)
      (z0 ^^^ p0.c0.val) (z1 ^^^ p0.c1.val) (z2 ^^^ p0.c2.val)
      (i0 ^^^ p2.c0.val) (i1 ^^^ p2.c1.val) (i2 ^^^ p2.c2.val)
  else (⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩, ⟨⟨i0⟩,⟨i1⟩,⟨i2⟩⟩)
termination_by 1600-j.toNat
decreasing_by
  have _hj' : j.toNat < 1600 := by
    simpa only [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide : 1600 < 2^32) USize.le_size)] using hj
  rw [USize.toNat_add,USize.toNat_one]
  change 1600-((j.toNat+1)%USize.size) < 1600-j.toNat
  rw [Nat.mod_eq_of_lt (by have := USize.le_size; omega)]
  omega

/-- Quadratic cofactor of the pack summand, summed over the remaining rows. -/
def packRound (table : PackedE) (weights constants eq : Array W) : Array W := Id.run do
  let mut h0 := lane 0
  let mut h1 := lane 0
  let mut h2 := lane 0
  for row in [:table.size/3200] do
    let cs := packRow table weights constants row 0 0 0 0 0 0 0 0 0 0
    h0 := WordExt3.add h0 (WordExt3.mul eq[row]! cs.zero)
    h1 := WordExt3.add h1 (WordExt3.mul eq[row]! cs.linear)
    h2 := WordExt3.add h2 (WordExt3.mul eq[row]! cs.infinity)
  return #[h0,h1,h2]

/-- Sum only the constant and leading pack coefficients over the equality suffix. -/
def packEndpoints (table : PackedE) (weights constants eq : Array W) : W × W := Id.run do
  let mut zero := lane 0
  let mut infinity := lane 0
  for hr : row in [:table.size/3200] do
    have bound : 3200*row+3200 ≤ table.size := by
      have hr : row < table.size/3200 := hr.upper
      have := Nat.div_mul_le_self table.size 3200
      omega
    let cs := packRowEndpointsNative table weights constants row bound 0 0 0 0 0 0 0
    zero := WordExt3.add zero (WordExt3.mul eq[row]! cs.1)
    infinity := WordExt3.add infinity (WordExt3.mul eq[row]! cs.2)
  return (zero,infinity)

/-- Recover the scaled linear coefficient from the running equality-weighted claim. -/
def packRoundFromClaim (table : PackedE) (weights constants eq : Array W)
    (entering scale value : W) : Array W :=
  if entering = lane 0 then (packRound table weights constants eq).map (scale*·)
  else
    let (zero,infinity) := packEndpoints table weights constants eq
    let c0 := WordExt3.mul scale zero
    let c2 := WordExt3.mul scale infinity
    let c1 := WordExt3.add (WordExt3.mul (WordExt3.add value c0) (WordExt3.invWord entering)) c2
    #[c0,c1,c2]

/-- The transmitted position coefficient indices, in wire order. -/
def positionCoefficient : Fin 3 → Fin 4 := ![0,2,3]

/-- Transmitted position coefficients with unboxed accumulation and no omitted linear term. -/
def positionRows (weights : Array W) (t : Array (Array W)) (kappa : W) (row : Nat)
    (z0 z1 z2 q0 q1 q2 c0 c1 c2 : UInt64) : Array W :=
  if _h : row < weights.size/2 then
    let offset := 2*row
    let w := weights[offset]!
    let dw := WordExt3.add w weights[offset+1]!
    let a := (t[0]!)[offset]!
    let da := WordExt3.add a (t[0]!)[offset+1]!
    let b := (t[1]!)[offset]!
    let db := WordExt3.add b (t[1]!)[offset+1]!
    let c := (t[2]!)[offset]!
    let dc := WordExt3.add c (t[2]!)[offset+1]!
    let h0 := WordExt3.add (WordExt3.mul kappa a) (WordExt3.mul (WordExt3.add kappa b) c)
    let h1 := WordExt3.add (WordExt3.add (WordExt3.mul kappa da)
      (WordExt3.mul (WordExt3.add kappa b) dc)) (WordExt3.mul db c)
    let h2 := WordExt3.mul db dc
    let p0 := WordExt3.mul w h0
    let p2 := WordExt3.add (WordExt3.mul w h2) (WordExt3.mul dw h1)
    let p3 := WordExt3.mul dw h2
    positionRows weights t kappa (row+1)
      (z0 ^^^ p0.c0.val) (z1 ^^^ p0.c1.val) (z2 ^^^ p0.c2.val)
      (q0 ^^^ p2.c0.val) (q1 ^^^ p2.c1.val) (q2 ^^^ p2.c2.val)
      (c0 ^^^ p3.c0.val) (c1 ^^^ p3.c1.val) (c2 ^^^ p3.c2.val)
  else #[⟨⟨z0⟩,⟨z1⟩,⟨z2⟩⟩,⟨⟨q0⟩,⟨q1⟩,⟨q2⟩⟩,⟨⟨c0⟩,⟨c1⟩,⟨c2⟩⟩]
termination_by weights.size/2-row

/-- Position cubic's transmitted coefficients, with zero padding through eleven variables. -/
def positionRound (weights : Array W) (t : Array (Array W)) (kappa : W) : Array W :=
  positionRows weights t kappa 0 0 0 0 0 0 0 0 0 0

/-- Accumulate a prefix of position weights into its 320 theta columns. -/
def transposeColumnLoop (g : Array W) (n : Nat) : Array W := Id.run do
  let mut columns := Array.replicate 320 (0 : W)
  for j in [:n] do
    let c := 64*(j/64%5)+j%64
    columns := columns.set! c (columns[c]!+g[j]!)
  return columns

/-- Sparse transpose of theta, rho and pi on position weights. -/
def transposeWeights (weights : Array W) : Array W :=
  let g := Array.ofFn fun i : Fin 1600 =>
    let l := i.val/64
    let x := l%5
    let y := l/5
    let pi := y+5*((2*x+3*y)%5)
    weights[64*pi+(i.val%64+rotations[l]!)%64]!
  let columns := transposeColumnLoop g 1600
  Array.ofFn fun i : Fin 1600 =>
    let x := i.val/64%5
    let z := i.val%64
    g[i.val]!+columns[64*((x+1)%5)+z]!+columns[64*((x+4)%5)+(z+1)%64]!

/-- Retained authored data for one layer. -/
structure Layer where
  /-- Product polynomial, then its challenge. -/
  product : Array W
  /-- Evaluation challenge. -/
  s : W
  /-- Transmitted pack tails, two scalars per round. -/
  packMessages : Array (Array W)
  /-- Pack and segment challenges. -/
  packPoint : Array W
  /-- Transmitted position messages, three scalars per round. -/
  positionMessages : Array (Array W)
  /-- Eleven position challenges. -/
  positionPoint : Array W
  /-- Three shifted evaluations. -/
  evaluations : Array W
  /-- Batching challenge. -/
  beta : W

/-- Counter boundaries around complete production phases. -/
inductive Phase where
  | total | setup | rmfe | product | pack | position | batch | openings
  | packMaps | packTensor | packCoefficients | packFolds
  deriving BEq, Repr

/-- Stable labels used by the phase benchmark. -/
def Phase.label : Phase → String
  | .total => "total" | .setup => "setup" | .rmfe => "rmfe" | .product => "product"
  | .pack => "pack" | .position => "position" | .batch => "batch" | .openings => "openings"
  | .packMaps => "pack-maps" | .packTensor => "pack-tensor"
  | .packCoefficients => "pack-coefficients" | .packFolds => "pack-folds"

/-- Prove one backwards layer and return its batched input claim. -/
def proveLayerM {M : Type → Type} [Monad M] (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (d : Nat) (claim : Claim)
    (products : RmfeProducts) : M (Layer × Claim × Writer) := do
  mark .product true
  let prod := product w d claim products
  let (s, next) := (writer.writeAll prod.message).sample
  let mut writer := next
  let mut value := evaluate prod.message s
  mark .product false
  mark .rmfe true
  let mu := instanceWeights s
  let kappa := sum mu
  let mut table := PackedE.zeros 0
  mark .rmfe false
  mark .pack true
  let constants := packConstants claim.weights kappa
  mark .packMaps true
  let challenge := CompStark.Sumcheck.prepare s
  let maps := prepareWeightMaps claim.weights challenge
  mark .packMaps false
  mark .packTensor true
  let early := earlyValues w d claim maps products (binaryValues prod.packs claim.point challenge)
  mark .packTensor false

  let mut scale := lane 1
  let mut point := #[]
  let mut packMessages := #[]
  for i in [:claim.point.size] do
    let later := eqTable (claim.point.extract (i+1) claim.point.size)
    mark .packCoefficients true
    let coeffs := if i < 4 then (earlyRound early claim.point point).map (scale*·)
      else packRoundFromClaim table claim.weights constants later claim.point[i]! scale value
    mark .packCoefficients false
    let message := #[coeffs[1]!, coeffs[2]!]
    let (r, next) := (writer.writeAll message).sample
    writer := next
    packMessages := packMessages.push message
    value := (1+claim.point[i]!+r)*(coeffs[0]!+r*(coeffs[1]!+r*coeffs[2]!))
    scale := scale*(1+claim.point[i]!+r)
    point := point.push r
    if i = 3 then
      mark .pack false
      mark .rmfe true
      table := packedTable w d mu point
      mark .rmfe false
      mark .pack true
    else if 4 ≤ i then
      mark .packFolds true
      table := foldPacked table 1600 r
      mark .packFolds false
  mark .pack false
  mark .position true
  let mut t := Array.ofFn fun k : Fin 3 => Array.ofFn fun j : Fin 2048 =>
    if j.val < 1600 then table.get (shift j.val k.val) else lane 0
  let mut weights := claim.weights ++ Array.replicate 448 0
  let mut positionPoint := #[]
  let mut positionMessages := #[]
  for _ in [:11] do
    let message := (positionRound weights t kappa).map (scale*·)
    let (r, next) := (writer.writeAll message).sample
    writer := next
    positionMessages := positionMessages.push message
    positionPoint := positionPoint.push r
    if 1024 ≤ weights.size then
      let map := CompStark.Sumcheck.prepare r
      weights := foldArrayShared weights 1 map
      t := t.map fun a => foldArrayShared a 1 map
    else
      weights := fold weights 1 r
      t := t.map fun a => fold a 1 r
  let evaluations := t.map (·[0]!)
  let (beta, next) := (writer.writeAll evaluations).sample
  mark .position false
  mark .batch true
  let eq := eqTable positionPoint
  let beta2 := beta*beta
  let chi := Array.ofFn fun j : Fin 1600 =>
    eq[j.val]!+beta*eq[shift j.val 4]!+beta2*eq[shift j.val 3]!
  let nextClaim := Claim.mk
    (evaluations[0]!+beta*(evaluations[1]!+beta*evaluations[2]!)) mu point (transposeWeights chi)
  mark .batch false
  return (⟨prod.message, s, packMessages, point, positionMessages, positionPoint, evaluations, beta⟩, nextClaim, next)

/-- Retained factors, messages and running claim after a quadratic sumcheck. -/
structure QuadraticResult where
  /-- First factor at the terminal point. -/
  a : Array W
  /-- Second factor at the terminal point. -/
  b : Array W
  /-- Bound coordinates. -/
  point : Array W
  /-- Transmitted constant and quadratic coefficients. -/
  messages : Array (Array W)
  /-- Final reconstructed running claim. -/
  value : W
  /-- Transcript state after the final challenge. -/
  writer : Writer

/-- A quadratic sumcheck over paired rows of dot-product factors. -/
def proveQuadratics (writer : Writer) (a b : Array W) (width : Nat) (scale value : W)
    (rounds : Nat) : QuadraticResult := Id.run do
  let mut a := a
  let mut b := b
  let mut value := value
  let mut writer := writer
  let mut point := #[]
  let mut messages := #[]
  for _ in [:rounds] do
    let mut zero : W := 0
    let mut infinity : W := 0
    for i in [:a.size/(2*width)] do
      for j in [:width] do
        let offset := 2*i*width+j
        zero := zero+a[offset]!*b[offset]!
        infinity := infinity+(a[offset]!+a[offset+width]!)*(b[offset]!+b[offset+width]!)
    zero := scale*zero
    infinity := scale*infinity
    let (r, next) := (writer.writeAll #[zero, infinity]).sample
    writer := next
    messages := messages.push #[zero, infinity]
    point := point.push r
    value := zero+r*(value+infinity+r*infinity)
    if 1024 ≤ a.size/(2*width)*width then
      let map := CompStark.Sumcheck.prepare r
      a := foldArrayShared a width map
      b := foldArrayShared b width map
    else
      a := fold a width r
      b := fold b width r
  return ⟨a, b, point, messages, value, writer⟩

/-- All terminal opening data, including the claims consumed by the PCS. -/
structure Openings where
  /-- Six compressed word-opening messages. -/
  outputMessages : Array (Array W)
  /-- Six word slot coordinates. -/
  outputPoint : Array W
  /-- Terminal word evaluation. -/
  outputValue : W
  /-- Ten compressed bit-opening messages. -/
  inputMessages : Array (Array W)
  /-- Four low coordinates, then six slot coordinates. -/
  inputPoint : Array W
  /-- All 64 terminal bit-slice evaluations. -/
  slices : Array W

/-- Fold all committed words at the external instance point, retaining spare slots. -/
def outputWords (committed : Array UInt64) (n : Nat) (point : Array W) : Array W :=
  let eq := eqTable point
  Array.ofFn fun slot : Fin (committed.size/n) => Id.run do
    let mut a : W := 0
    for b in [:n] do a := a+WordExt3.mulScalar eq[b]! ⟨committed[slot.val*n+b]!⟩
    return a

/-- Exact slot-and-slice weights on the fifty committed segment-input lanes. -/
def inputWeights (claim : Claim) : Array W :=
  Array.ofFn fun i : Fin 4096 =>
    let slot := i.val/64
    if slot < 50 then
      (if slot < 25 then 1+claim.point.back! else claim.point.back!) * claim.weights[64*(slot%25)+i.val%64]!
    else 0

/-- Transpose an eight-by-eight Boolean matrix packed in one word. -/
@[inline] def transposeByte (x : UInt64) : UInt64 :=
  let t := (x ^^^ (x >>> 7)) &&& 0x00AA00AA00AA00AA
  let x := x ^^^ t ^^^ (t <<< 7)
  let t := (x ^^^ (x >>> 14)) &&& 0x0000CCCC0000CCCC
  let x := x ^^^ t ^^^ (t <<< 14)
  let t := (x ^^^ (x >>> 28)) &&& 0x00000000F0F0F0F0
  x ^^^ t ^^^ (t <<< 28)

/-- Gather eight lane bytes before transposing their simultaneous bit columns. -/
@[inline] def bitColumns (a b c d e f g h shift : UInt64) : UInt64 :=
  transposeByte (((a >>> shift) &&& (255 : UInt64)) ||| (((b >>> shift) &&& (255 : UInt64)) <<< 8) |||
    (((c >>> shift) &&& (255 : UInt64)) <<< 16) ||| (((d >>> shift) &&& (255 : UInt64)) <<< 24) |||
    (((e >>> shift) &&& (255 : UInt64)) <<< 32) ||| (((f >>> shift) &&& (255 : UInt64)) <<< 40) |||
    (((g >>> shift) &&& (255 : UInt64)) <<< 48) ||| (((h >>> shift) &&& (255 : UInt64)) <<< 56))

/-- Fold committed bits by byte selection maps, retaining sixteen separate instance coordinates. -/
def inputBits (committed : Array UInt64) (n : Nat) (point : Array W) : Array W := Id.run do
  let eq := eqTable point
  let maps := Array.ofFn fun group : Fin (n/128) =>
    subsets (eq.extract (8*group.val) (8*group.val+8))
  let mut out := PackedE.zeros 65536
  for slot in [:64] do
    for i in [:16] do
      let offset := (i+16*slot)*64
      for group in [:n/128] do
        let offsetWord := slot*n+128*group+i
        let a := committed[offsetWord]!
        let b := committed[offsetWord+16]!
        let c := committed[offsetWord+32]!
        let d := committed[offsetWord+48]!
        let e := committed[offsetWord+64]!
        let f := committed[offsetWord+80]!
        let g := committed[offsetWord+96]!
        let h := committed[offsetWord+112]!
        let map := maps[group]!
        for byte in [:8] do
          let columns := bitColumns a b c d e f g h (8*byte).toUInt64
          for bit in [:8] do
            let j := offset+8*byte+bit
            let value := map[((columns >>> (8*bit).toUInt64) &&& 255).toNat]!
            out := out.set j (WordExt3.add (out.get j) value)
  return out.toArray

/-- Reduce the final layer and middle-state claims to the complete commitment openings. -/
def proveOpenings (writer : Writer) (committed : Array UInt64) (n : Nat)
    (words wordWeights : Array W) (middle : W) (claim : Claim) : Openings × Writer := Id.run do
  let word := proveQuadratics writer words wordWeights 1 1 middle 6
  let writer := word.writer.write word.a[0]!
  let weights := inputWeights claim
  let folded := inputBits committed n (claim.point.extract 0 (claim.point.size-1))
  let perInstance := Array.ofFn fun i : Fin 16 => Id.run do
    let mut a : W := 0
    for slot in [:64] do
      for z in [:64] do a := a+folded[(i.val+16*slot)*64+z]!*weights[slot*64+z]!
    return a
  let low := proveQuadratics writer perInstance claim.mu 1 1 claim.value 4
  let eq := eqTable low.point
  let atInstance := Array.ofFn fun offset : Fin 4096 => Id.run do
    let slot := offset.val/64
    let z := offset.val%64
    let mut a : W := 0
    for i in [:16] do a := a+eq[i]!*folded[(i+16*slot)*64+z]!
    return a
  let slot := proveQuadratics low.writer atInstance weights 64 low.b[0]! low.value 6
  return (⟨word.messages, word.point, word.a[0]!, low.messages++slot.messages, low.point++slot.point, slot.a⟩,
    slot.writer.writeAll slot.a)

/-- Full reduction result, retaining the witness, authored messages and final claim. -/
structure Reduction where
  /-- Initial instance point, supplied by the enclosing protocol. -/
  batchPoint : Array W
  /-- Segment and lane batching coordinates. -/
  segment : W
  /-- Five lane coordinates. -/
  lanes : Array W
  /-- Weighted middle-state claim transmitted before the layers. -/
  middle : W
  /-- Twelve layer transcripts. -/
  layers : Array Layer
  /-- Input claim after all twelve layers. -/
  finalClaim : Claim
  /-- Terminal commitment reductions. -/
  openings : Openings
  /-- Final transport and challenge trace. -/
  writer : Writer

/-- Honest two-segment GKR reduction of a fixed committed block and output claim. -/
def proveM {M : Type → Type} [Monad M] (mark : Phase → Bool → M Unit) (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : M Reduction := do
  mark .setup true
  let (segmentPoint, writer) := writer.sampleMany 1
  let segment := segmentPoint[0]!
  let (lanes, writer) := writer.sampleMany 5
  let laneEq := eqTable lanes
  let words := outputWords committed (2^w.nLog) batchPoint
  let wordWeights := Array.ofFn fun slot : Fin 64 =>
    if 25 ≤ slot.val && slot.val < 50 then (1+segment)*laneEq[slot.val-25]! else 0
  let middle := dot words wordWeights
  let writer := writer.write middle
  let mut claim := Claim.mk
    (middle+segment*dot (laneEq.extract 0 25) output)
    (eqTable (batchPoint.extract 0 4)) ((batchPoint.extract 4 batchPoint.size).push segment)
    (Array.ofFn fun j : Fin 1600 => WordExt3.mulScalar laneEq[j.val/64]! ⟨1 <<< (j.val%64).toUInt64⟩)
  let mut writer := writer
  let mut layers := #[]
  mark .setup false
  mark .rmfe true
  let products := prepareRmfeProducts
  mark .rmfe false
  for d in [:12] do
    let (layer, nextClaim, next) ← proveLayerM mark writer w d claim products
    layers := layers.push layer
    claim := nextClaim
    writer := next
  mark .openings true
  let (openings, finalWriter) := proveOpenings writer committed (2^w.nLog) words wordWeights middle claim
  mark .openings false
  return ⟨batchPoint, segment, lanes, middle, layers, claim, openings, finalWriter⟩

/-- Pure production reduction, sharing its complete implementation with the phase observer. -/
def prove (writer : Writer) (w : SlicedWitness) (committed : Array UInt64)
    (batchPoint output : Array W) : Reduction :=
  Id.run (proveM (fun _ _ => pure ()) writer w committed batchPoint output)

end CompStark.Keccak.GkrProver
