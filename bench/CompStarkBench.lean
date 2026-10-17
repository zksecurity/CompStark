import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.Packed
import CompStark.Merkle.Packed
import CompStark.Merkle.Tree

/-! # CompStark micro-benchmarks

`CompStarkBench poseidon2-spec LOG_N`: the width-16 specification on the Montgomery field, on
`2 ^ LOG_N` chained states; prints the median nanoseconds per permutation of seven runs.
-/

open CompStark.Poseidon2

def timeNs (f : Unit → IO UInt64) : IO (Nat × UInt64) := do
  let t0 ← IO.monoNanosNow
  let r ← f ()
  let t1 ← IO.monoNanosNow
  return (t1 - t0, r)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["poseidon2-spec", logN] =>
    let n := 2 ^ logN.toNat!
    let P := KoalaBear.width16 KoalaBear.Fast.Field
    let s0 : Vector KoalaBear.Fast.Field 16 :=
      Vector.ofFn fun i ↦ KoalaBear.Fast.ofUInt32 i.val.toUInt32
    let mut samples := #[]
    for _ in [0:7] do
      let (ns, r) ← timeNs fun _ ↦ do
        let mut s := s0
        for _ in [0:n] do
          s := permute P s
        return s[0].val.toUInt64
      samples := samples.push (ns / n)
      if r == 12345 then IO.println "" -- keep the result live
    IO.println s!"poseidon2-spec width16 ns/perm median {(samples.qsort (· < ·))[3]!}"
    return 0
  | ["poseidon2-packed", logN] =>
    let n := 2 ^ logN.toNat!
    let groups := n / 8
    let P := KoalaBear.width16 KoalaBear.Fast.Field
    let K := Packed.Packed16.ofParams P
    -- State `l` of group `g` starts as `(g * 8 + l) * 16 + j` in coordinate `j`.
    let init : Array KoalaBear.Fast.Field := Array.ofFn (n := 128 * groups) fun k ↦
      let g := k.val / 128; let j := k.val % 128 / 8; let l := k.val % 8
      KoalaBear.Fast.ofUInt32 ((g * 8 + l) * 16 + j).toUInt32
    let buf := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields init
    let run (b : ByteArray) : ByteArray := Id.run do
      let mut b := b
      for g in [0:groups] do
        b := Packed.permute16 K b (128 * g).toUSize
      return b
    -- Check every lane of the first group against the specification.
    let out := run buf
    for l in [0:8] do
      let s : Vector KoalaBear.Fast.Field 16 := Vector.ofFn fun j ↦ init.getD (j.val * 8 + l) 0
      let e := permute P s
      for j in [0:16] do
        let w := CompPoly.CPolynomial.NTTFast.Packed.Native.read out (8 * j + l)
        if w != (e.toArray.getD j 0).val then
          IO.eprintln s!"mismatch lane {l} coordinate {j}"; return 1
    let mut samples := #[]
    for k in [0:7] do
      let input := CompPoly.CPolynomial.NTTFast.Packed.Native.write buf 0 k.toUInt32
      let (ns, r) ← timeNs fun _ ↦ do
        let b := run input
        return (CompPoly.CPolynomial.NTTFast.Packed.Native.read b 0).toUInt64
      samples := samples.push (ns * 10 / n)
      if r == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[3]!
    IO.println s!"poseidon2-packed width16 ns/perm median {m / 10}.{m % 10}"
    return 0
  | ["merkle", logH, widthArg, chunksArg] =>
    let h := 2 ^ logH.toNat!
    let w := widthArg.toNat!
    let C := chunksArg.toNat!
    let K24 := Packed.Packed24.ofParams (KoalaBear.width24 KoalaBear.Fast.Field)
    let K16 := Packed.Packed16.ofParams (KoalaBear.width16 KoalaBear.Fast.Field)
    let enc := CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields
    let entry (k : Nat) : KoalaBear.Fast.Field := KoalaBear.Fast.ofUInt32 ((7 * k + 1) % 2130706433).toUInt32
    -- Check small shapes against the specification: odd heights, single rows, partial blocks.
    for (sh, sw) in [(1, 1), (2, 3), (5, 16), (8, 17), (13, 40), (64, 10), (33, 7)] do
      let vals := Array.ofFn (n := sh * sw) fun k ↦ entry k.val
      let spec := CompStark.Merkle.KoalaBear.root KoalaBear.Fast.Field [⟨sw, sh, vals⟩]
      let got := CompStark.Merkle.Packed.root K24 K16 sw #[enc vals]
      for j in [0:8] do
        if CompPoly.CPolynomial.NTTFast.Packed.Native.read got j != (spec.toArray.getD j 0).val then
          IO.eprintln s!"merkle mismatch at {sh} × {sw}, word {j}"; return 1
    let rowsPer := h / C
    let chunks := (Array.range C).map fun c ↦
      enc (Array.ofFn (n := rowsPer * w) fun k ↦ entry (c * rowsPer * w + k.val))
    let rootWords := CompStark.Merkle.Packed.root K24 K16 w chunks
    let canon := (List.range 8).map fun j ↦
      (KoalaBear.Fast.ringEquiv (CompPoly.CPolynomial.NTTFast.Packed.ofWord (CompPoly.CPolynomial.NTTFast.Packed.Native.read rootWords j))).val
    IO.println s!"root {canon}"
    let mut samples := #[]
    for k in [0:7] do
      let input := chunks.modify 0 fun c ↦ CompPoly.CPolynomial.NTTFast.Packed.Native.write c 0 k.toUInt32
      let (ns, r) ← timeNs fun _ ↦ do
        return (CompPoly.CPolynomial.NTTFast.Packed.Native.read (CompStark.Merkle.Packed.root K24 K16 w input) 0).toUInt64
      samples := samples.push ns
      if r == 12345 then IO.println ""
    let m := (samples.qsort (· < ·))[3]!
    IO.println s!"merkle 2^{logH} x {w} ms median {m / 1000000}.{m / 1000 % 1000}"
    return 0
  | _ => IO.eprintln "usage: CompStarkBench poseidon2-spec LOG_N"; return 1
