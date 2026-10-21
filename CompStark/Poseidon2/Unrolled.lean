/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! # Generated Poseidon2 round kernels

The packed rounds are straight-line code over `L` independent states, one per vector lane, so the
C compiler turns each lane-wise operation into vector instructions. State coordinate `j` of lane
`l` is word `i + j * L + l` of the buffer `b`. The generators expand to the `let`s of a kernel,
referring to the binders of the definition they are used in by name: `b`, `i`, the constant
tables and the bounds hypothesis `h`.
-/

namespace CompStark.Poseidon2.Unrolled
open Lean

meta def name (s : String) : Ident := mkIdent (Name.mkSimple s)

meta def lit (k : Nat) : Term := Syntax.mkNumLit (toString k)

/-- Word `k` after word `idx` of `arr`, with its bound `inBounds hb k _` from the hypothesis
`hb` that words `idx, …, idx + n` fit. -/
meta def read (arr idx hb : Term) (k : Nat) : MacroM Term :=
  `($(name "readUOffset") $arr $idx $(lit k)
    ($(name "inBounds") $hb $(lit k) (by simp only [USize.reduceToNat]; decide)))

/-- The modulus of the word arithmetic, KoalaBear's. -/
meta def modulus : Ident := mkIdent `KoalaBear.fieldSize

meta def add (x y : Term) : MacroM Term := `($(name "add") $modulus $x $y)

meta def mul (x y : Term) : MacroM Term := `($(name "mul") $modulus $x $y)

meta def sub (x y : Term) : MacroM Term := `($(name "sub") $modulus $x $y)

meta def halve (x : Term) : MacroM Term := `($(name "halve") $x)

/-- `let x := v` for each binding, then `body`. -/
meta def lets (bs : Array (Ident × Term)) (body : Term) : MacroM Term :=
  bs.foldrM (fun (x, v) b ↦ `(let $x:ident := $v; $b)) body

meta def v (s : String) (j l : Nat) : Ident := name s!"{s}{j}_{l}"

/-- The bindings of every lane, operation-major: the same operation of all lanes is adjacent,
which is the shape the vectorizer packs. -/
meta def interleave (L : Nat) (lane : Nat → MacroM (Array (Ident × Term))) :
    MacroM (Array (Ident × Term)) := do
  let seqs ← (Array.range L).mapM lane
  let mut bs := #[]
  for k in [0:seqs[0]!.size] do
    for l in [0:L] do
      bs := bs.push seqs[l]![k]!
  return bs

/-- Read the `t × L` state. -/
meta def readState (t L : Nat) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  for j in [0:t] do
    for l in [0:L] do
      bs := bs.push (v "x" j l, ← read (name "b") (name "i") (name "hb") (j * L + l))
  return bs

/-- `y ^ 3` as two products, the square left unreduced. -/
meta def cube (out a : Ident) : MacroM (Array (Ident × Term)) := do
  let sq := name s!"{out.getId}_sq"
  return #[(sq, ← `($(name "mulLazy") $a $a)), (out, ← `($(name "mulSign") $sq $a))]

/-- Store the `t × L` state `z`, one unchecked eight-word store per coordinate: the state stays
a `ByteArray` of the size of `b`, so the bounds come from `hb` and no store branches. -/
meta def store (t L : Nat) (z : String) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[(name "st",
    ← `((⟨$(name "b"), rfl⟩ : { x : ByteArray // x.size = $(name "b").size })))]
  for j in [0:t] do
    let vs := (Array.range L).map fun l ↦ (v z j l : Term)
    bs := bs.push (name "st", ← `($(name "store8") $(name "st") $(name "i") $(lit (j * L)) $vs*
      ($(name s!"storeBounds{t}") $(name "hb") $(lit (j * L))
        (by simp only [USize.reduceToNat]; decide))))
  return bs

/-- `mat4` on every block of four coordinates of lane `l`, with Plonky3's addition chain except
row 2 as `(t0123 + x2) + 2 x3`: with Plonky3's `t01233 + t23`, clang's SLP vectorizer splices lanes
across vectors and the kernel grows by a third. -/
meta def mat4Lane (t l : Nat) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  for blk in [0:t / 4] do
    let x (k : Nat) : Term := v "x" (4 * blk + k) l
    let m (s : String) : Ident := name s!"m{blk}_{l}_{s}"
    bs := bs.push (m "t01", ← add (x 0) (x 1))
    bs := bs.push (m "t23", ← add (x 2) (x 3))
    bs := bs.push (m "t0123", ← add (m "t01") (m "t23"))
    bs := bs.push (m "t01123", ← add (m "t0123") (x 1))
    bs := bs.push (m "t01233", ← add (m "t0123") (x 3))
    bs := bs.push (m "x0x0", ← add (x 0) (x 0))
    bs := bs.push (m "x2x2", ← add (x 2) (x 2))
    bs := bs.push (v "z" (4 * blk) l, ← add (m "t01123") (m "t01"))
    bs := bs.push (v "z" (4 * blk + 1) l, ← add (m "t01123") (m "x2x2"))
    bs := bs.push (m "t01232", ← add (m "t0123") (x 2))
    bs := bs.push (m "x3x3", ← add (x 3) (x 3))
    bs := bs.push (v "z" (4 * blk + 2) l, ← add (m "t01232") (m "x3x3"))
    bs := bs.push (v "z" (4 * blk + 3) l, ← add (m "t01233") (m "x0x0"))
  return bs

/-- `mat4` on every block of four, in place. -/
meta def mat4Blocks (t L : Nat) : MacroM Term := do
  let bs := (← readState t L) ++ (← interleave L (mat4Lane t)) ++ (← store t L "z")
  lets bs (← `($(name "st").1))

/-- Add to every coordinate the sum over all blocks of its row, in place. -/
meta def mixBlocks (t L : Nat) : MacroM Term := do
  let bs := (← readState t L) ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    for k in [0:4] do
      let mut acc : Term := v "x" k l
      for blk in [1:t / 4] do
        let s := name s!"S{k}_{l}_{blk}"
        bs := bs.push (s, ← add acc (v "x" (4 * blk + k) l))
        acc := s
      bs := bs.push (name s!"S{k}_{l}", acc)
    for j in [0:t] do
      bs := bs.push (v "z" j l, ← add (v "x" j l) (name s!"S{j % 4}_{l}"))
    return bs) ++ (← store t L "z")
  lets bs (← `($(name "st").1))

/-- The constant additions and S-boxes of a full round, in place. -/
meta def sbox (t L : Nat) : MacroM Term := do
  let mut bs := #[]
  for j in [0:t] do
    bs := bs.push (name s!"c{j}", ← read (name "rc") (name "r") (name "hr") j)
  bs := bs ++ (← readState t L)
  bs := bs ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    for j in [0:t] do
      bs := bs.push (v "a" j l, ← add (v "x" j l) (name s!"c{j}"))
      bs := bs ++ (← cube (v "y" j l) (v "a" j l))
    return bs)
  bs := bs ++ (← store t L "y")
  lets bs (← `($(name "st").1))

/-- `V_j · x + sum` for the width-`t` diagonal `V` of KoalaBear's Poseidon2, which starts
`[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4]` and continues with `±1/2^k`: small multiples and halves as
additions, subtractions and halving, `±1/2^k` with `mulInvPow2`. -/
meta def diagonal (t j : Nat) (z : Ident) (x acc : Term) : MacroM (Array (Ident × Term)) := do
  let tmp (s : String) : Ident := name s!"{z.getId}_{s}"
  match j with
  | 0 => return #[(tmp "2", ← add x x), (z, ← sub acc (tmp "2"))]
  | 1 => return #[(z, ← add acc x)]
  | 2 => return #[(tmp "2", ← add x x), (z, ← add acc (tmp "2"))]
  | 3 => return #[(tmp "h", ← halve x), (z, ← add acc (tmp "h"))]
  | 4 => return #[(tmp "2", ← add x x), (tmp "3", ← add (tmp "2") x), (z, ← add acc (tmp "3"))]
  | 5 =>
    return #[(tmp "2", ← add x x), (tmp "4", ← add (tmp "2") (tmp "2")),
      (z, ← add acc (tmp "4"))]
  | 6 => return #[(tmp "h", ← halve x), (z, ← sub acc (tmp "h"))]
  | 7 => return #[(tmp "2", ← add x x), (tmp "3", ← add (tmp "2") x), (z, ← sub acc (tmp "3"))]
  | 8 =>
    return #[(tmp "2", ← add x x), (tmp "4", ← add (tmp "2") (tmp "2")),
      (z, ← sub acc (tmp "4"))]
  | _ =>
    -- `±2 ^ (-k)`: the exponent `k`, negative entries marked by `true`.
    let pow2 : List (Nat × Bool) := if t == 16 then
        [(8, false), (3, false), (24, false), (8, true), (3, true), (4, true), (24, true)]
      else [(8, false), (2, false), (3, false), (4, false), (5, false), (6, false), (24, false),
        (8, true), (3, true), (4, true), (5, true), (6, true), (7, true), (9, true), (24, true)]
    match pow2[j - 9]? with
    | some (k, neg) =>
      let s ← `($(name "mulInvPow2") $(lit k) $x)
      return #[(tmp "s", s), (z, ← (if neg then sub else add) acc (tmp "s"))]
    | none => return #[(z, ← add (← mul (name s!"d{j}") x) acc)]

/-- The sum of `xs` as a tree of additions, adding neighbours level by level, and its root: the
sum of a partial round runs beside its S-box instead of after it. -/
meta partial def treeSum (pre : String) (xs : Array Term) (level : Nat := 0) :
    MacroM (Array (Ident × Term) × Term) := do
  if xs.size ≤ 1 then return (#[], xs[0]!)
  let mut bs := #[]
  let mut ys := #[]
  for k in [0:xs.size / 2] do
    let n := name s!"{pre}_{level}_{k}"
    bs := bs.push (n, ← add xs[2 * k]! xs[2 * k + 1]!)
    ys := ys.push (n : Term)
  if xs.size % 2 == 1 then ys := ys.push xs[xs.size - 1]!
  let (bs', r) ← treeSum pre ys (level + 1)
  return (bs ++ bs', r)

/-- A partial round with constant `c` and the internal diagonal `d`. -/
meta def partialRound (t L : Nat) : MacroM Term := do
  let mut bs := #[]
  for j in [0:t] do
    bs := bs.push (name s!"d{j}", ← read (name "d") (lit 0) (name "hd") j)
  bs := bs ++ (← readState t L)
  bs := bs ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    bs := bs.push (v "a" 0 l, ← add (v "x" 0 l) (name "c"))
    bs := bs ++ (← cube (v "y" 0 l) (v "a" 0 l))
    let (sum, rest) ← treeSum s!"r{l}" ((Array.range (t - 1)).map fun j ↦ (v "x" (j + 1) l : Term))
    bs := bs ++ sum
    bs := bs.push (name s!"s_{l}", ← add (v "y" 0 l) rest)
    let acc : Term := name s!"s_{l}"
    let ys : Array Term :=
      #[v "y" 0 l] ++ (Array.range (t - 1)).map fun j ↦ (v "x" (j + 1) l : Term)
    for j in [0:t] do
      bs := bs ++ (← diagonal t j (v "z" j l) ys[j]! acc)
    return bs)
  bs := bs ++ (← store t L "z")
  lets bs (← `($(name "st").1))

/-- Coordinates `0, …, 15` of the eight lanes of a width-`t` group from eight source lines of
sixteen words: word `j` of line `q{l}` of `m` becomes coordinate `j` of lane `l`. -/
meta def load16 (t : Nat) : MacroM Term := do
  let mut bs := #[]
  for j in [0:16] do
    for l in [0:8] do
      bs := bs.push (v "x" j l, ← read (name "m") (name s!"q{l}") (name s!"h{l}") j)
  bs := bs ++ (← store t 8 "x").extract 0 17
  lets bs (← `($(name "st").1))

/-- Coordinates `0, …, 7` of the eight lanes of the group at `i` of `st`, stored as eight
contiguous digests: lane `l` at word `p{l}` of `out`. -/
meta def store8x8 : MacroM Term := do
  let mut bs := #[]
  for j in [0:8] do
    for l in [0:8] do
      bs := bs.push (v "x" j l, ← read (name "st") (name "i") (name "hb") (8 * j + l))
  bs := bs.push (name "o",
    ← `((⟨$(name "out"), rfl⟩ : { x : ByteArray // x.size = $(name "out").size })))
  for l in [0:8] do
    let vs := (Array.range 8).map fun j ↦ (v "x" j l : Term)
    bs := bs.push (name "o", ← `($(name "store8") $(name "o") $(name s!"p{l}") 0 $vs*
      ($(name "storeAt") $(name s!"g{l}"))))
  lets bs (← `($(name "o").1))

end CompStark.Poseidon2.Unrolled

open CompStark.Poseidon2.Unrolled in
/-- The body of a partial round on `L` packed states of width `t`. -/
macro "p2_partial%" t:num L:num : term => partialRound t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of the constant additions and S-boxes of a full round. -/
macro "p2_sbox%" t:num L:num : term => sbox t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of `mat4` on every block of four. -/
macro "p2_mat4%" t:num L:num : term => mat4Blocks t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of the block-sum mixing of the external matrix. -/
macro "p2_mix%" t:num L:num : term => mixBlocks t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a transposing load of eight lines into a width-`t` group. -/
macro "p2_load16%" t:num : term => load16 t.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a transposing store of eight digests from a group. -/
macro "p2_store8x8%" : term => store8x8
