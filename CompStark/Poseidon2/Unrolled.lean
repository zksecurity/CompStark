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

/-- The identifier `s.f`. -/
meta def dotted (s f : String) : Ident := mkIdent (Name.mkStr (Name.mkSimple s) f)

meta def lit (k : Nat) : Term := Syntax.mkNumLit (toString k)

/-- Word `k` after word `idx` of `arr`, with its bound `inBounds hb k _` from the hypothesis
`hb` that words `idx, …, idx + n` fit. -/
meta def read (arr idx hb : Term) (k : Nat) : MacroM Term :=
  `($(name "readUOffset") $arr $idx $(lit k)
    ($(name "inBounds") $hb $(lit k) (by simp only [USize.reduceToNat]; decide)))

/-- What the kernels of a field depend on: its modulus `p = odd · 2 ^ twoAdicity + 1`, the S-box
degree, and the tails of the internal diagonals of widths 16 and 24, whose first nine entries
`[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4]` every field shares: entry `9 + m` is `±2 ^ (-k)` for the
`m`-th pair `(k, negative)`. -/
meta structure Shape where
  modulus : Name
  degree : Nat
  odd : Nat
  twoAdicity : Nat
  tail16 : List (Nat × Bool)
  tail24 : List (Nat × Bool)

/-- The shapes of the fields with packed kernels. -/
meta def shapeOf : Name → MacroM Shape
  | `koalabear => return {
      modulus := `_root_.KoalaBear.fieldSize, degree := 3, odd := 127, twoAdicity := 24
      tail16 := [(8, false), (3, false), (24, false), (8, true), (3, true), (4, true), (24, true)]
      tail24 := [(8, false), (2, false), (3, false), (4, false), (5, false), (6, false),
        (24, false), (8, true), (3, true), (4, true), (5, true), (6, true), (7, true), (9, true),
        (24, true)] }
  | `babybear => return {
      modulus := `_root_.BabyBear.fieldSize, degree := 7, odd := 15, twoAdicity := 27
      tail16 := [(8, false), (2, false), (3, false), (27, false), (8, true), (4, true), (27, true)]
      tail24 := [(8, false), (2, false), (3, false), (4, false), (7, false), (9, false),
        (27, false), (8, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true),
        (27, true)] }
  | f => Macro.throwError s!"no Poseidon2 kernel shape for {f}"

/-- The modulus of the word arithmetic. -/
meta def Shape.p (S : Shape) : Ident := mkIdent S.modulus

meta def add (S : Shape) (x y : Term) : MacroM Term := `($(name "add") $(S.p) $x $y)

meta def sub (S : Shape) (x y : Term) : MacroM Term := `($(name "sub") $(S.p) $x $y)

meta def halve (S : Shape) (x : Term) : MacroM Term := `($(name "halve") $(S.p) $x)

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

/-- Write words `i, …, i + 7` of `b` back unchanged, as `s0` (`touch8`), first: the stores after
it then need no exclusivity checks, so the compiler interleaves the loads with them instead of
holding every loaded word until the first store. -/
meta def touch : MacroM (Array (Ident × Term)) := do
  return #[(name "s0", ← `($(name "touch8") $(name "b") $(name "i")
    ($(dotted "Fits" "mono") $(name "hb") (by decide))))]

/-- Read the `t × L` state from the touched buffer `s0`. -/
meta def readState (t L : Nat) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  for j in [0:t] do
    for l in [0:L] do
      bs := bs.push (v "x" j l, ← read (← `($(name "s0").1)) (name "i")
        (← `($(dotted "Fits" "of_size") $(name "s0").2 $(name "hb"))) (j * L + l))
  return bs

/-- The S-box `a ^ d`, canonical. -/
meta def sboxSign (S : Shape) (a : Term) : MacroM Term :=
  if S.degree == 3 then `($(name "cubeSign") $(S.p) $a) else `($(name "pow7Sign") $(S.p) $a)

/-- The S-box `a ^ d`, its last product left below `2 p`. -/
meta def sboxLazy (S : Shape) (a : Term) : MacroM Term :=
  if S.degree == 3 then `($(name "cubeLazy") $(S.p) $a) else `($(name "pow7Lazy") $(S.p) $a)

/-- Store the `t × L` state `z` into the touched buffer `s0`, one unchecked eight-word store per
coordinate: the state stays a `ByteArray` of the size of `b`, so the bounds come from `hb` and no
store branches. -/
meta def store (t L : Nat) (z : String) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[(name "st", (name "s0" : Term))]
  for j in [0:t] do
    let vs := (Array.range L).map fun l ↦ (v z j l : Term)
    bs := bs.push (name "st", ← `($(name "store8") $(name "st") $(name "i") $(lit (j * L)) $vs*
      ($(name s!"storeBounds{t}") $(name "hb") $(lit (j * L))
        (by simp only [USize.reduceToNat]; decide))))
  return bs

/-- `mat4` on every block of four coordinates of lane `l`, its words reduced below `p` first, with
Plonky3's addition chain except row 2 as `(t0123 + x2) + 2 x3`: with Plonky3's `t01233 + t23`,
clang's SLP vectorizer splices lanes across vectors and the kernel grows by a third. -/
meta def mat4Lane (S : Shape) (t l : Nat) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  for j in [0:t] do
    bs := bs.push (v "r" j l, ← `($(name "reduceOnce") $(S.p) $(v "x" j l)))
  for blk in [0:t / 4] do
    let x (k : Nat) : Term := v "r" (4 * blk + k) l
    let m (s : String) : Ident := name s!"m{blk}_{l}_{s}"
    bs := bs.push (m "t01", ← add S (x 0) (x 1))
    bs := bs.push (m "t23", ← add S (x 2) (x 3))
    bs := bs.push (m "t0123", ← add S (m "t01") (m "t23"))
    bs := bs.push (m "t01123", ← add S (m "t0123") (x 1))
    bs := bs.push (m "t01233", ← add S (m "t0123") (x 3))
    bs := bs.push (m "x0x0", ← add S (x 0) (x 0))
    bs := bs.push (m "x2x2", ← add S (x 2) (x 2))
    bs := bs.push (v "z" (4 * blk) l, ← add S (m "t01123") (m "t01"))
    bs := bs.push (v "z" (4 * blk + 1) l, ← add S (m "t01123") (m "x2x2"))
    bs := bs.push (m "t01232", ← add S (m "t0123") (x 2))
    bs := bs.push (m "x3x3", ← add S (x 3) (x 3))
    bs := bs.push (v "z" (4 * blk + 2) l, ← add S (m "t01232") (m "x3x3"))
    bs := bs.push (v "z" (4 * blk + 3) l, ← add S (m "t01233") (m "x0x0"))
  return bs

/-- `mat4` on every block of four, in place, on words below `2 p` reduced first: the S-box
leaves its powers unreduced, which takes the reduction out of its multiplier-bound kernel. -/
meta def mat4Blocks (S : Shape) (t L : Nat) : MacroM Term := do
  let bs := (← touch) ++ (← readState t L) ++ (← interleave L (mat4Lane S t)) ++ (← store t L "z")
  lets bs (← `($(name "st")))

/-- Add to every coordinate the sum over all blocks of its row, in place. -/
meta def mixBlocks (S : Shape) (t L : Nat) : MacroM Term := do
  let bs := (← touch) ++ (← readState t L) ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    for k in [0:4] do
      let mut acc : Term := v "x" k l
      for blk in [1:t / 4] do
        let s := name s!"S{k}_{l}_{blk}"
        bs := bs.push (s, ← add S acc (v "x" (4 * blk + k) l))
        acc := s
      bs := bs.push (name s!"S{k}_{l}", acc)
    for j in [0:t] do
      bs := bs.push (v "z" j l, ← add S (v "x" j l) (name s!"S{j % 4}_{l}"))
    return bs) ++ (← store t L "z")
  lets bs (← `($(name "st")))

/-- The constant additions and S-boxes of a full round, in place, the powers left below `2 p`. -/
meta def sbox (S : Shape) (t L : Nat) : MacroM Term := do
  let mut bs := (← touch)
  for j in [0:t] do
    bs := bs.push (name s!"c{j}", ← read (name "rc") (name "r") (name "hr") j)
  bs := bs ++ (← readState t L)
  bs := bs ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    for j in [0:t] do
      bs := bs.push (v "a" j l, ← add S (v "x" j l) (name s!"c{j}"))
      bs := bs.push (v "y" j l, ← sboxLazy S (v "a" j l))
    return bs)
  bs := bs ++ (← store t L "y")
  lets bs (← `($(name "st")))

/-- `V_j · x + sum` for the width-`t` diagonal `V` of the field's Poseidon2, which starts
`[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4]` and continues with `±1/2^k`: small multiples and halves as
additions, subtractions and halving, `±1/2^k` with `mulInvPow2`. -/
meta def diagonal (S : Shape) (t j : Nat) (z : Ident) (x acc : Term) :
    MacroM (Array (Ident × Term)) := do
  let tmp (s : String) : Ident := name s!"{z.getId}_{s}"
  match j with
  | 0 => return #[(tmp "2", ← add S x x), (z, ← sub S acc (tmp "2"))]
  | 1 => return #[(z, ← add S acc x)]
  | 2 => return #[(tmp "2", ← add S x x), (z, ← add S acc (tmp "2"))]
  | 3 => return #[(tmp "h", ← halve S x), (z, ← add S acc (tmp "h"))]
  | 4 =>
    return #[(tmp "2", ← add S x x), (tmp "3", ← add S (tmp "2") x),
      (z, ← add S acc (tmp "3"))]
  | 5 =>
    return #[(tmp "2", ← add S x x), (tmp "4", ← add S (tmp "2") (tmp "2")),
      (z, ← add S acc (tmp "4"))]
  | 6 => return #[(tmp "h", ← halve S x), (z, ← sub S acc (tmp "h"))]
  | 7 =>
    return #[(tmp "2", ← add S x x), (tmp "3", ← add S (tmp "2") x),
      (z, ← sub S acc (tmp "3"))]
  | 8 =>
    return #[(tmp "2", ← add S x x), (tmp "4", ← add S (tmp "2") (tmp "2")),
      (z, ← sub S acc (tmp "4"))]
  | _ =>
    match (if t == 16 then S.tail16 else S.tail24)[j - 9]? with
    | some (k, neg) =>
      let s ← `($(name "mulInvPow2") $(S.p) $(lit k) $(lit (S.odd * 2 ^ (S.twoAdicity - k))) $x)
      return #[(tmp "s", s), (z, ← (if neg then sub S else add S) acc (tmp "s"))]
    | none => Macro.throwError s!"no diagonal entry {j} at width {t}"

/-- The sum of `xs` as a tree of additions, adding neighbours level by level, and its root: the
sum of a partial round runs beside its S-box instead of after it. -/
meta partial def treeSum (S : Shape) (pre : String) (xs : Array Term) (level : Nat := 0) :
    MacroM (Array (Ident × Term) × Term) := do
  if xs.size ≤ 1 then return (#[], xs[0]!)
  let mut bs := #[]
  let mut ys := #[]
  for k in [0:xs.size / 2] do
    let n := name s!"{pre}_{level}_{k}"
    bs := bs.push (n, ← add S xs[2 * k]! xs[2 * k + 1]!)
    ys := ys.push (n : Term)
  if xs.size % 2 == 1 then ys := ys.push xs[xs.size - 1]!
  let (bs', r) ← treeSum S pre ys (level + 1)
  return (bs ++ bs', r)

/-- A partial round with constant `c`. -/
meta def partialRound (S : Shape) (t L : Nat) : MacroM Term := do
  let mut bs := (← touch) ++ (← readState t L)
  bs := bs ++ (← interleave L fun l ↦ do
    let mut bs := #[]
    bs := bs.push (v "a" 0 l, ← add S (v "x" 0 l) (name "c"))
    bs := bs.push (v "y" 0 l, ← sboxSign S (v "a" 0 l))
    let (sum, rest) ← treeSum S s!"r{l}"
      ((Array.range (t - 1)).map fun j ↦ (v "x" (j + 1) l : Term))
    bs := bs ++ sum
    bs := bs.push (name s!"s_{l}", ← add S (v "y" 0 l) rest)
    let acc : Term := name s!"s_{l}"
    let ys : Array Term :=
      #[v "y" 0 l] ++ (Array.range (t - 1)).map fun j ↦ (v "x" (j + 1) l : Term)
    -- Coordinate 0: `-2 y + (y + rest) = rest - y`.
    bs := bs.push (v "z" 0 l, ← sub S rest (v "y" 0 l))
    for j in [1:t] do
      bs := bs ++ (← diagonal S t j (v "z" j l) ys[j]! acc)
    return bs)
  bs := bs ++ (← store t L "z")
  lets bs (← `($(name "st")))

/-- Coordinates `0, …, 15` of the eight lanes of a width-`t` group from eight source lines of
sixteen words: word `j` of line `q{l}` of `m` becomes coordinate `j` of lane `l`. -/
meta def load16 (t : Nat) : MacroM Term := do
  let mut bs := (← touch)
  for j in [0:16] do
    for l in [0:8] do
      bs := bs.push (v "x" j l, ← read (name "m") (name s!"q{l}") (name s!"h{l}") j)
  bs := bs ++ (← store t 8 "x").extract 0 17
  lets bs (← `($(name "st").1))

/-- Coordinates `0, …, 15` of the eight lanes of a width-`t` group from sixteen source lines of
eight words: word `l` of line `o{j}` of `c{j}` becomes coordinate `j` of lane `l`. -/
meta def loadColumns (t : Nat) : MacroM Term := do
  let mut bs := (← touch)
  for j in [0:16] do
    for l in [0:8] do
      bs := bs.push (v "x" j l, ← read (name s!"c{j}") (name s!"o{j}") (name s!"h{j}") l)
  bs := bs ++ (← store t 8 "x").extract 0 17
  lets bs (← `($(name "st").1))

/-- Coordinates `0, …, 7` of the eight lanes of the group at `i` of `st`, stored as eight
contiguous digests: lane `l` at word `p{l}` of `out`. -/
meta def store8x8 : MacroM Term := do
  -- `out` written back at `p0` first, as `touch` does for the kernels' groups.
  let mut bs := #[(name "o", ← `($(name "touch8") $(name "out") $(name "p0") $(name "g0")))]
  for j in [0:8] do
    for l in [0:8] do
      bs := bs.push (v "x" j l, ← read (name "st") (name "i") (name "hb") (8 * j + l))
  for l in [0:8] do
    let vs := (Array.range 8).map fun j ↦ (v "x" j l : Term)
    bs := bs.push (name "o", ← `($(name "store8") $(name "o") $(name s!"p{l}") 0 $vs*
      ($(name "storeAt") $(name s!"g{l}"))))
  lets bs (← `($(name "o").1))

end CompStark.Poseidon2.Unrolled

open CompStark.Poseidon2.Unrolled in
/-- The body of a partial round on `L` packed states of width `t`. -/
macro "p2_partial%" f:ident t:num L:num : term => do
  partialRound (← shapeOf f.getId) t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of the constant additions and S-boxes of a full round. -/
macro "p2_sbox%" f:ident t:num L:num : term => do
  sbox (← shapeOf f.getId) t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of `mat4` on every block of four. -/
macro "p2_mat4%" f:ident t:num L:num : term => do
  mat4Blocks (← shapeOf f.getId) t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of the block-sum mixing of the external matrix. -/
macro "p2_mix%" f:ident t:num L:num : term => do
  mixBlocks (← shapeOf f.getId) t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a transposing load of eight lines into a width-`t` group. -/
macro "p2_load16%" t:num : term => load16 t.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a load of sixteen columns' lines of eight words into a group. -/
macro "p2_loadColumns%" t:num : term => loadColumns t.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a transposing store of eight digests from a group. -/
macro "p2_store8x8%" : term => store8x8
