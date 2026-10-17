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

meta def add (x y : Term) : MacroM Term := `($(name "add") $x $y)

meta def mul (x y : Term) : MacroM Term := `($(name "mul") $x $y)

meta def sub (x y : Term) : MacroM Term := `($(name "sub") $x $y)

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

/-- `y ^ 3` as two products. -/
meta def cube (out a : Ident) : MacroM (Array (Ident × Term)) := do
  let sq := name s!"{out.getId}_sq"
  return #[(sq, ← mul a a), (out, ← mul sq a)]

/-- The external matrix on lane `l` of `y`: `mat4` per block of four with Plonky3's addition chain,
then
the sum over blocks of each row added to every block. -/
meta def externalLane (t l : Nat) (y : String) (z : String) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  let blocks := t / 4
  for blk in [0:blocks] do
    let x (k : Nat) : Term := v y (4 * blk + k) l
    let m (s : String) : Ident := name s!"m{blk}_{l}_{s}"
    bs := bs.push (m "t01", ← add (x 0) (x 1))
    bs := bs.push (m "t23", ← add (x 2) (x 3))
    bs := bs.push (m "t0123", ← add (m "t01") (m "t23"))
    bs := bs.push (m "t01123", ← add (m "t0123") (x 1))
    bs := bs.push (m "t01233", ← add (m "t0123") (x 3))
    bs := bs.push (m "x0x0", ← add (x 0) (x 0))
    bs := bs.push (m "x2x2", ← add (x 2) (x 2))
    bs := bs.push (v s!"M{blk}r" 3 l, ← add (m "t01233") (m "x0x0"))
    bs := bs.push (v s!"M{blk}r" 1 l, ← add (m "t01123") (m "x2x2"))
    bs := bs.push (v s!"M{blk}r" 0 l, ← add (m "t01123") (m "t01"))
    bs := bs.push (v s!"M{blk}r" 2 l, ← add (m "t01233") (m "t23"))
  for k in [0:4] do
    let mut acc : Term := v "M0r" k l
    for blk in [1:blocks] do
      let s := name s!"S{k}_{l}_{blk}"
      bs := bs.push (s, ← add acc (v s!"M{blk}r" k l))
      acc := s
    bs := bs.push (name s!"S{k}_{l}", acc)
  for blk in [0:blocks] do
    for k in [0:4] do
      bs := bs.push (v z (4 * blk + k) l, ← add (v s!"M{blk}r" k l) (name s!"S{k}_{l}"))
  return bs

/-- The external matrix on all lanes. -/
meta def external (t L : Nat) (y : String) (z : String) : MacroM (Array (Ident × Term)) :=
  interleave L fun l ↦ externalLane t l y z

/-- Store the `t × L` state `z`, one unchecked eight-word store per coordinate: the state stays
a `ByteArray` of the size `n` of `b`, so the bounds come from `h` and no store branches. -/
meta def store (t L : Nat) (z : String) : MacroM (Array (Ident × Term)) := do
  let mut bs := #[(name "st", ← `((⟨$(name "b"), rfl⟩ : { x : ByteArray // x.size = $(name "b").size })))]
  for j in [0:t] do
    let vs := (Array.range L).map fun l ↦ (v z j l : Term)
    let zeros := Array.replicate (16 - L) (lit 0)
    bs := bs.push (name "st", ← `((⟨$(name "putWords") $(name "st") (($(name "i") + $(lit (j * L))) * 4)
      $(lit L) $(vs ++ zeros)*
        ($(name "storeBounds") $(name "hb") $(lit (j * L)) (by simp only [USize.reduceToNat]; decide)),
      $(name "size_putWords") ..⟩ : { x : ByteArray // x.size = $(name "b").size })))
  return bs

/-- `mat4` on every block of four coordinates of lane `l`, with Plonky3's addition chain. -/
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
    bs := bs.push (v "z" (4 * blk + 2) l, ← add (m "t01233") (m "t23"))
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

/-- The initial external matrix. -/
meta def linear (t L : Nat) : MacroM Term := do
  let bs := (← readState t L) ++ (← external t L "x" "z") ++ (← store t L "z")
  lets bs (← `($(name "st").1))

/-- A full round with the constants at word `r` of `rc`. -/
meta def fullRound (t L : Nat) : MacroM Term := do
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
  bs := bs ++ (← external t L "y" "z") ++ (← store t L "z")
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

/-- `V_j · x + sum` for the width-16 diagonal
`V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]`:
small multiples and halves as additions, subtractions and halving, the rest as products with the
diagonal word `d{j}`. -/
meta def diagonal (j : Nat) (z : Ident) (x acc : Term) : MacroM (Array (Ident × Term)) := do
  let t (s : String) : Ident := name s!"{z.getId}_{s}"
  match j with
  | 0 => return #[(t "2", ← add x x), (z, ← sub acc (t "2"))]
  | 1 => return #[(z, ← add acc x)]
  | 2 => return #[(t "2", ← add x x), (z, ← add acc (t "2"))]
  | 3 => return #[(t "h", ← halve x), (z, ← add acc (t "h"))]
  | 4 => return #[(t "2", ← add x x), (t "3", ← add (t "2") x), (z, ← add acc (t "3"))]
  | 5 => return #[(t "2", ← add x x), (t "4", ← add (t "2") (t "2")), (z, ← add acc (t "4"))]
  | 6 => return #[(t "h", ← halve x), (z, ← sub acc (t "h"))]
  | 7 => return #[(t "2", ← add x x), (t "3", ← add (t "2") x), (z, ← sub acc (t "3"))]
  | 8 => return #[(t "2", ← add x x), (t "4", ← add (t "2") (t "2")), (z, ← sub acc (t "4"))]
  | _ => return #[(z, ← add (← mul (name s!"d{j}") x) acc)]

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
    let mut acc : Term := v "y" 0 l
    for j in [1:t] do
      bs := bs.push (v "s" j l, ← add acc (v "x" j l))
      acc := v "s" j l
    let ys : Array Term := #[v "y" 0 l] ++ (Array.range (t - 1)).map fun j ↦ (v "x" (j + 1) l : Term)
    for j in [0:t] do
      bs := bs ++ (← diagonal j (v "z" j l) ys[j]! acc)
    return bs)
  bs := bs ++ (← store t L "z")
  lets bs (← `($(name "st").1))

end CompStark.Poseidon2.Unrolled

open CompStark.Poseidon2.Unrolled in
/-- The body of the external matrix on `L` packed states of width `t`. -/
macro "p2_linear%" t:num L:num : term => linear t.getNat L.getNat

open CompStark.Poseidon2.Unrolled in
/-- The body of a full round on `L` packed states of width `t`. -/
macro "p2_full%" t:num L:num : term => fullRound t.getNat L.getNat

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
