/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Challenger

/-! # Challenger known answers

Plonky3's `DuplexChallenger<KoalaBear, Poseidon2KoalaBear<24>, 24, 16>` on a fixed sequence
(`bench/rust: RAYON_NUM_THREADS=1 compstark-bench challenger`): observe `0, …, 19`, sample two
elements and an extension element, observe `7` and the extension element `100 + 101 X + 102 X² +
103 X³`, sample 10 bits, grind 6 bits, and sample once more.
-/

namespace CompStarkTests.Challenger
open CompStark.KoalaBear

local notation "F" => _root_.KoalaBear.Fast.Field

def canon (x : F) : Nat := Montgomery.Native32.FastField.toNat x

def run : List Nat :=
  let c := (List.range 20).foldl (fun c i ↦ Transcript.observe c (i : F)) Transcript.init
  let (a, c) := c.sample
  let (b, c) := c.sample
  let (e, c) := c.sampleExt
  let c := (c.observe 7).observeExt ⟨100, 101, 102, 103⟩
  let (bits, c) := c.sampleBits 10
  let (w, c) := c.grind 6
  let (z, _) := c.sample
  [canon a, canon b, canon e.c0, canon e.c1, canon e.c2, canon e.c3, bits, canon w, canon z]

#guard run == [1315075128, 621498114, 1241469331, 965142788, 1213494102, 2071041246, 703, 123,
  1348157896]

end CompStarkTests.Challenger
