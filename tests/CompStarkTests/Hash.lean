/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.KoalaBear.Hash

/-! # Sponge and compression known answers

Outputs of Plonky3's `PaddingFreeSponge<Perm24, 24, 16, 8>` and
`TruncatedPermutation<Perm16, 2, 8, 16>` on the default KoalaBear Poseidon2 permutations
(`bench/rust`, `cargo run --release`).
-/

namespace CompStarkTests.Hash
open CompStark.Hash

/-- The leaf hash of `0, …, n - 1`, as canonical outputs. -/
def hashIota (n : Nat) : Vector Nat 8 :=
  (KoalaBear.hash _root_.KoalaBear.Field ((List.range n).map Nat.cast)).map ZMod.val

#guard hashIota 0 == #v[0, 0, 0, 0, 0, 0, 0, 0]
#guard hashIota 1 == #v[1372179428, 133812428, 696896225, 1987094720, 2054524407, 903120858,
  1657571027, 324691152]
#guard hashIota 8 == #v[2067671377, 285730248, 67081120, 1570755920, 810744145, 2106090739,
  18027642, 346009986]
#guard hashIota 16 == #v[403818341, 1636855270, 787684945, 1713176768, 2101345750, 943584829,
  1807014356, 1669906235]
#guard hashIota 17 == #v[1076045929, 1862126369, 541684338, 161054317, 197069995, 79500844,
  1582073440, 882092014]
#guard hashIota 32 == #v[300880145, 421418732, 997536514, 622983904, 1383735143, 464819595,
  1098806565, 1343681663]
#guard hashIota 50 == #v[856552550, 535981396, 1199560609, 1880955451, 1889767569, 338613516,
  2127631099, 1133148347]

#guard (KoalaBear.compress _root_.KoalaBear.Field (Vector.ofFn fun i ↦ (i.val : _))
    (Vector.ofFn fun i ↦ ((100 + i.val : Nat) : _))).map ZMod.val ==
  #v[1735060840, 251194189, 1830597343, 733824892, 2052730034, 1625998731, 1433224953,
    835724207]

end CompStarkTests.Hash
