/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Poseidon2.KoalaBear
import CompStark.Poseidon2.PackedCorrectness
import CompStark.Poseidon2.PackedCorrectness24

/-! # Poseidon2 known answers

Outputs of Plonky3 0.4.2's `default_koalabear_poseidon2_16` and `_24`
(`bench/rust`, `cargo run --release`), on the spec field and the Montgomery
field.
-/

namespace CompStarkTests.Poseidon2
open CompStark.Poseidon2

/-- The width-16 permutation on canonical inputs, as canonical outputs, on the spec field. -/
def spec16 (x : Vector Nat 16) : Vector Nat 16 :=
  (permute (KoalaBear.width16 _root_.KoalaBear.Field) (x.map Nat.cast)).map ZMod.val

/-- The width-24 permutation on canonical inputs, as canonical outputs, on the spec field. -/
def spec24 (x : Vector Nat 24) : Vector Nat 24 :=
  (permute (KoalaBear.width24 _root_.KoalaBear.Field) (x.map Nat.cast)).map ZMod.val

/-- The width-16 permutation on the Montgomery field. -/
def fast16 (x : Vector Nat 16) : Vector Nat 16 :=
  (permute (KoalaBear.width16 _root_.KoalaBear.Fast.Field)
    (x.map fun (n : Nat) ↦ _root_.KoalaBear.Fast.ofField (n : _root_.KoalaBear.Field))).map fun y ↦
      (_root_.KoalaBear.Fast.ringEquiv y).val

def zero16 : Vector Nat 16 := Vector.replicate 16 0
def iota16 : Vector Nat 16 := Vector.ofFn (·.val)
def sage16 : Vector Nat 16 :=
  #v[894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
    120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
    1783754913]

#guard spec16 zero16 == #v[1194359470, 20586639, 1240637140, 1730441233, 2130651597, 2003319866,
  1017798662, 222976322, 488727120, 474647328, 1184838029, 219759704, 2028817067, 2056706922,
  1578739509, 2000630822]

#guard spec16 iota16 == #v[2089692522, 1915416326, 492489469, 252860357, 1061679923, 82240369,
  1810169820, 1585792269, 1096226960, 1569781184, 1452705076, 2081290613, 1344369360,
  1949099839, 544415199, 892194947]

#guard spec16 sage16 == #v[190453639, 458899855, 383789123, 1958965770, 1470307143, 135446903,
  1980271247, 26609194, 337889870, 543343594, 900082402, 1267415354, 1018710090, 902823573,
  1161524658, 1483653556]

#guard fast16 sage16 == spec16 sage16

#guard spec24 (Vector.replicate 24 0) == #v[1372179428, 133812428, 696896225, 1987094720,
  2054524407, 903120858, 1657571027, 324691152, 344396689, 134463269, 1897168723, 1087497082,
  739751391, 1242866705, 426389026, 1390578948, 1453710565, 300242462, 498514495, 750539631,
  1732736931, 148744772, 1655026465, 2073801105]

#guard spec24 (Vector.ofFn (·.val)) == #v[1066957349, 1187481218, 1896457856, 2097200787,
  1255095997, 1603911976, 296344071, 943491381, 527145271, 408365780, 129005542, 652050596,
  1457594694, 1386323341, 1797036470, 1137586744, 1264986356, 1342061487, 1643886210,
  1603170659, 2078478589, 56048766, 446199937, 1551853266]



/-- info: 'CompStark.Poseidon2.Packed.permute16_width16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Poseidon2.Packed.permute16_width16

/-- info: 'CompStark.Poseidon2.Packed.permute24_width24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Poseidon2.Packed.permute24_width24

end CompStarkTests.Poseidon2
