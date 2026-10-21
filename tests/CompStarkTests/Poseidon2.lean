/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.KoalaBear.Poseidon2

/-! # Poseidon2 known answers

Outputs of Plonky3's `default_koalabear_poseidon2_16` and `_24`
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

#guard spec16 zero16 == #v[1467453764, 68262570, 2085334433, 1711169726, 869537427, 698494029,
  1998923102, 727938840, 1236421175, 857433239, 1995651691, 1526804549, 968729910, 15322618,
  1511105384, 1900792116]

#guard spec16 iota16 == #v[1259554834, 663463928, 1989430097, 476523442, 836740795, 1803459961,
  1229318262, 2023956904, 2054405130, 1556655036, 1455339712, 1471465890, 423337459, 353979748,
  1203410294, 1592576868]

#guard spec16 sage16 == #v[1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110,
  1391183747, 351743874, 1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461,
  748270449, 651545025]

#guard fast16 sage16 == spec16 sage16

#guard spec24 (Vector.replicate 24 0) == #v[1918697942, 2025897067, 904050874, 1093610768,
  214053233, 1029880100, 2130076554, 348914674, 1690826780, 1746457725, 397349473, 1037728683,
  217139752, 1271784670, 1515047731, 784532753, 1019638077, 322148854, 291094520, 370500222,
  899996969, 2115305425, 979986821, 471585472]

#guard spec24 (Vector.ofFn (·.val)) == #v[723511737, 87131171, 587052829, 1323145575, 949917837,
  2060493993, 234724110, 834906887, 306751607, 1771020267, 329216878, 823818173, 765507096,
  1447982946, 605505945, 247386051, 1223069940, 354661286, 233493652, 2075130821, 1961191294,
  313483662, 1701936810, 1815724394]

/-- info: 'CompStark.Poseidon2.Packed.permute16_width16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Poseidon2.Packed.permute16_width16

/-- info: 'CompStark.Poseidon2.Packed.permute24_width24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.Poseidon2.Packed.permute24_width24

/-- info: 'CompStark.KoalaBear.perm16_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.perm16_eq

/-- info: 'CompStark.KoalaBear.perm24_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompStark.KoalaBear.perm24_eq

end CompStarkTests.Poseidon2
