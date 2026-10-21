/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Poseidon2.Map
public import CompPoly.Fields.BabyBear.Fast
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Poseidon2 over BabyBear

Plonky3's default BabyBear instances (`default_babybear_poseidon2_16` and `_24`): S-box
`x ↦ x ^ 7`, four initial and four terminal full rounds, 13 partial rounds at width 16 and 21 at
width 24, and the round constants of the Horizen Labs reference parameters. The constants are
canonical representatives, cast into any field of characteristic `p`, so the same instance runs on
the spec field `BabyBear.Field` and on the Montgomery field `BabyBear.Fast.Field`: the permutation
on the Montgomery field is the specification on `BabyBear.Field`, read through the ring
isomorphism between them (`fast_width16`, `fast_width24`).
-/

@[expose] public section
namespace CompStark.Poseidon2.BabyBear

namespace Constants

/-- Plonky3's round constants of the initial full rounds at width 16. -/
def initial16 : List (Vector Nat 16) := [
    #v[
      1774958255, 1185780729, 1621102414, 1796380621, 588815102, 1932426223, 1925334750, 747903232,
      89648862, 360728943, 977184635, 1425273457, 256487465, 1200041953, 572403254, 448208942],
    #v[
      1215789478, 944884184, 953948096, 547326025, 646827752, 889997530, 1536873262, 86189867,
      1065944411, 32019634, 333311454, 456061748, 1963448500, 1827584334, 1391160226, 1348741381],
    #v[
      88424255, 104111868, 1763866748, 79691676, 1988915530, 1050669594, 359890076, 573163527,
      222820492, 159256268, 669703072, 763177444, 889367200, 256335831, 704371273, 25886717],
    #v[
      51754520, 1833211857, 454499742, 1384520381, 777848065, 1053320300, 1851729162, 344647910,
      401996362, 1046925956, 5351995, 1212119315, 754867989, 36972490, 751272725, 506915399]]

/-- Plonky3's round constants of the partial rounds at width 16. -/
def internal16 : List Nat := [
    1518359488, 1765533241, 945325693, 422793067, 311365592, 1311448267, 1629555936, 1009879353,
    190525218, 786108885, 557776863, 212616710, 605745517]

/-- Plonky3's round constants of the terminal full rounds at width 16. -/
def terminal16 : List (Vector Nat 16) := [
    #v[
      1922082829, 1870549801, 1502529704, 1990744480, 1700391016, 1702593455, 321330495, 528965731,
      183414327, 1886297254, 1178602734, 1923111974, 744004766, 549271463, 1781349648, 542259047],
    #v[
      1536158148, 715456982, 503426110, 340311124, 1558555932, 1226350925, 742828095, 1338992758,
      1641600456, 1843351545, 301835475, 43203215, 386838401, 1520185679, 1235297680, 904680097],
    #v[
      1491801617, 1581784677, 913384905, 247083962, 532844013, 107190701, 213827818, 1979521776,
      1358282574, 1681743681, 1867507480, 1530706910, 507181886, 695185447, 1172395131, 1250800299],
    #v[
      1503161625, 817684387, 498481458, 494676004, 1404253825, 108246855, 59414691, 744214112,
      890862029, 1342765939, 1417398904, 1897591937, 1066647396, 1682806907, 1015795079,
      1619482808]]

/-- Plonky3's round constants of the initial full rounds at width 24. -/
def initial24 : List (Vector Nat 24) := [
    #v[
      262278199, 127253399, 314968988, 246143118, 157582794, 118043943, 454905424, 815798990,
      1004040026, 1773108264, 1066694495, 1930780904, 1180307149, 1464793095, 1660766320,
      1389166148, 343354132, 1307439985, 638242172, 525458520, 1964135730, 1751797115, 1421525369,
      831813382],
    #v[
      695835963, 1845603984, 540703332, 1333667262, 1917861751, 1170029417, 1989924532, 1518763784,
      1339793538, 622609176, 686842369, 1737016378, 1282239129, 897025192, 716894289, 1997503974,
      395622276, 1201063290, 1917549072, 1150912935, 1687379185, 1507936940, 241306552, 989176635],
    #v[
      1147522062, 27129487, 1257820264, 142102402, 217046702, 1664590951, 855276054, 1215259350,
      946500736, 552696906, 1424297384, 538103555, 1608853840, 162510541, 623051854, 1549062383,
      1908416316, 1622328571, 1079030649, 1584033957, 1099252725, 1910423126, 447555988, 862495875],
    #v[
      128479034, 1587822577, 608401422, 1290028279, 342857858, 825405577, 427731030, 1718628547,
      588764636, 204228775, 1454563174, 1740472809, 1338899225, 1269493554, 53007114, 1647670797,
      306391314, 172614232, 51256176, 1221257987, 1239734761, 273790406, 1781980094, 1291790245]]

/-- Plonky3's round constants of the partial rounds at width 24. -/
def internal24 : List Nat := [
    497520322, 1930103076, 1052077299, 1540960371, 924863639, 1365519753, 1726563304, 440300254,
    1891545577, 822033215, 1111544260, 308575117, 1708681573, 1240419708, 1199068823, 1186174623,
    1551596046, 1886977120, 1327682690, 1210751726, 1810596765]

/-- Plonky3's round constants of the terminal full rounds at width 24. -/
def terminal24 : List (Vector Nat 24) := [
    #v[
      53041581, 723038058, 1439947916, 1136469704, 205609311, 1883820770, 14387587, 720724951,
      1854174607, 1629316321, 530151394, 1679178250, 1549779579, 48375137, 976057819, 463976218,
      875839332, 1946596189, 434078361, 1878280202, 1363837384, 1470845646, 1792450386, 1040977421],
    #v[
      1209164052, 714957516, 390340387, 1213686459, 790726260, 117294666, 140621810, 993455846,
      1889603648, 78845751, 925018226, 708123747, 1647665372, 1649953458, 942439428, 1006235079,
      238616145, 930036496, 1401020792, 989618631, 1545325389, 1715719711, 755691969, 150307788],
    #v[
      1567618575, 1663353317, 1950429111, 1891637550, 192082241, 1080533265, 1463323727, 890243564,
      158646617, 1402624179, 59510015, 1198261138, 1065075039, 1150410028, 1293938517, 76770019,
      1478577620, 1748789933, 457372011, 1841795381, 760115692, 1042892522, 1507649755, 1827572010],
    #v[
      1206940496, 1896271507, 1003792297, 738091882, 1124078057, 1889898, 813674331, 228520958,
      1832911930, 781141772, 459826664, 202271745, 1296144415, 1111203133, 1090783436, 641665156,
      1393671120, 1303271640, 809508074, 162506101, 1262312258, 1672219447, 1608891156, 1380248020]]
end Constants

variable (F : Type*) [Field F]

/-- The diagonal `V` of the width-16 internal matrix:
`[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]`. -/
def diagonal16 : Vector F 16 :=
  #v[-2, 1, 2, 2⁻¹, 3, 4, -2⁻¹, -3, -4, (2 ^ 8)⁻¹, 4⁻¹, 8⁻¹, (2 ^ 27)⁻¹, -(2 ^ 8)⁻¹, -16⁻¹,
    -(2 ^ 27)⁻¹]

/-- The diagonal `V` of the width-24 internal matrix: `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7,
-1/2^27]`. -/
def diagonal24 : Vector F 24 :=
  #v[-2, 1, 2, 2⁻¹, 3, 4, -2⁻¹, -3, -4, (2 ^ 8)⁻¹, 4⁻¹, 8⁻¹, 16⁻¹, (2 ^ 7)⁻¹, (2 ^ 9)⁻¹,
    (2 ^ 27)⁻¹, -(2 ^ 8)⁻¹, -4⁻¹, -8⁻¹, -16⁻¹, -32⁻¹, -64⁻¹, -(2 ^ 7)⁻¹, -(2 ^ 27)⁻¹]

/-- Plonky3's default width-16 Poseidon2 over BabyBear, in a field `F` of characteristic `p`. -/
def width16 : Params F 16 :=
  .ofNat 7 Constants.initial16 Constants.internal16 Constants.terminal16 (diagonal16 F)

/-- Plonky3's default width-24 Poseidon2 over BabyBear, in a field `F` of characteristic `p`. -/
def width24 : Params F 24 :=
  .ofNat 7 Constants.initial24 Constants.internal24 Constants.terminal24 (diagonal24 F)

variable {F} {K : Type*} [Field K] (f : F →+* K)

theorem width16_map : (width16 F).map f = width16 K := by
  simp only [width16, Params.ofNat_map, diagonal16, Vector.map_mk, List.map_toArray,
    List.map_cons, List.map_nil, map_neg, map_inv₀, map_pow, map_ofNat, map_one]

theorem width24_map : (width24 F).map f = width24 K := by
  simp only [width24, Params.ofNat_map, diagonal24, Vector.map_mk, List.map_toArray,
    List.map_cons, List.map_nil, map_neg, map_inv₀, map_pow, map_ofNat, map_one]

open _root_.BabyBear.Fast (ringEquiv) in
/-- On the Montgomery field the width-16 permutation is the specification. -/
theorem fast_width16 (s : Vector _root_.BabyBear.Fast.Field 16) :
    (permute (width16 _) s).map ringEquiv =
      permute (width16 _root_.BabyBear.Field) (s.map ringEquiv) := by
  have h := permute_map ringEquiv.toRingHom (width16 _) s
  rw [width16_map] at h
  exact h

open _root_.BabyBear.Fast (ringEquiv) in
/-- On the Montgomery field the width-24 permutation is the specification. -/
theorem fast_width24 (s : Vector _root_.BabyBear.Fast.Field 24) :
    (permute (width24 _) s).map ringEquiv =
      permute (width24 _root_.BabyBear.Field) (s.map ringEquiv) := by
  have h := permute_map ringEquiv.toRingHom (width24 _) s
  rw [width24_map] at h
  exact h

end CompStark.Poseidon2.BabyBear
