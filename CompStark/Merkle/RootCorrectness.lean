/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Merkle.PackedCorrectness
import all CompStark.Merkle.Packed
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # Correctness of the packed Merkle root

The leaf digests of the chunk tasks, the compression range tasks of every layer and the layer
loop agree with `Merkle.Poseidon2.root` on a single matrix: `root_eq`.
-/

@[expose] public section
namespace CompStark.Merkle.Packed
open CompStark.Poseidon2 CompStark.Poseidon2.Packed
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields array_eq_of_getD)

local notation "F" => KoalaBear.Fast.Field

theorem vget_congr {α : Type*} {n : Nat} (v : Vector α n) {a b : Nat} (h : a = b) (ha : a < n)
    (hb : b < n) : v[a]'ha = v[b]'hb := by subst h; rfl

/-- Digests as consecutive words. -/
def flat (ds : List (Vector F 8)) : Array F := (ds.flatMap Vector.toList).toArray

theorem size_flat (ds : List (Vector F 8)) : (flat ds).size = 8 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [flat, List.flatMap_cons, List.size_toArray, List.length_append,
      Vector.length_toList, List.length_cons] at ih ⊢
    omega

theorem getD_flat (ds : List (Vector F 8)) (k : Nat) :
    (flat ds).getD k 0 = (ds.getD (k / 8) 0)[k % 8]'(Nat.mod_lt _ (by decide)) := by
  induction ds generalizing k with
  | nil => simp only [flat, List.flatMap_nil, List.getD_nil, Vector.getElem_zero]; rfl
  | cons d ds ih =>
    have e : flat (d :: ds) = d.toArray ++ flat ds := Array.toList_inj.mp (by
      simp only [flat, List.flatMap_cons, Array.toList_append, List.append_cancel_right_eq]; rfl)
    rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    simp only [Vector.size_toArray]
    by_cases hk : k < 8
    · simp only [hk, ↓reduceIte, Nat.div_eq_of_lt hk, List.getD_cons_zero, Nat.mod_eq_of_lt hk,
        Vector.getElem?_toArray, Vector.getElem?_eq_getElem hk, Option.getD_some]
    · rw [ite_eq_right hk, ← Array.getD_eq_getD_getElem?, ih,
        show k / 8 = (k - 8) / 8 + 1 by omega, List.getD_cons_succ]
      exact vget_congr _ (by omega) _ _

theorem flat_eq (A : Array F) (ds : List (Vector F 8)) (hs : A.size = 8 * ds.length)
    (h : ∀ i < ds.length, ∀ j (hj : j < 8), A.getD (8 * i + j) 0 = (ds.getD i 0)[j]'hj) :
    A = flat ds := by
  apply array_eq_of_getD _ _ 0 (by rw [hs, size_flat])
  intro k
  rw [getD_flat]
  by_cases hk : k < A.size
  · rw [show k = 8 * (k / 8) + k % 8 by omega, h _ (by omega) _ (Nat.mod_lt _ (by decide))]
    congr 3 <;> omega
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega),
      List.getD_eq_default _ _ (by omega), Option.getD_none, Vector.getElem_zero]

theorem dig_flat (ds : List (Vector F 8)) (k : Nat) : dig (flat ds) k = ds.getD k 0 := by
  ext j hj
  simp only [dig, Vector.getElem_ofFn, getD_flat, show (8 * k + j) / 8 = k by omega]
  exact vget_congr _ (by omega) _ _

/-- Parent `i` of a layer stored as consecutive words. -/
def parent (P : Array F) (i : Nat) : Vector F 8 :=
  CompStark.Hash.Poseidon2.compress F (dig P (2 * i)) (dig P (2 * i + 1))

theorem compressRange_encode (P : Array F) (n o0 count : Nat) (hP : P.size = 8 * n)
    (hu : 4 * P.size < USize.size) (huO : 4 * (8 * count) < USize.size) (hc : o0 + count ≤ n / 2) :
    compressRange (Packed16.ofParams (KoalaBear.width16 F)) (encode P) n o0 count =
      encode (flat ((List.range count).map fun i ↦ parent P (o0 + i))) := by
  have key : ∀ G, ∃ C, (List.range G).foldl (fun out g ↦
      compress8 (Packed16.ofParams (KoalaBear.width16 F)) (encode P) n (o0 + 8 * g) o0 count out)
      (encode (Array.replicate (8 * count) (0 : F))) = encode C ∧ C.size = 8 * count ∧
      ∀ k, C.getD k 0 = if k < 8 * count ∧ k < 64 * G then
        (parent P (o0 + k / 8))[k % 8]'(Nat.mod_lt _ (by decide)) else 0 := by
    intro G
    induction G with
    | zero =>
      refine ⟨_, rfl, Array.size_replicate, fun k ↦ ?_⟩
      rw [ite_eq_right (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> rfl
    | succ G ih =>
      obtain ⟨C, e, s, g⟩ := ih
      rw [List.range_succ, List.foldl_append, e, List.foldl_cons, List.foldl_nil]
      obtain ⟨C', e', s', g'⟩ := compress8_encode P C n (o0 + 8 * G) o0 count hP hu s
        (by rw [s]; exact huO) (by omega) hc
      refine ⟨C', e', s', fun k ↦ ?_⟩
      rw [g', show o0 + 8 * G - o0 = 8 * G by omega]
      by_cases h1 : 8 * (8 * G) ≤ k ∧ k < 8 * count ∧ k < 8 * (8 * G) + 64
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
        rfl
      · rw [ite_eq_right h1, g]
        by_cases h2 : k < 8 * count ∧ k < 64 * G
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  obtain ⟨C, e, s, g⟩ := key ((count + 7) / 8)
  rw [compressRange, zeroWords_fields, e,
    flat_eq C ((List.range count).map fun i ↦ parent P (o0 + i))
      (by rw [s, List.length_map, List.length_range])]
  intro i hi j hj
  rw [List.length_map, List.length_range] at hi
  have hl : i < ((List.range count).map fun i ↦ parent P (o0 + i)).length := by
    rw [List.length_map, List.length_range]; exact hi
  rw [g, ite_eq_left (by omega), List.getD_eq_getElem _ _ hl, List.getElem_map,
    List.getElem_range, show (8 * i + j) / 8 = i by omega]
  exact vget_congr _ (by omega) _ _

theorem flat_append (a b : List (Vector F 8)) : flat (a ++ b) = flat a ++ flat b := by
  simp only [flat, List.flatMap_append, List.append_toArray]

theorem flat_replicate (m : Nat) : flat (List.replicate m 0) = Array.replicate (8 * m) 0 := by
  symm
  apply flat_eq _ _ (by rw [Array.size_replicate, List.length_replicate])
  intro i hi j hj
  rw [List.length_replicate] at hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ite_eq_left (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi, ↓reduceIte,
    Option.getD_some, Vector.getElem_zero]

theorem foldl_spawnAll (parts : Nat) (f : Nat → ByteArray) (e : ByteArray) :
    (CompPoly.Tasks.spawnAll parts f).foldl (fun acc t ↦ acc ++ t.get) e =
      (List.range parts).foldl (fun acc k ↦ acc ++ f k) e := by
  rw [← Array.foldl_map (f := Task.get) (g := fun acc x ↦ acc ++ x),
    CompPoly.Tasks.map_get_spawnAll, Array.foldl_map, ← Array.foldl_toList, Array.toList_range]

theorem foldl_encode_flat (L : Nat → List (Vector F 8)) (m : Nat) :
    (List.range m).foldl (fun acc k ↦ acc ++ encode (flat (L k))) (ByteArray.emptyWithCapacity 0) =
      encode (flat ((List.range m).foldl (fun acc k ↦ acc ++ L k) [])) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, flat_append, CompPoly.PackedRepr.encode_append]

theorem foldl_tiles {α : Type*} (half size : Nat) (g : Nat → α) (m : Nat) :
    (List.range m).foldl (fun acc k ↦ acc ++
      (List.range (min size (half - min half (k * size)))).map fun i ↦ g (k * size + i)) [] =
      (List.range (min half (m * size))).map g := by
  induction m with
  | zero => simp only [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.min_zero, List.map_nil]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    by_cases hm : m * size ≤ half
    · have hs : min half ((m + 1) * size) =
          min half (m * size) + min size (half - min half (m * size)) := by
        rw [Nat.succ_mul]; omega
      rw [hs, List.range_add, List.map_append, List.map_map,
        show min half (m * size) = m * size by omega]
      rfl
    · rw [show half - min half (m * size) = 0 by omega, Nat.min_zero, List.range_zero, List.map_nil,
        List.append_nil]
      rw [Nat.succ_mul]
      congr 2
      omega

theorem nextLayer_encode (ds : List (Vector F 8))
    (hu : 4 * (8 * ds.length) < USize.size) :
    CompStark.Merkle.Packed.nextLayer (Packed16.ofParams (KoalaBear.width16 F)) (encode (flat ds))
        ds.length =
      (encode (flat (CompStark.Merkle.nextLayer (CompStark.Hash.Poseidon2.hash F)
          (CompStark.Hash.Poseidon2.compress F) [] ds)),
        (CompStark.Merkle.nextLayer (CompStark.Hash.Poseidon2.hash F)
          (CompStark.Hash.Poseidon2.compress F) [] ds).length) := by
  have hP := size_flat ds
  unfold CompStark.Merkle.Packed.nextLayer
  dsimp only
  rw [foldl_spawnAll]
  generalize hparts : (if ds.length / 2 < 64 then 1 else min 16 (ds.length / 2 / 32)) = parts
  have hp : 0 < parts := by split at hparts <;> omega
  generalize hsize : (ds.length / 2 + parts - 1) / parts = size
  have hcover : ds.length / 2 ≤ parts * size := by
    subst hsize
    have := Nat.div_add_mod (ds.length / 2 + parts - 1) parts
    have := Nat.mod_lt (ds.length / 2 + parts - 1) hp
    omega
  have hr : ∀ k, CompStark.Merkle.Packed.compressRange (Packed16.ofParams (KoalaBear.width16 F))
      (encode (flat ds)) ds.length (k * size)
        (min size (ds.length / 2 - min (ds.length / 2) (k * size))) =
      encode (flat ((List.range (min size (ds.length / 2 - min (ds.length / 2) (k * size)))).map
        fun i ↦ parent (flat ds) (k * size + i))) := fun k ↦ by
    by_cases hk : k * size ≤ ds.length / 2
    · exact compressRange_encode _ _ _ _ hP (by rw [hP]; exact hu) (by omega) (by omega)
    · rw [show ds.length / 2 - min (ds.length / 2) (k * size) = 0 by omega, Nat.min_zero]
      rfl
  simp only [hr]
  rw [show ByteArray.emptyWithCapacity (32 * _) = ByteArray.emptyWithCapacity 0 from rfl,
    foldl_encode_flat, foldl_tiles,
    show min (ds.length / 2) (parts * size) = ds.length / 2 by omega]
  have hpair : (List.range (ds.length / 2)).map (parent (flat ds)) =
      (List.range (ds.length / 2)).map fun i ↦ CompStark.Hash.Poseidon2.compress F
        (ds.getD (2 * i) 0) (ds.getD (2 * i + 1) 0) := by
    refine List.map_congr_left fun i _ ↦ ?_
    rw [parent, dig_flat, dig_flat]
  have hpad : ds.length / 2 ≤ if ds.length = 2 then 1 else (ds.length / 2 + 1) / 2 * 2 := by
    split <;> omega
  simp only [CompStark.Merkle.nextLayer, CompStark.Merkle.padTo, hpair, padDigests,
    zeroWords_fields,
    ← CompPoly.PackedRepr.encode_append, flat_append, flat_replicate, List.length_append,
    List.length_map, List.length_range, List.length_replicate]
  exact Prod.ext rfl (by omega)

theorem flatten_cons (c : Array F) (cs : List (Array F)) :
    (c :: cs).toArray.flatten = c ++ cs.toArray.flatten := by
  apply Array.toList_inj.mp
  simp only [Array.toList_flatten, List.map_cons, List.flatten_cons, Array.toList_append]

theorem getD_append (A B : Array F) (k : Nat) :
    (A ++ B).getD k 0 = if k < A.size then A.getD k 0 else B.getD (k - A.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

/-- The leaf digests of a chunk of rows of width `w`. -/
def chunkLeaves (w : Nat) (c : Array F) : List (Vector F 8) :=
  (List.range (c.size / w)).map fun r ↦
    CompStark.Hash.Poseidon2.hash F ((⟨w, c.size / w, c⟩ : CompStark.Merkle.Matrix F).row r)

theorem flatMap_chunkLeaves (w : Nat) (cs : List (Array F))
    (hc : ∀ c ∈ cs, c.size % w = 0) (h : Nat) :
    cs.flatMap (chunkLeaves w) = (List.range (cs.map (·.size / w)).sum).map fun r ↦
      CompStark.Hash.Poseidon2.hash F
        ((⟨w, h, cs.toArray.flatten⟩ : CompStark.Merkle.Matrix F).row r) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc0 := hc c List.mem_cons_self
    rw [List.flatMap_cons, ih fun c' h' ↦ hc c' (List.mem_cons_of_mem c h'), List.map_cons,
      List.sum_cons, List.range_add, List.map_append, List.map_map, chunkLeaves]
    have hs : c.size = c.size / w * w := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc0)).symm
    congr 1
    · refine List.map_congr_left fun r hr ↦ congrArg _ ?_
      have hr := List.mem_range.mp hr
      refine List.map_congr_left fun j hj ↦ ?_
      have hj : j < w := List.mem_range.mp hj
      have : r * w + j < c.size := by
        have := Nat.mul_le_mul_right w (show r + 1 ≤ c.size / w by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      simp only [flatten_cons, getD_append, this, ↓reduceIte]
    · refine List.map_congr_left fun r _ ↦ congrArg _ ?_
      refine List.map_congr_left fun j hj ↦ ?_
      have hj := List.mem_range.mp hj
      simp only [flatten_cons, getD_append]
      have : (c.size / w + r) * w + j = c.size + (r * w + j) := by rw [Nat.add_mul, ← hs]; omega
      rw [this, ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem hashChunk_flat (w : Nat) (c : Array F) (hc : c.size % w = 0)
    (hu : 32 * c.size < USize.size) :
    hashChunk (Packed24.ofParams (KoalaBear.width24 F)) (encode c) w (c.size / w) =
      encode (flat (chunkLeaves w c)) := by
  have hs : c.size = c.size / w * w := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc)).symm
  have hr : c.size / w ≤ c.size := Nat.div_le_self _ _
  obtain ⟨D, e, s, g⟩ := hashChunk_encode c w (c.size / w) hs (by omega) (by omega)
  rw [e, flat_eq D (chunkLeaves w c) (by rw [s, chunkLeaves, List.length_map, List.length_range])]
  intro r hr j hj
  have hl := hr
  rw [chunkLeaves, List.length_map, List.length_range] at hr
  rw [g r hr j hj, List.getD_eq_getElem _ _ hl]
  simp only [chunkLeaves, List.getElem_map, List.getElem_range]

theorem leaves_encode (w : Nat) (hw : 0 < w) (cs : List (Array F))
    (hc : ∀ c ∈ cs, c.size % w = 0) (hu : ∀ c ∈ cs, 32 * c.size < USize.size) :
    leaves (Packed24.ofParams (KoalaBear.width24 F)) w (cs.toArray.map encode) =
      (encode (flat (cs.flatMap (chunkLeaves w))), (cs.map (·.size / w)).sum) := by
  unfold leaves
  simp only [CompPoly.Tasks.get_join, Nat.ne_of_gt hw, ↓reduceIte, List.map_toArray,
    List.foldl_toArray', List.map_map, Function.comp_def, CompPoly.Tasks.get_spawn,
    size_encode_fields, Nat.mul_div_mul_left _ _ (show 0 < 4 by decide)]
  rw [List.map_congr_left fun c hc' ↦ hashChunk_flat w c (hc c hc') (hu c hc'),
    show ByteArray.emptyWithCapacity (32 * _) = encode (flat []) from rfl]
  have fold : ∀ (cs : List (Array F)) (L : List (Vector F 8)),
      (cs.map fun c ↦ encode (flat (chunkLeaves w c))).foldl (· ++ ·) (encode (flat L)) =
        encode (flat (L ++ cs.flatMap (chunkLeaves w))) := by
    intro cs
    induction cs with
    | nil => intro L; rw [List.map_nil, List.foldl_nil, List.flatMap_nil, List.append_nil]
    | cons c cs ih =>
      intro L
      rw [List.map_cons, List.foldl_cons, ← CompPoly.PackedRepr.encode_append, ← flat_append, ih,
        List.flatMap_cons, List.append_assoc]
  have sum : ∀ (cs : List (Array F)) (a : Nat),
      cs.foldl (fun acc c ↦ acc + c.size / w) a = a + (cs.map (·.size / w)).sum := by
    intro cs
    induction cs with
    | nil => intro a; rfl
    | cons c cs ih => intro a; rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega
  rw [fold, List.foldl_map]
  simp only [size_encode_fields, Nat.mul_div_mul_left _ _ (show 0 < 4 by decide)]
  rw [sum, List.nil_append, Nat.zero_add]

local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

/-- One step of the layer loop. -/
def step (L : List (Vector F 8)) : List (Vector F 8) :=
  if L.length ≤ 1 then L else CompStark.Merkle.nextLayer hashF compF [] L

theorem upperLayers_nil (f : Nat) (L : List (Vector F 8)) :
    CompStark.Merkle.upperLayers hashF compF f [] L = step^[f] L := by
  induction f generalizing L with
  | zero => rfl
  | succ f ih =>
    rw [CompStark.Merkle.upperLayers, Function.iterate_succ_apply]
    by_cases h : L.length ≤ 1
    · have fix : ∀ g, step^[g] L = L := fun g ↦ by
        induction g with
        | zero => rfl
        | succ g ihg => rw [Function.iterate_succ_apply', ihg, step, ite_eq_left h]
      rw [ite_eq_left h, step, ite_eq_left h, fix]
    · rw [ite_eq_right h, step, ite_eq_right h, ← ih]
      rfl

theorem length_step (L : List (Vector F 8)) :
    (step L).length = if L.length ≤ 1 then L.length else
      if L.length = 2 then 1 else (L.length / 2 + 1) / 2 * 2 := by
  unfold step
  split
  · rfl
  · simp only [CompStark.Merkle.nextLayer, CompStark.Merkle.padTo, List.length_append,
      List.length_map, List.length_range, List.length_replicate]
    split <;> omega

theorem iterate_step_fix (L : List (Vector F 8)) (h : L.length ≤ 1) (g : Nat) : step^[g] L = L := by
  induction g with
  | zero => rfl
  | succ g ihg => rw [Function.iterate_succ_apply', ihg, step, ite_eq_left h]

theorem iterate_step_length (k : Nat) : ∀ L : List (Vector F 8), L.length ≤ 2 ^ k →
    (step^[k] L).length ≤ 1 := by
  induction k with
  | zero => intro L h; exact h
  | succ k ih =>
    intro L h
    rw [Function.iterate_succ_apply]
    apply ih
    rw [length_step]
    have : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
    have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    split
    · have := Nat.one_le_two_pow (n := k); omega
    · split
      · have := Nat.one_le_two_pow (n := k); omega
      · rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp only [Nat.zero_add, Nat.pow_one] at h; omega
        · have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
          omega

theorem iterate_step_stable (k a : Nat) (L : List (Vector F 8)) (h : L.length ≤ 2 ^ k)
    (hk : k ≤ a) : step^[a] L = step^[k] L := by
  rw [show a = (a - k) + k by omega, Function.iterate_add_apply,
    iterate_step_fix _ (iterate_step_length k L h)]

theorem foldl_range_const {α : Type*} (g : α → α) (n : Nat) (x : α) :
    (List.range n).foldl (fun a _ ↦ g a) x = g^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Function.iterate_succ_apply']

theorem padDigests_flat (L : List (Vector F 8)) (p : Nat) :
    padDigests (encode (flat L)) L.length p = encode (flat (CompStark.Merkle.padTo 0 p L)) := by
  rw [padDigests, zeroWords_fields, CompStark.Merkle.padTo, flat_append, flat_replicate,
    CompPoly.PackedRepr.encode_append]

theorem flat_singleton (r : Vector F 8) : flat [r] = r.toArray :=
  Array.toList_inj.mp (by
    simp only [flat, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rfl)

theorem rootOfLeaves_encode (L : List (Vector F 8)) (h1 : 1 ≤ L.length)
    (hu : 32 * (L.length + 1) < USize.size) :
    rootOfLeaves (Packed16.ofParams (KoalaBear.width16 F)) (encode (flat L)) L.length =
      encode ((CompStark.Merkle.upperLayers hashF compF
        (CompStark.Merkle.padTo 0 (CompStark.Merkle.padEven L.length) L).length []
        (CompStark.Merkle.padTo 0 (CompStark.Merkle.padEven L.length) L)).headD 0).toArray := by
  unfold rootOfLeaves
  dsimp only
  generalize hP : CompStark.Merkle.padTo 0 (CompStark.Merkle.padEven L.length) L = P
  have hPl : P.length = CompStark.Merkle.padEven L.length := by
    rw [← hP, CompStark.Merkle.padTo, List.length_append, List.length_replicate,
      CompStark.Merkle.padEven]
    split <;> omega
  have hpad : (if L.length = 1 then 1 else L.length + L.length % 2) = P.length := by
    rw [hPl, CompStark.Merkle.padEven]
  rw [hpad, padDigests_flat, ← hpad, show (if L.length = 1 then 1 else L.length + L.length % 2) =
    CompStark.Merkle.padEven L.length from rfl, hP, ← hPl, foldl_range_const, upperLayers_nil]
  have hPu : 32 * P.length < USize.size := by
    rw [hPl, CompStark.Merkle.padEven]; split <;> omega
  have hP1 : 1 ≤ P.length := by rw [hPl, CompStark.Merkle.padEven]; split <;> omega
  -- The loop runs `step` on the encoded layers.
  have comm : ∀ n, ∀ Q : List (Vector F 8), 1 ≤ Q.length → 32 * Q.length < USize.size →
      (fun acc : ByteArray × Nat ↦ if acc.2 ≤ 1 then acc else
          CompStark.Merkle.Packed.nextLayer (Packed16.ofParams (KoalaBear.width16 F))
            acc.1 acc.2)^[n]
        (encode (flat Q), Q.length) = (encode (flat (step^[n] Q)), (step^[n] Q).length) ∧
        1 ≤ (step^[n] Q).length ∧ (step^[n] Q).length ≤ Q.length := by
    intro n
    induction n with
    | zero => intro Q h1 _; exact ⟨rfl, h1, le_rfl⟩
    | succ n ih =>
      intro Q h1 hQ
      have hs : 1 ≤ (step Q).length ∧ (step Q).length ≤ Q.length := by
        rw [length_step]; split
        · omega
        · split <;> omega
      obtain ⟨e, l1, l2⟩ := ih (step Q) hs.1 (by omega)
      refine ⟨?_, l1, by rw [Function.iterate_succ_apply]; omega⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← e]
      congr 1
      dsimp only
      by_cases hq : Q.length ≤ 1
      · rw [ite_eq_left hq, step, ite_eq_left hq]
      · rw [ite_eq_right hq, step, ite_eq_right hq, nextLayer_encode Q (by omega)]
  obtain ⟨e, l1, _⟩ := comm 64 P hP1 hPu
  rw [e]
  have h64 : P.length ≤ 2 ^ 64 := by
    rcases USize.size_eq with h | h <;> rw [h] at hPu <;> omega
  have hn : P.length ≤ 2 ^ P.length := Nat.lt_two_pow_self.le
  rw [← iterate_step_stable 64 (64 + P.length) P h64 (by omega),
    ← iterate_step_stable P.length (64 + P.length) P hn (by omega)]
  have hl := iterate_step_length 64 P h64
  rw [iterate_step_stable 64 (64 + P.length) P h64 (by omega)]
  generalize step^[64] P = R at hl l1 ⊢
  match R, hl, l1 with
  | [r], _, _ =>
    simp only [flat_singleton, List.headD_cons]

/-- The packed Merkle root of a matrix given as chunks of rows is Plonky3's root. -/
theorem root_eq (w : Nat) (hw : 0 < w) (cs : List (Array F))
    (hc : ∀ c ∈ cs, c.size % w = 0) (hu : ∀ c ∈ cs, 32 * c.size < USize.size)
    (hh : 0 < (cs.map (·.size / w)).sum)
    (hl : 32 * ((cs.map (·.size / w)).sum + 1) < USize.size) :
    root (Packed24.ofParams (KoalaBear.width24 F)) (Packed16.ofParams (KoalaBear.width16 F)) w
        (cs.toArray.map encode) =
      encode (CompStark.Merkle.Poseidon2.root F
        [⟨w, (cs.map (·.size / w)).sum, cs.toArray.flatten⟩]).toArray := by
  generalize hH : (cs.map (·.size / w)).sum = H at hh hl
  unfold root
  rw [leaves_encode w hw cs hc hu, hH, flatMap_chunkLeaves w cs hc H, hH]
  dsimp only
  have hlen : ((List.range H).map fun r ↦
      hashF ((⟨w, H, cs.toArray.flatten⟩ : CompStark.Merkle.Matrix F).row r)).length = H := by
    rw [List.length_map, List.length_range]
  have e := rootOfLeaves_encode ((List.range H).map fun r ↦
      hashF ((⟨w, H, cs.toArray.flatten⟩ : CompStark.Merkle.Matrix F).row r))
    (by rw [hlen]; exact hh) (by rw [hlen]; exact hl)
  rw [hlen] at e
  rw [e]
  simp only [CompStark.Merkle.Poseidon2.root, CompStark.Merkle.root, List.mergeSort_singleton,
    List.headD_cons, List.takeWhile_cons, beq_self_eq_true, List.takeWhile_nil,
    CompStark.Merkle.firstLayer, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_cons, List.length_nil, ite_true,
    List.drop_succ_cons, List.drop_zero, Nat.zero_add]

end CompStark.Merkle.Packed
