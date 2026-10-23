/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Openings
public import CompStark.Stark.Fast.ProgWords
public import CompStark.Stark.Fast.ProgGroup
public import CompStark.Stark.Constraints

/-! # The fast quotient is the specification's

The fast quotient works in the extension's stored, bit-reversed row order. Stored row `j` is the
quotient domain's natural row `perm[j]`; the trace there is the extension's row `j`, because the
bit reversal is an involution (`bitRevPerm_getD_getD`). Its next row is stored at `next[j]`, and
its selectors and inverse vanishing polynomial are the specification's at `perm[j]`. So every
block of stored rows holds the specification's rows `quotientRow … perm[j]`, and reordering by
`perm` puts row `r` in place.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial

open Montgomery.Native32

section
variable {F : Type} [BaseField F]

theorem rowAcc_cons (a : Expr F × List F) (cw : List (Expr F × List F)) (ev : Expr F → F) (j : Nat)
    (x : F) : rowAcc (a :: cw) ev j x = rowAcc cw ev j (x + ev a.1 * a.2.getD j 0) := by
  rw [rowAcc, rowAcc, List.foldl_cons]

/-- The rows `perm[0], perm[1], …` of a matrix. -/
theorem permuteRows_eq (m : Mat F) (perm : Array Nat) : permuteRows m perm =
    Array.ofFn (n := perm.size * m.width) fun k ↦
      m.values.getD (perm.getD (k.val / m.width) 0 * m.width + k.val % m.width) 0 := by
  simp only [permuteRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← Array.foldl_toList]
  have : perm.toList = (List.range' 0 perm.size).map (perm.getD · 0) := by
    apply List.ext_getElem (by simp only [Array.length_toList, List.length_map, List.length_range'])
    intro i h1 h2
    rw [Array.length_toList] at h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  rw [this, List.foldl_map, CompStark.Stark.foldl_blocks, Array.emptyWithCapacity_eq,
    Array.empty_append]
  simp only [Nat.zero_add]
  rfl

/-- Entry `(r, c)` of the rows `perm[0], perm[1], …`. -/
theorem permuteRows_getD (m : Mat F) (perm : Array Nat) (r c : Nat) (hr : r < perm.size)
    (hc : c < m.width) : (permuteRows m perm).getD (r * m.width + c) 0 =
      m.values.getD (perm.getD r 0 * m.width + c) 0 := by
  have hlt : r * m.width + c < perm.size * m.width := by
    have : (r + 1) * m.width ≤ perm.size * m.width := Nat.mul_le_mul_right _ hr
    rw [Nat.succ_mul] at this
    omega
  rw [permuteRows_eq, NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
  have hd : (r * m.width + c) / m.width = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
  have hm : (r * m.width + c) % m.width = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [hd, hm]

theorem getD_map_lt {α β : Type} (a : Array α) (f : α → β) (j : Nat) (h : j < a.size) (d : β)
    (d' : α) : (a.map f).getD j d = f (a.getD j d') := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]

end

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-! ### The bit-reversal permutation -/

theorem bitRevPerm_getD_lt (b i : Nat) (hi : i < 2 ^ b) : (bitRevPerm b).getD i 0 < 2 ^ b := by
  rw [bitRevPerm_getD b i hi]
  exact NTT.Transform.bitRevNat_lt b i

/-- `bitRevPerm` is an involution. -/
theorem bitRevPerm_getD_getD (b i : Nat) (hi : i < 2 ^ b) :
    (bitRevPerm b).getD ((bitRevPerm b).getD i 0) 0 = i := by
  rw [bitRevPerm_getD b _ (bitRevPerm_getD_lt b i hi), bitRevPerm_getD b i hi,
    NTT.Transform.bitRevNat_involutive b i hi]

/-! ### Parallel ranges of blocks -/

/-- Words `i, …, i + B - 1` of an encoded array. -/
theorem slice_encode_ofFn (a : Array F) (i B : Nat) (h : i + B ≤ a.size) :
    slice (encode a) i B = encode (Array.ofFn (n := B) fun k ↦ a.getD (i + k.val) 0) := by
  rw [slice_encode]
  congr 1
  apply Array.ext (by rw [Array.size_extract, Array.size_ofFn]; omega)
  intro k h1 h2
  rw [Array.getElem_extract, Array.getElem_ofFn, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-! ### The specification's trace and the tables -/

theorem lt_of_mem_bitRevPerm {b i : Nat} (h : i ∈ bitRevPerm b) : i < 2 ^ b := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp h
  have := bitRevPerm_getD_lt b j (by rw [← size_bitRevPerm b]; exact hj)
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at this

/-- A table of the selector values `sel` in stored order. -/
theorem table_encode (d l : Nat) (sel : Array F) (f : Nat → F)
    (hf : ∀ i < 2 ^ (d + l), f i = sel.getD i 0) :
    NTTFast.Packed.Native.encodeFields ((bitRevPerm (d + l)).map f) =
      encode ((bitRevPerm (d + l)).map fun i ↦ sel.getD i 0) := by
  rw [NTTFast.Packed.Native.encodeFields_eq]
  exact congrArg encode (Array.map_congr_left fun i hi ↦ hf i (lt_of_mem_bitRevPerm hi))

theorem tables_first [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).first =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qFirst d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ by unfold qFirst; rw [NTTFast.Packed.getD_ofFn_bounded _ i hi]

theorem tables_last [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).last =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qLast d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ by unfold qLast; rw [NTTFast.Packed.getD_ofFn_bounded _ i hi]

theorem tables_trans [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).trans =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qTrans d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ (getD_map_lt (cosetPoints (gen : F) (d + l))
    (· - (twoAdicGen d)⁻¹) i (by rw [size_cosetPoints]; exact hi) 0 0).symm

theorem tables_next [Mont32BaseField p] (d l j : Nat) (hj : j < 2 ^ (d + l)) :
    (quotientTables (p := p) d l).next.getD j 0 =
      (bitRevPerm (d + l)).getD (((bitRevPerm (d + l)).getD j 0 + 2 ^ l) % 2 ^ (d + l)) 0 :=
  getD_map_lt _ _ j (by rw [size_bitRevPerm]; exact hj) 0 0

/-! ### The quotient law -/

theorem getElem!_lit4
    (a b c d : ByteArray) : #[a, b, c, d][0]! = a ∧ #[a, b, c, d][1]! = b ∧ #[a, b, c,
        d][2]! = c ∧ #[a, b, c, d][3]! = d := ⟨rfl, rfl, rfl, rfl⟩

theorem word_encode_ofFn (B : Nat) (hB : 4 * B < USize.size) (X : Nat → F) (k : Nat)
    (hk : k < B) : word (encode (Array.ofFn (n := B) fun i ↦ X i.val)) k = X k := by
  rw [word, Words.read_encode _ _ (by rw [Array.size_ofFn]; exact hB)
      (by rw [Array.size_ofFn]; exact hk),
    NTTFast.Packed.ofWord_val, NTTFast.Packed.getD_ofFn_bounded _ _ hk]

theorem word_tab {B : Nat} (hB : 4 * B < USize.size) (f : Nat → F) (i : Nat) (hi : i < B) :
    word (encode (tab B f)) i = f i :=
  word_encode_ofFn B hB f i hi

/-- The block height of the quotient tables: a power of two, at most 256, dividing the domain. -/
theorem tables_B [Mont32BaseField p] (d l : Nat) :
    0 < (quotientTables (p := p) d l).B ∧ (quotientTables (p := p) d l).B ≤ 256 ∧
      (quotientTables (p := p) d l).B ∣ 2 ^ (d + l) := by
  have hTB : (quotientTables (p := p) d l).B =
      min (2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16)) 256 := rfl
  have hpow : ∃ e, 2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16) = 2 ^ e ∧
      2 ^ e ∣ 2 ^ (d + l) := by
    split
    · exact ⟨d + l, Nat.div_one _, dvd_refl _⟩
    · rename_i hge
      have h12 : 12 ≤ d + l := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : d + l < 12))
          (le_refl _))
      have h16 : 2 ^ (d + l) = 16 * 2 ^ (d + l - 4) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        congr 1
        omega
      refine ⟨d + l - 4, ?_, Nat.pow_dvd_pow 2 (by omega)⟩
      rw [h16, Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨e, hRe, hd⟩ := hpow
  rw [hTB, hRe]
  refine ⟨Nat.lt_min.mpr ⟨Nat.two_pow_pos _, by decide⟩, Nat.min_le_right _ _, ?_⟩
  by_cases h8 : e ≤ 8
  · rw [Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h8) (le_refl (2 ^ 8)))]
    exact hd
  · rw [Nat.min_eq_right
      (le_trans (le_refl (2 ^ 8)) (Nat.pow_le_pow_right (by decide) (by omega)))]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd

/-- Blocks of `B` values from block `b0` appended in order, every step appending its block `a`'s
values `g (a B + i)` while keeping the invariant `Inv` of its state. -/
theorem foldl_blocks_eq {α σ : Type} (B b0 nb : Nat) (g : Nat → α) (Inv : σ → Prop)
    (step : Array α × σ → Nat → Array α × σ)
    (hstep : ∀ (out : Array α) (st : σ) (a : Nat), Inv st → b0 ≤ a → a < b0 + nb →
      Inv (step (out, st) a).2 ∧ (step (out, st) a).1 = out ++ Array.ofFn (n := B) fun i ↦
        g (a * B + i.val))
    (out0 : Array α) (h0 : out0 = #[]) (st0 : σ) (hi : Inv st0) :
    (List.foldl step (out0, st0) (List.range' b0 nb)).1 =
      Array.ofFn (n := nb * B) fun k ↦ g (b0 * B + k.val) := by
  suffices hm : ∀ m ≤ nb, ∃ st, Inv st ∧ List.foldl step (out0, st0) (List.range' b0 m) =
      (Array.ofFn (n := m * B) fun k ↦ g (b0 * B + k.val), st) by
    obtain ⟨st, -, e⟩ := hm nb le_rfl
    rw [e]
  intro m hm
  induction m with
  | zero =>
    refine ⟨st0, hi, ?_⟩
    rw [List.range'_zero, List.foldl_nil, h0]
    congr 1
    exact (Array.eq_empty_of_size_eq_zero (by rw [Array.size_ofFn, Nat.zero_mul])).symm
  | succ m ih =>
    obtain ⟨st, hst, e⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, e, List.foldl_cons, List.foldl_nil, Nat.one_mul]
    obtain ⟨h1, h2⟩ := hstep _ st (b0 + m) hst (by omega) (by omega)
    refine ⟨_, h1, Prod.ext ?_ rfl⟩
    rw [h2, show (Array.ofFn (n := B) fun i ↦ g ((b0 + m) * B + i.val)) =
      Array.ofFn (n := B) fun i ↦ (fun k ↦ g (b0 * B + k)) (m * B + i.val) from
        congrArg Array.ofFn (funext fun i ↦ by simp only; congr 1; ring),
      ofFn_append_ofFn (fun k ↦ g (b0 * B + k)) (m * B) B, show m * B + B = (m + 1) * B by ring]

theorem powerSeq_getD [Mont32BaseField p] [Binomial4 p] (alpha : EF) (K k : Nat) (hk : k < K) :
    (powerSeq alpha K).getD k 0 = Ext.pow alpha k := by
  suffices h : ∀ n, (List.range n).foldl (fun (acc, x) _ ↦ (acc.push x, x * alpha))
      ((#[] : Array EF), 1) = (Array.ofFn (n := n) fun i ↦ Ext.pow alpha i.val,
        Ext.pow alpha n) by
    rw [powerSeq, h K, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
      rw [Array.size_ofFn]; exact hk), Option.getD_some, Array.getElem_ofFn]
  intro n
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    refine Prod.ext (by rw [Array.ofFn_zero]) ?_
    show (1 : EF) = Ext.pow alpha 0
    rw [Ext.pow]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    refine Prod.ext ?_ ?_
    · show (Array.ofFn fun i : Fin n ↦ Ext.pow alpha i.val).push (Ext.pow alpha n) = _
      exact (Array.ofFn_succ (f := fun i : Fin (n + 1) ↦ Ext.pow alpha i.val)).symm
    · show Ext.pow alpha n * alpha = Ext.pow alpha (n + 1)
      apply Challenge.toSpec.injective
      rw [Challenge.toSpec_mul, Ext.toSpec_pow, Ext.toSpec_pow, pow_succ]

theorem weightCoords_eq [Mont32BaseField p] [Binomial4 p] (alpha : EF) (K : Nat) :
    weightCoords alpha K = Array.ofFn (n := 4 * K) fun i ↦
      (Ext.coeffs (Ext.pow alpha (K - 1 - i.val / 4))).getD (i.val % 4) 0 := by
  unfold weightCoords
  refine congrArg Array.ofFn (funext fun i ↦ ?_)
  rw [powerSeq_getD alpha K _ (by have := i.isLt; omega)]

/-- A program on groups of rows by the kernel with its code is the program on the group machine. -/
theorem groupRun_eq (kernels : List (Prog.GroupKernel p)) (code : Array (Prog.Instr F))
    (env : Prog.GroupEnv) (s : ByteArray) :
    groupRun (kernelFor kernels code) code env s = Prog.run (Prog.groupMachine p env) code s := by
  unfold groupRun kernelFor
  rcases hk : List.find? (fun k ↦ k.code == code) kernels with _ | k
  · rw [hk]
  · rw [hk]
    have := beq_iff_eq.mp (List.find?_some (p := fun k : Prog.GroupKernel p ↦ k.code == code) hk)
    show k.run env s = _
    rw [k.run_eq, this]

/-- The program `progRun` gives is the constraints' compiled program. -/
theorem progRun_fst (ks : List (CheckedKernel p)) (cs : List (Expr F)) :
    (progRun ks cs).1 = Prog.compile cs := by
  unfold progRun
  split
  · rename_i k hk
    have hc : k.1.cs = cs :=
      of_decide_eq_true (List.find?_some (p := fun k : CheckedKernel p ↦ decide (k.1.cs = cs)) hk)
    rw [k.1.prog_eq, hc]
  · rfl

/-- The run `progRun` gives is the compiled program on the group machine. -/
theorem progRun_snd (ks : List (CheckedKernel p)) (cs : List (Expr F)) (env : Prog.GroupEnv)
    (s : ByteArray) :
    (progRun ks cs).2 env s = Prog.run (Prog.groupMachine p env) (Prog.compile cs).code s := by
  unfold progRun
  split
  · rename_i k hk
    have hc : k.1.cs = cs :=
      of_decide_eq_true (List.find?_some (p := fun k : CheckedKernel p ↦ decide (k.1.cs = cs)) hk)
    show k.1.kernel.run env s = _
    rw [k.1.kernel.run_eq, k.2, k.1.prog_eq, hc]
  · exact groupRun_eq _ _ env s

/-- **The quotient's blocks**: a program accumulating, on every block of rows, every stored row
`j`'s value coordinates `Q j`, gives the quotient values in natural order. -/
theorem quotientBlocks_eq [Mont32BaseField p] [Binomial4 p] (d l : Nat) (prog : Prog F)
    (run : Prog.GroupEnv → ByteArray → ByteArray)
    (hrun : ∀ env s, run env s = Prog.run (Prog.groupMachine p env) prog.code s) (SC WT : Array F)
    (block : Nat → Prog.View × Prog.Loads) (Q : Nat → Nat → F)
    (hblk : ∀ r0, (quotientTables (p := p) d l).B ∣ r0 →
      r0 + (quotientTables (p := p) d l).B ≤ 2 ^ (d + l) →
      ∃ (V : Array F) (cb cs : Nat) (L : Prog.LoadsF p), block r0 = (⟨encode V, cb, cs⟩, L.enc) ∧
        4 * V.size < USize.size ∧ L.Addr ∧
        (∀ ins ∈ prog.code, ins.InRange V cb cs L (quotientTables (p := p) d l).B prog.regs) ∧
        ∀ i < (quotientTables (p := p) d l).B, ∀ st0 : Prog.St F, st0.acc = (fun _ ↦ 0) →
          ∀ j < 4, (Prog.run (Prog.fieldMachine (Prog.blockCtx V cb cs L SC WT
            (quotientTables (p := p) d l).B i)) prog.code st0).acc j = Q (r0 + i) j) :
    quotientBlocks (quotientTables (p := p) d l) prog run SC WT block =
      Array.ofFn (n := 2 ^ (d + l)) fun r ↦ Ext4.smul ((batchInv (qZh d l) : Array F).getD
        (r.val % 2 ^ l) 0) ⟨Q ((bitRevPerm (d + l)).getD r 0) 0,
          Q ((bitRevPerm (d + l)).getD r 0) 1, Q ((bitRevPerm (d + l)).getD r 0) 2,
          Q ((bitRevPerm (d + l)).getD r 0) 3⟩ := by
  obtain ⟨hB0, -, hBn⟩ := tables_B (p := p) d l
  have hTd : (quotientTables (p := p) d l).degreeBits = d := rfl
  have hTl : (quotientTables (p := p) d l).logChunks = l := rfl
  have hTp : (quotientTables (p := p) d l).perm = bitRevPerm (d + l) := rfl
  have hTz : (quotientTables (p := p) d l).invZh = batchInv (qZh d l) := rfl
  unfold quotientBlocks
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Nat.add_sub_cancel_left]
  rw [hTd, hTl, hTp, hTz] at *
  generalize quotientTables (p := p) d l = T at hblk hB0 hBn ⊢
  rcases T with ⟨_, _, _, _, _, _, _, _, B, hS⟩
  dsimp only at hblk hB0 hBn ⊢
  -- Stored row `j`'s value.
  let g (j : Nat) : EF := Ext4.smul ((batchInv (qZh d l) : Array F).getD
    ((bitRevPerm (d + l)).getD j 0 % 2 ^ l) 0) ⟨Q j 0, Q j 1, Q j 2, Q j 3⟩
  show Array.map (fun r ↦ (parChunks _ _ _).getD r 0) (bitRevPerm (d + l)) = _
  rw [parChunks_eq_blocks (2 ^ (d + l) / B) (min (2 ^ (d + l) / B) 16) B _ g ?hf
    (Or.inl (Nat.lt_min.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.two_pow_pos _) hBn) hB0,
      by decide⟩)), Nat.div_mul_cancel hBn]
  case hf =>
    intro b0 nb hnb
    have hr0 (a : Nat) (ha1 : b0 ≤ a) (ha2 : a < b0 + nb) : a * B + B ≤ 2 ^ (d + l) := by
      rcases hnb with hnb | hnb
      · have := Nat.mul_le_mul_right B (show a + 1 ≤ 2 ^ (d + l) / B by omega)
        rw [Nat.succ_mul, Nat.div_mul_cancel hBn] at this; exact this
      · omega
    split
    · rename_i hc
      refine foldl_blocks_eq B b0 nb g (Prog.GEncoded (p := p) B prog.regs) _ ?_ _
        Array.emptyWithCapacity_eq _ (Prog.gEncoded_zeros B prog.regs)
      intro out st a hst ha1 ha2
      obtain ⟨V, cb, cs, L, hb, hV, hL, hcode, hQ⟩ := hblk (a * B) (Dvd.intro_left _ rfl)
        (hr0 a ha1 ha2)
      obtain ⟨hE, hw⟩ := Prog.groupBlock_acc prog.code prog.regs V cb cs L SC WT B hc.1 hc.2 hV hL
        hcode (fun i j ↦ Q (a * B + i) j) hQ st hst
      dsimp only
      rw [hb, hrun]
      refine ⟨hE, ?_⟩
      rw [CompStark.Stark.foldl_push_range']
      refine congrArg (out ++ ·) (congrArg Array.ofFn (funext fun i ↦ ?_))
      have h0 := hw 0 (by decide) i i.isLt
      have h1 := hw 1 (by decide) i i.isLt
      have h2 := hw 2 (by decide) i i.isLt
      have h3 := hw 3 (by decide) i i.isLt
      rw [Nat.mul_zero, Nat.zero_add] at h0
      rw [Nat.mul_one] at h1
      rw [Nat.mul_comm B 2] at h2
      rw [Nat.mul_comm B 3] at h3
      simp only [Nat.zero_add, g, word, h0, h1, h2, h3,
          CompPoly.CPolynomial.NTTFast.Packed.ofWord_val]
    · refine foldl_blocks_eq B b0 nb g (Prog.Encoded (p := p) B prog.regs) _ ?_ _
        Array.emptyWithCapacity_eq _ ⟨_, Prog.blockRel_zeros B prog.regs _⟩
      intro out st a hst ha1 ha2
      obtain ⟨V, cb, cs, L, hb, hV, hL, hcode, hQ⟩ := hblk (a * B) (Dvd.intro_left _ rfl)
        (hr0 a ha1 ha2)
      obtain ⟨hE, hw⟩ := Prog.runBlock_acc prog.code prog.regs V cb cs L SC WT B (4 * B) hS st
        hst hV hL hcode (fun i j ↦ Q (a * B + i) j) hQ
      dsimp only
      rw [hb]
      refine ⟨hE, ?_⟩
      rw [CompStark.Stark.foldl_push_range']
      refine congrArg (out ++ ·) (congrArg Array.ofFn (funext fun i ↦ ?_))
      simp only [Nat.zero_add, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
        hw 3 (by decide), g]
      rw [word_tab hS _ _ i.isLt, word_tab hS _ _ i.isLt, word_tab hS _ _ i.isLt,
        word_tab hS _ _ i.isLt]
  apply Array.ext (by rw [Array.size_map, Array.size_ofFn, size_bitRevPerm])
  intro r h1 h2
  rw [Array.size_ofFn] at h2
  have hP := bitRevPerm_getD_lt (d + l) r h2
  have hPr : (bitRevPerm (d + l))[r]'(by rw [size_bitRevPerm]; exact h2) =
      (bitRevPerm (d + l)).getD r 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [size_bitRevPerm]; exact h2),
      Option.getD_some]
  rw [Array.getElem_map, Array.getElem_ofFn, hPr, NTTFast.Packed.getD_ofFn_bounded _ _ hP]
  simp only [g, bitRevPerm_getD_getD _ _ h2]

/-- Constraints zipped with weights by index, accumulated: the program's accumulation order. -/
theorem foldl_zip_range' {α : Type} (ev : α → F) (f : Nat → List F) (j : Nat) :
    ∀ (cs : List α) (n : Nat) (x : F),
      (cs.zip ((List.range' n cs.length).map f)).foldl (fun x a ↦ x + ev a.1 * a.2.getD j 0) x =
        ((cs.zipIdx n).map fun (c, k) ↦ ev c * (f k).getD j 0).foldl (· + ·) x
  | [], _, _ => rfl
  | c :: cs, n, x => by
    rw [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons, List.foldl_cons,
      List.zipIdx_cons, List.map_cons, List.foldl_cons]
    exact foldl_zip_range' ev f j cs (n + 1) _

theorem foldl_add_congr {α : Type} (f g : α → F) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → ∀ x : F,
      (l.map f).foldl (· + ·) x = (l.map g).foldl (· + ·) x
  | [], _, _ => rfl
  | a :: l, h, x => by
    rw [List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons,
      h a List.mem_cons_self]
    exact foldl_add_congr f g l (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) _

/-! ### The loads of a block of stored rows -/

/-- Rows `r0, …, r0 + B - 1` of `m` transposed: column `c` at entries `c B, …`. -/
def blockT (m : Mat F) (r0 B : Nat) : Array F :=
  Array.ofFn (n := m.width * B) fun k ↦ m.values.getD ((r0 + k.val % B) * m.width + k.val / B) 0

theorem size_blockT (m : Mat F) (r0 B : Nat) : (blockT m r0 B).size = m.width * B :=
  Array.size_ofFn

theorem blockT_getD (m : Mat F) (r0 B c k : Nat) (hc : c < m.width) (hk : k < B) :
    (blockT m r0 B).getD (c * B + k) 0 = m.values.getD ((r0 + k) * m.width + c) 0 := by
  have hlt : c * B + k < m.width * B := by
    have := Nat.mul_le_mul_right B (show c + 1 ≤ m.width by omega)
    rw [Nat.succ_mul] at this; omega
  rw [blockT, NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
  have hd : (c * B + k) / B = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
  have hm : (c * B + k) % B = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [hd, hm]

/-- Appending `n` rows of column `c` of a packed matrix from row `r`, within one block. -/
theorem append_colAt {pm : PMat} {s : Mat F} (h : RM pm s) (r n c : Nat) (hn : 0 < n)
    (hblk : r % pm.rows + n ≤ pm.rows) (hr : r + n ≤ s.height) (hc : c < s.width) (X : Array F) :
    (pm.colAt c r).1.copySlice (4 * (pm.colAt c r).2) (encode X) (encode X).size (4 * n) =
      encode (X ++ Array.ofFn (n := n) fun k ↦ s.values.getD ((r + k.val) * s.width + c) 0) := by
  obtain ⟨A, e1, e2, -, e4⟩ := colAt_spec h r n c hblk hr hn hc
  rw [e1]
  have := CompPoly.PackedRepr.copySlice_encode A X (pm.colAt c r).2 n
  change (encode A).copySlice (4 * _) _ _ (4 * n) = _ at this
  rw [this]
  refine congrArg (fun Y ↦ encode (X ++ Y)) (Array.ext (by
    rw [Array.size_extract, Array.size_ofFn]; omega) fun k k1 k2 ↦ ?_)
  rw [Array.size_ofFn] at k2
  rw [Array.getElem_extract, Array.getElem_ofFn, ← e4 k k2, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The transposed rows of a block copied from a packed matrix's columns. -/
theorem block_rel {pm : PMat} {s : Mat F} (h : RM pm s) (r0 B : Nat) (hB : 0 < B)
    (hr : r0 + B ≤ s.height) : pm.block r0 B = encode (blockT s r0 B) := by
  have hw := h.width
  have hT (C : Nat) (hC : C ≤ s.width) : (blockT s r0 B).extract 0 (C * B) =
      Array.ofFn (n := C * B) fun k ↦ s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0 := by
    have hle : C * B ≤ s.width * B := Nat.mul_le_mul_right B hC
    refine Array.ext (by
      rw [Array.size_extract, size_blockT, Array.size_ofFn, Nat.min_eq_left hle,
        Nat.sub_zero]) fun k k1 k2 ↦ ?_
    rw [Array.size_ofFn] at k2
    have hk : k < s.width * B := Nat.lt_of_lt_of_le k2 hle
    rw [Array.getElem_extract, Array.getElem_ofFn, Array.getElem_eq_getD 0, blockT,
      NTTFast.Packed.getD_ofFn_bounded _ _ (by rw [Nat.zero_add]; exact hk)]
    simp only [Nat.zero_add]
  have hstep (C : Nat) (X : Array F) (hX : X = Array.ofFn (n := C * B) fun k ↦
      s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0) :
      X ++ (Array.ofFn (n := B) fun k ↦ s.values.getD ((r0 + k.val) * s.width + C) 0) =
      Array.ofFn (n := (C + 1) * B) fun k ↦
        s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0 := by
    subst hX
    refine Array.ext (by rw [Array.size_append, Array.size_ofFn, Array.size_ofFn,
      Array.size_ofFn, Nat.succ_mul]) fun k k1 k2 ↦ ?_
    rw [Array.getElem_append, Array.getElem_ofFn]
    split
    · rename_i hk
      rw [Array.getElem_ofFn]
    · rename_i hk
      rw [Array.size_ofFn] at hk
      rw [Array.getElem_ofFn]
      dsimp only
      rw [Array.size_ofFn] at k2
      have h1 : k / B = C := Nat.div_eq_of_lt_le (Nat.le_of_not_lt hk) k2
      have h2 : k % B = k - C * B := by
        rw [Nat.mod_eq_sub_mul_div, h1, Nat.mul_comm]
      rw [Array.size_ofFn, h1, h2]
  unfold PMat.block
  rw [show ByteArray.emptyWithCapacity (4 * (pm.width * B)) = encode (#[] : Array F) from rfl]
  dsimp only
  rw [CompStark.Merkle.Packed.foldRange_eq, CompStark.Merkle.Packed.foldRange_eq, hw]
  split
  · rename_i hblk
    have key : ∀ C ≤ s.width, (List.range C).foldl (fun out c ↦
        (pm.colAt c r0).1.copySlice (4 * (pm.colAt c r0).2) out out.size (4 * B))
        (encode (#[] : Array F)) = encode ((blockT s r0 B).extract 0 (C * B)) := by
      intro C hC
      induction C with
      | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul, Array.extract_zero]
      | succ C ih =>
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
          append_colAt h r0 B C hB hblk hr (by omega), hT C (by omega), hT (C + 1) hC,
          hstep C _ rfl]
    rw [key s.width le_rfl, show s.width * B = (blockT s r0 B).size by rw [size_blockT],
      Array.extract_size]
  · have key : ∀ C ≤ s.width, (List.range C).foldl (fun out c ↦
        CompStark.Merkle.Packed.foldRange (fun out k ↦ (pm.colAt c (r0 + k)).1.copySlice
          (4 * (pm.colAt c (r0 + k)).2) out out.size 4) B 0 out)
        (encode (#[] : Array F)) = encode ((blockT s r0 B).extract 0 (C * B)) := by
      intro C hC
      induction C with
      | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul, Array.extract_zero]
      | succ C ih =>
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
          CompStark.Merkle.Packed.foldRange_eq, hT C (by omega), hT (C + 1) hC,
          ← hstep C _ rfl]
        have inner : ∀ K ≤ B, (List.range K).foldl (fun out k ↦ (pm.colAt C (r0 + k)).1.copySlice
            (4 * (pm.colAt C (r0 + k)).2) out out.size 4) (encode (Array.ofFn (n := C * B)
              fun k ↦ s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0)) =
            encode ((Array.ofFn (n := C * B) fun k ↦
              s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0) ++
              Array.ofFn (n := K) fun k ↦ s.values.getD ((r0 + k.val) * s.width + C) 0) := by
          intro K hK
          induction K with
          | zero => rw [List.range_zero, List.foldl_nil, Array.ofFn_zero, Array.append_empty]
          | succ K ihK =>
            rw [List.range_succ, List.foldl_append, ihK (by omega), List.foldl_cons,
              List.foldl_nil]
            have e := append_colAt h (r0 + K) 1 C (by decide)
              (by have := Nat.mod_lt (r0 + K) h.pos; omega) (by omega) (by omega)
              ((Array.ofFn (n := C * B) fun k ↦
                s.values.getD ((r0 + k.val % B) * s.width + k.val / B) 0) ++
                Array.ofFn (n := K) fun k ↦ s.values.getD ((r0 + k.val) * s.width + C) 0)
            rw [Nat.mul_one] at e
            rw [e, Array.append_assoc]
            congr 2
            refine Array.ext (by rw [Array.size_append, Array.size_ofFn, Array.size_ofFn,
              Array.size_ofFn]) fun k k1 k2 ↦ ?_
            rw [Array.getElem_append, Array.getElem_ofFn]
            split
            · rw [Array.getElem_ofFn]
            · rename_i hk
              rw [Array.size_ofFn] at hk k2
              rw [Array.getElem_ofFn]
              dsimp only
              rw [show k = K by omega, Array.size_ofFn, Nat.sub_self, Nat.add_zero]
        exact inner B le_rfl
    rw [key s.width le_rfl, show s.width * B = (blockT s r0 B).size by rw [size_blockT],
      Array.extract_size]

theorem transposeRows_blockT (m : Mat F) (r0 B : Nat) (hM : (r0 + B) * m.width ≤ m.values.size)
    (hs : 4 * m.values.size < USize.size) :
    NTTFast.Packed.Native.transposeRows (encode m.values) m.width r0 B =
      encode (blockT m r0 B) :=
  transposeRows_encode m.values m.width r0 B hM hs

/-- Entry `(j, c)` of a matrix in the extension's bit-reversed order is the stored row `j`'s. -/
theorem permuteRows_bitRev [Mont32BaseField p] (m : Mat F) (d l j c : Nat) (hj : j < 2 ^ (d + l))
    (hc : c < m.width) :
    (permuteRows m (bitRevPerm (d + l))).getD ((bitRevPerm (d + l)).getD j 0 * m.width + c) 0 =
      m.values.getD (j * m.width + c) 0 := by
  rw [permuteRows_getD m _ _ c (by rw [size_bitRevPerm]; exact bitRevPerm_getD_lt _ _ hj) hc,
    bitRevPerm_getD_getD _ _ hj]

/-- The next row of the stored row `j` is stored at `next[j]`. -/
theorem permuteRows_bitRev_next [Mont32BaseField p] (m : Mat F) (d l j c : Nat)
    (hj : j < 2 ^ (d + l)) (hc : c < m.width) :
    (permuteRows m (bitRevPerm (d + l))).getD
      ((((bitRevPerm (d + l)).getD j 0 + 2 ^ l) % 2 ^ (d + l)) * m.width + c) 0 =
      m.values.getD ((quotientTables (p := p) d l).next.getD j 0 * m.width + c) 0 := by
  rw [permuteRows_getD m _ _ c (by rw [size_bitRevPerm]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    hc, tables_next d l j hj]

/-- A table of the quotient domain in the extension's bit-reversed order. -/
def selT (d l : Nat) (t : Array F) : Array F := (bitRevPerm (d + l)).map fun i ↦ t.getD i 0

theorem size_selT (d l : Nat) (t : Array F) : (selT d l t).size = 2 ^ (d + l) := by
  rw [selT, Array.size_map, size_bitRevPerm]

theorem selT_getD (d l : Nat) (t : Array F) (k : Nat) (hk : k < 2 ^ (d + l)) :
    (selT d l t).getD k 0 = t.getD ((bitRevPerm (d + l)).getD k 0) 0 :=
  getD_map_lt _ _ k (by rw [size_bitRevPerm]; exact hk) 0 0

/-- Periodic columns in the extension's bit-reversed order. -/
def perT (d l : Nat) (pl : List (Array F)) : Array (Array F) :=
  (pl.map fun tab ↦ (bitRevPerm (d + l)).map fun r ↦ periodicRow tab r).toArray

theorem perT_getD (d l : Nat) (pl : List (Array F)) (j k : Nat) (hk : k < 2 ^ (d + l)) :
    ((perT d l pl).getD j #[]).getD k 0 =
      periodicRow (pl.getD j #[]) ((bitRevPerm (d + l)).getD k 0) := by
  by_cases hj : j < pl.length
  · have hPj : (perT d l pl).getD j #[] = (bitRevPerm (d + l)).map fun r ↦
        periodicRow pl[j] r := by
      simp only [perT, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    rw [hPj, getD_map_lt _ _ _ (by rw [size_bitRevPerm]; exact hk) 0 0,
      List.getD_eq_getElem _ _ hj]
  · have hPj : (perT d l pl).getD j #[] = #[] := by
      simp only [perT, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
        List.getElem?_eq_none (by omega : pl.length ≤ j), Option.map_none, Option.getD_none]
    rw [hPj, List.getD_eq_default _ _ (by omega)]
    simp only [periodicRow, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_nil, Option.getD_none]

theorem mem_perT {d l : Nat} {pl : List (Array F)} {c : Array F} (hc : c ∈ perT d l pl) :
    c.size = 2 ^ (d + l) := by
  simp only [perT, List.mem_toArray, List.mem_map] at hc
  obtain ⟨_, -, rfl⟩ := hc
  rw [Array.size_map, size_bitRevPerm]

theorem periodicWords_eq [Mont32BaseField p] (A : Air F) (d l : Nat) :
    periodicWords (quotientTables (p := p) d l) A =
      (perT d l (A.periodic.map fun col ↦ periodicOnQuotient col d l)).map encode := by
  unfold periodicWords
  apply Array.toList_inj.mp
  simp only [Array.toList_map, perT, List.map_map]
  exact List.map_congr_left fun col _ ↦ NTTFast.Packed.Native.encodeFields_eq _

/-- The loads of the block of `B` stored rows from `r0`: the trace `s`, the preprocessed trace
`sp` and the permutation trace `rs` with the next rows `nx`, the periodic columns `pl` and the
selectors, in the extension's bit-reversed order. -/
def qLoads [Mont32BaseField p] (d l : Nat) (s sp rs : Mat F) (R Rp Rq : Nat)
    (pl : List (Array F)) (nx : Array Nat) (r0 B : Nat) :
    Prog.LoadsF p :=
  ⟨⟨colBlocks s R, s.width, R⟩, ⟨colBlocks sp Rp, sp.width, Rp⟩, blockT sp r0 B,
    ⟨colBlocks rs Rq, rs.width, Rq⟩, blockT rs r0 B, r0, nx, seqRows nx r0 B, perT d l pl,
    selT d l (qFirst d l), selT d l (qLast d l), selT d l (qTrans d l)⟩

/-- A matrix of `H` rows, at least the quotient domain's, addressable. -/
def QShape (d l H : Nat) (m : Mat F) : Prop :=
  m.values.size = m.width * H ∧ 2 ^ (d + l) ≤ H ∧ 4 * m.values.size < USize.size

theorem QShape.block {d l H : Nat} {m : Mat F} (h : QShape d l H m) {r0 B : Nat}
    (hr0 : r0 + B ≤ 2 ^ (d + l)) : (r0 + B) * m.width ≤ m.values.size := by
  rw [h.1, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (le_trans hr0 h.2.1)

theorem QShape.blockT {d l H : Nat} {m : Mat F} (h : QShape d l H m) {r0 B : Nat}
    (hr0 : r0 + B ≤ 2 ^ (d + l)) : 4 * (blockT m r0 B).size < USize.size := by
  rw [size_blockT]
  have h1 := h.block hr0
  have h2 : m.width * B ≤ (r0 + B) * m.width := by
    rw [Nat.mul_comm (r0 + B)]; exact Nat.mul_le_mul_left _ (by omega)
  have := h.2.2
  omega

theorem QShape.row {d l H : Nat} {m : Mat F} (h : QShape d l H m) {j c : Nat}
    (hj : j < 2 ^ (d + l)) (hc : c < m.width) : j * m.width + c < m.values.size := by
  have : (j + 1) * m.width ≤ m.values.size := by
    rw [h.1, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by have := h.2.1; omega)
  rw [Nat.succ_mul] at this; omega

theorem qLoads_addr [Mont32BaseField p] {d l H : Nat} {s sp rs : Mat F} {R Rp Rq : Nat}
    (hR : RowsOk s R) (hRp : RowsOk sp Rp) (hRq : RowsOk rs Rq)
    (hsp : QShape d l H sp)
    (hrs : QShape d l H rs) (pl : List (Array F)) (nx : Array Nat) {r0 B : Nat}
    (hr0 : r0 + B ≤ 2 ^ (d + l)) (hn : 4 * 2 ^ (d + l) < USize.size) :
    (qLoads (p := p) d l s sp rs R Rp Rq pl nx r0 B).Addr :=
  ⟨colsF_addr hR, colsF_addr hRp, hsp.blockT hr0, colsF_addr hRq, hrs.blockT hr0,
    fun c hc ↦ by rw [mem_perT hc]; exact hn,
    by show 4 * (selT d l _).size < _; rw [size_selT]; exact hn,
    by show 4 * (selT d l _).size < _; rw [size_selT]; exact hn,
    by show 4 * (selT d l _).size < _; rw [size_selT]; exact hn⟩

theorem qLoads_inRange [Mont32BaseField p] {d l H : Nat} {s sp rs : Mat F} {R Rp Rq : Nat}
    (hR : RowsOk s R) (hRp : RowsOk sp Rp) (hRq : RowsOk rs Rq)
    (hs : QShape d l H s) (hsp : QShape d l H sp) (hrs : QShape d l H rs)
    (hHs : s.height = H) (hHp : sp.height = H) (hHq : rs.height = H)
    (pl : List (Array F)) {r0 B : Nat} (hr0 : r0 + B ≤ 2 ^ (d + l)) (src : Prog.Src)
    (h : Prog.Src.Below s.width sp.width sp.width rs.width src) :
    (qLoads (p := p) d l s sp rs R Rp Rq pl (quotientTables (p := p) d l).next r0 B).InRange B
      src := by
  have hnx (k : Nat) (hk : k < B) :
      (quotientTables (p := p) d l).next.getD (r0 + k) 0 < 2 ^ (d + l) := by
    rw [tables_next _ _ _ (by omega)]
    exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  have hcolB (m : Mat F) (c : Nat) (hc : c < m.width) : c * B + B ≤ (blockT m r0 B).size := by
    rw [size_blockT]
    have := Nat.mul_le_mul_right B (show c + 1 ≤ m.width by omega)
    rw [Nat.succ_mul] at this; omega
  cases src with
  | next c =>
    refine ⟨fun k hk ↦ ?_, ?_⟩
    have := hnx k hk
    have := hs.2.1
    exact colsF_has hR ((quotientTables (p := p) d l).next.getD (r0 + k) 0) c (by omega) h
    exact seqRows_spec
  | prepCur c => exact hcolB sp c h
  | prepNext c =>
    refine ⟨fun k hk ↦ ?_, ?_⟩
    have := hnx k hk
    have := hsp.2.1
    exact colsF_has hRp ((quotientTables (p := p) d l).next.getD (r0 + k) 0) c (by omega) h
    exact seqRows_spec
  | permCur c => exact hcolB rs c h
  | permNext c =>
    refine ⟨fun k hk ↦ ?_, ?_⟩
    have := hnx k hk
    have := hrs.2.1
    exact colsF_has hRq ((quotientTables (p := p) d l).next.getD (r0 + k) 0) c (by omega) h
    exact seqRows_spec
  | periodic j =>
    intro hj
    have hj' : j < (perT d l pl).size := hj
    show r0 + B ≤ ((perT d l pl).getD j #[]).size
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj', Option.getD_some,
      mem_perT (Array.getElem_mem hj')]
    exact hr0
  | isFirstRow => show r0 + B ≤ (selT d l _).size; rw [size_selT]; exact hr0
  | isLastRow => show r0 + B ≤ (selT d l _).size; rw [size_selT]; exact hr0
  | isTransition => show r0 + B ≤ (selT d l _).size; rw [size_selT]; exact hr0

/-- A block row's base environment (`Prog.blockCtx` on `qLoads`) is the specification's on the
natural row `perm[r0 + i]` at the columns below the widths and the periodic columns and
selectors. -/
theorem qLoads_env [Mont32BaseField p] (d l : Nat) (s sp rs : Mat F) (R Rp Rq : Nat)
    (hR : RowsOk s R) (hRp : RowsOk sp Rp) (hs : 2 ^ (d + l) ≤ s.height)
    (hsp : 2 ^ (d + l) ≤ sp.height) (pl : List (Array F))
    (pis : List F) (SC WT : Array F) (r0 B i : Nat) (hi : i < B) (hri : r0 + i < 2 ^ (d + l)) :
    (∀ c < s.width, (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.cur c =
      (rowEnv (Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l))))
        (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
        (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l)
        ((bitRevPerm (d + l)).getD (r0 + i) 0)).cur c) ∧
    (∀ c < s.width, (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.next c =
      (rowEnv (Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l))))
        (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
        (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l)
        ((bitRevPerm (d + l)).getD (r0 + i) 0)).next c) ∧
    (∀ c < sp.width, (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.prepCur c =
      (rowEnv (Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l))))
        (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
        (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l)
        ((bitRevPerm (d + l)).getD (r0 + i) 0)).prepCur c) ∧
    (∀ c < sp.width, (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.prepNext c =
      (rowEnv (Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l))))
        (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
        (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l)
        ((bitRevPerm (d + l)).getD (r0 + i) 0)).prepNext c) ∧
    (∀ j, (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.periodic j =
      (rowEnv (Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l))))
        (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
        (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l)
        ((bitRevPerm (d + l)).getD (r0 + i) 0)).periodic j) ∧
    (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.isFirstRow =
      (qFirst d l : Array F).getD ((bitRevPerm (d + l)).getD (r0 + i) 0) 0 ∧
    (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.isLastRow =
      (qLast d l : Array F).getD ((bitRevPerm (d + l)).getD (r0 + i) 0) 0 ∧
    (Prog.blockCtx (blockT s r0 B) 0 B (qLoads (p := p) d l s sp rs R Rp Rq pl
      (quotientTables (p := p) d l).next r0 B) SC WT B i).env.isTransition =
      (qTrans d l : Array F).getD ((bitRevPerm (d + l)).getD (r0 + i) 0) 0 := by
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, fun c hc ↦ ?_, fun c hc ↦ ?_, fun j ↦ ?_,
    selT_getD d l (qFirst d l) _ hri, selT_getD d l (qLast d l) _ hri,
    selT_getD d l (qTrans d l) _ hri⟩
  · show (blockT s r0 B).getD (0 + c * B + i) 0 = (permuteRows s _).getD _ 0
    rw [Nat.zero_add, blockT_getD s r0 B c i hc hi]
    exact (permuteRows_bitRev s d l _ c hri hc).symm
  · have hn : (quotientTables (p := p) d l).next.getD (r0 + i) 0 < 2 ^ (d + l) := by
      rw [tables_next _ _ _ hri]
      exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    show (⟨colBlocks s R, s.width, R⟩ : Prog.ColsF p).at
      ((quotientTables (p := p) d l).next.getD (r0 + i) 0) c = _
    rw [colsF_at hR ((quotientTables (p := p) d l).next.getD (r0 + i) 0) c (by omega) hc]
    exact (permuteRows_bitRev_next s d l _ c hri hc).symm
  · show (blockT sp r0 B).getD (c * B + i) 0 = (permuteRows sp _).getD _ 0
    rw [blockT_getD sp r0 B c i hc hi]
    exact (permuteRows_bitRev sp d l _ c hri hc).symm
  · have hn : (quotientTables (p := p) d l).next.getD (r0 + i) 0 < 2 ^ (d + l) := by
      rw [tables_next _ _ _ hri]
      exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    show (⟨colBlocks sp Rp, sp.width, Rp⟩ : Prog.ColsF p).at
      ((quotientTables (p := p) d l).next.getD (r0 + i) 0) c = _
    rw [colsF_at hRp ((quotientTables (p := p) d l).next.getD (r0 + i) 0) c (by omega) hc]
    exact (permuteRows_bitRev_next sp d l _ c hri hc).symm
  · exact perT_getD d l pl j _ hri

/-- The preprocessed trace the quotient reads: the one given, or none of `height` rows. -/
abbrev prepOrEmpty (ps : Option (Mat F)) (height : Nat) : Mat F := ps.getD ⟨0, height, #[]⟩

/-- The fast quotient is the specification's on related extensions of the trace and the
preprocessed trace. -/
theorem quotientWith_rel [Mont32BaseField p] [Binomial4 p] (ks : List (CheckedKernel p))
    (A : Air F) (pis : List F) (d l : Nat)
    (alpha : EF) {ext : PMat} {s : Mat F} {prep : Option PMat} {ps : Option (Mat F)}
    (h : RM ext s) (hs : MatOk s) (hh : 2 ^ (d + l) ≤ s.height) (hp : Option.Rel RM prep ps)
    (hps : ∀ q ∈ ps, MatOk q ∧ q.height = s.height)
    (hc : ∀ c ∈ A.constraints, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0)) :
    quotientWith ks (quotientTables
        (p := p) d l) A pis ext prep alpha = quotientOfLde A pis d l s ps alpha := by
  have hw := h.width
  obtain ⟨hw0, -, hvs', hadd⟩ := hs
  have hus : 4 * s.values.size < USize.size := by
    unfold Addressable at hadd
    rw [hvs']
    omega
  have hpw : (ps.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by cases ps <;> rfl
  have hpw' : (prep.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by
    cases hp with
    | none => rfl
    | @some a q hr => exact hr.1
  have hpm : RowsOk (prepOrEmpty ps s.height) (prep.getD PMat.empty).rows ∧
      (prep.getD PMat.empty).toCols = (⟨colBlocks (prepOrEmpty ps s.height)
        (prep.getD PMat.empty).rows, (prepOrEmpty ps s.height).width,
        (prep.getD PMat.empty).rows⟩ : Prog.ColsF p).enc ∧
      ∀ r0 B, 0 < B → r0 + B ≤ s.height → (prep.getD PMat.empty).block r0 B =
        encode (blockT (prepOrEmpty ps s.height) r0 B) := by
    cases hp with
    | none =>
      refine ⟨⟨Nat.one_pos, Nat.mod_one _, by
        show 4 * 1 < USize.size; have := USize.le_size; omega⟩,
        empty_toCols s.height, fun r0 B _ _ ↦ ?_⟩
      show PMat.empty.block r0 B = encode (blockT (⟨0, s.height, #[]⟩ : Mat F) r0 B)
      rw [Array.eq_empty_of_size_eq_zero (xs := blockT _ r0 B) (by rw [size_blockT,
        Nat.zero_mul])]
      unfold PMat.block
      simp only [PMat.empty, Nat.zero_mul, Nat.mul_zero]
      split <;> rfl
    | @some a q hr =>
      obtain ⟨-, hqh⟩ := hps q rfl
      refine ⟨hr.rowsOk, toCols_rel hr, fun r0 B hB hrB ↦ block_rel hr r0 B hB (by
        show r0 + B ≤ q.height; rw [hqh]; exact hrB)⟩
  have hspv : (prepOrEmpty ps s.height).values.size =
      (prepOrEmpty ps s.height).width * s.height := by
    cases hp with
    | none => show (#[] : Array F).size = 0 * s.height; rw [Nat.zero_mul]; rfl
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, -⟩, hqh⟩ := hps q rfl
      show q.values.size = q.width * s.height
      rw [hq, hqh]
  have husp : 4 * (prepOrEmpty ps s.height).values.size < USize.size := by
    cases hp with
    | none => show 4 * 0 < USize.size; have := USize.le_size; omega
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, hqa⟩, -⟩ := hps q rfl
      unfold Addressable at hqa
      show 4 * q.values.size < USize.size
      rw [hq]
      omega
  have hpq : (ps.map fun m ↦ Mat.ofValues m.width (2 ^ (d + l))
        (permuteRows m (bitRevPerm (d + l)))).getD (Mat.ofValues 0 (2 ^ (d + l)) #[]) =
      Mat.ofValues (prepOrEmpty ps s.height).width (2 ^ (d + l))
        (permuteRows (prepOrEmpty ps s.height) (bitRevPerm (d + l))) := by
    cases ps with
    | none =>
      show Mat.ofValues 0 (2 ^ (d + l)) #[] = Mat.ofValues 0 (2 ^ (d + l)) (permuteRows _ _)
      rw [Array.eq_empty_of_size_eq_zero (xs := permuteRows _ _)
        (by rw [permuteRows_eq, Array.size_ofFn]; rfl)]
    | some q => rfl
  have hsph : (prepOrEmpty ps s.height).height = s.height := by
    cases ps with
    | none => rfl
    | some q => exact (hps q rfl).2
  generalize prepOrEmpty ps s.height = sp at hpw hpw' hpm hspv husp hpq hsph
  rw [hpw] at hc
  have hn : 2 ^ (d + l) ≤ s.values.size := by
    rw [hvs']; exact le_trans hh (Nat.le_mul_of_pos_left _ hw0)
  have hnU : 4 * 2 ^ (d + l) < USize.size := by omega
  -- The weights and the periodic columns as arrays.
  let K := A.constraints.length
  let WT : Array F := Array.ofFn (n := 4 * K) fun i ↦
    (Ext.coeffs (Ext.pow alpha (K - 1 - i.val / 4))).getD (i.val % 4) 0
  have hWT : weightCoords alpha K = WT := weightCoords_eq alpha K
  have hsS : QShape d l s.height s := ⟨hvs', hh, hus⟩
  have hspS : QShape d l s.height sp := ⟨hspv, hh, husp⟩
  have hrsS : QShape d l s.height (⟨0, s.height, #[]⟩ : Mat F) :=
    ⟨by show 0 = 0 * s.height; rw [Nat.zero_mul], hh, by show 4 * 0 < USize.size; omega⟩
  unfold quotientOfLde
  dsimp only
  rw [hpq, quotientValues_eq]
  unfold quotientWith
  rw [periodicWords_eq]
  generalize A.periodic.map (fun col ↦ periodicOnQuotient col d l) = pl
  -- Stored row `j`'s environment and accumulation.
  let tq := Mat.ofValues s.width (2 ^ (d + l)) (permuteRows s (bitRevPerm (d + l)))
  let pq := Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))
  let E (j : Nat) : Expr.Env F F := rowEnv tq pq pl (2 ^ (d + l)) (2 ^ l) pis (qFirst d l)
    (qLast d l) (qTrans d l) ((bitRevPerm (d + l)).getD j 0)
  let Q (j k : Nat) : F := rowAcc (weighted A alpha) (fun c ↦ c.eval (E j)) k 0
  dsimp only
  rw [progRun_fst, hWT, quotientBlocks_eq d l _ _
      (progRun_snd ks A.constraints) pis.toArray WT _ Q
    ?hblk]
  case hblk =>
    intro r0 hdvd hr0
    obtain ⟨hB0, -, -⟩ := tables_B (p := p) d l
    rw [tables_first, tables_last, tables_trans]
    have hrs0 : blockT (⟨0, s.height, #[]⟩ : Mat F) r0 (quotientTables (p := p) d l).B = #[] :=
      Array.eq_empty_of_size_eq_zero (by rw [size_blockT]; exact Nat.zero_mul _)
    generalize (quotientTables (p := p) d l).B = B at hdvd hr0 hB0 hrs0 ⊢
    have hrs1 : RowsOk (⟨0, s.height, #[]⟩ : Mat F) 1 :=
      ⟨Nat.one_pos, Nat.mod_one _, by have := USize.le_size; omega⟩
    refine ⟨blockT s r0 B, 0, B, qLoads d l s sp (⟨0, s.height, #[]⟩ : Mat F) ext.rows
      (prep.getD PMat.empty).rows 1 pl (quotientTables (p := p) d l).next r0 B, ?_,
      hsS.blockT hr0,
      qLoads_addr h.rowsOk hpm.1 hrs1 hspS hrsS pl _ hr0 hnU, fun ins hins ↦ ?_,
      fun i hi st0 hst0 j hj ↦ ?_⟩
    · rw [block_rel h r0 B hB0 (by omega), hpm.2.2 r0 B hB0 (by omega), toCols_rel h,
        hpm.2.1, empty_toCols (p := p) s.height]
      simp only [Prog.LoadsF.enc, qLoads, hrs0]
      rfl
    · refine Prog.Instr.inRange_of (cq := (· < s.width))
        (lq := Prog.Src.Below s.width sp.width sp.width 0) (fun c hc ↦ ?_)
        (qLoads_inRange h.rowsOk hpm.1 hrs1 hsS hspS hrsS rfl hsph rfl pl hr0)
        ins ((Prog.compile_run A.constraints ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ _ ↦ 0⟩
          ⟨fun _ ↦ 0, fun _ ↦ 0⟩).2 ins hins)
        (Prog.compile_leafOk A.constraints s.width s.width sp.width sp.width 0 hc ins hins)
      rw [size_blockT, Nat.zero_add]
      have := Nat.mul_le_mul_right B (show c + 1 ≤ s.width by exact hc)
      rw [Nat.succ_mul] at this; exact this
    · have hri : r0 + i < 2 ^ (d + l) := by omega
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := qLoads_env d l s sp (⟨0, s.height, #[]⟩ : Mat F)
        ext.rows (prep.getD PMat.empty).rows 1 h.rowsOk hpm.1 hh (by rw [hsph]; exact hh) pl pis
        pis.toArray WT r0 B i hi hri
      rw [(Prog.compile_run A.constraints _ st0).1, hst0]
      dsimp only
      simp only [Q, rowAcc, weighted, List.range_eq_range', foldl_zip_range']
      refine foldl_add_congr _ _ _ (fun a ha ↦ ?_) 0
      obtain ⟨c, k⟩ := a
      have hcm : c ∈ A.constraints := List.fst_mem_of_mem_zipIdx ha
      have hk : k < K := List.snd_lt_of_mem_zipIdx ha
      dsimp only
      congr 1
      · exact Expr.eval_hom (R := F) (S := F) id (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
          s.width s.width sp.width sp.width _ (E (r0 + i)) e1 e2 e3 e4 e5
          (fun jj ↦ show pis.toArray.getD jj 0 = pis.getD jj 0 by
            rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD])
          (fun _ ↦ rfl) e6 e7 e8 c (hc c hcm)
      · show WT.getD (4 * k + j) 0 = _
        rw [NTTFast.Packed.getD_ofFn_bounded _ _ (by omega)]
        have h1 : (4 * k + j) / 4 = k := by omega
        have h2 : (4 * k + j) % 4 = j := by omega
        simp only [h1, h2]
        rfl
  refine congrArg Array.ofFn (funext fun r ↦ ?_)
  unfold quotientRow
  simp only [Q, E, bitRevPerm_getD_getD _ _ r.isLt]
  rfl

end CompStark.Stark.Fast
