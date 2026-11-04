/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgFused
public import CompStark.Stark.Fast.ProgGroup

/-! # Fused chunks compute the field's values

A program's accumulations, recorded one per slot (`slotMachine`), give its accumulators: each
accumulator is the slots times their weights (`run_slots`).
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (splice lit16 size_encode_fields array_eq_of_getD)
open CompPoly.CPolynomial.NTTFast.Packed.Native (Buf write16U)
open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.Words (tab size_tab tab_congr getD_tab)

variable {F : Type}

/-- A row's registers, its accumulations recorded in slots, and the next slot. -/
structure SlotSt (F : Type) where
  reg : Nat → F
  slot : Nat → F
  t : Nat

/-- An operand's value on a row with registers `reg`. -/
def Opd.valR (ctx : Ctx F) (reg : Nat → F) : Opd F → F
  | .reg r => reg r
  | .cur c => ctx.cur c
  | .const x => x

/-- A program on a row, its accumulations recorded in slots instead of accumulated. -/
def slotMachine [Field F] (ctx : Ctx F) : Machine F (SlotSt F) where
  load d src s := { s with reg := Function.update s.reg d (ctx.src src) }
  scalar d i s := { s with reg := Function.update s.reg d (ctx.scalar i) }
  bin o d a b s :=
    { s with reg := Function.update s.reg d (o.eval (a.valR ctx s.reg) (b.valR ctx s.reg)) }
  acc a _ s := { s with slot := Function.update s.slot s.t (a.valR ctx s.reg), t := s.t + 1 }

theorem Opd.valR_eq [Zero F] (ctx : Ctx F) (st : St F) (a : Opd F) :
    a.valR ctx st.reg = a.val ctx st := by
  cases a <;> rfl

/-- **Accumulations as slots**: a program's registers are the slot machine's, its slots below the
first are kept, and every accumulator gains the new slots times their weights. -/
theorem run_slots [Field F] (ctx : Ctx F) :
    ∀ (code : List (Instr F)) (st : St F) (ss : SlotSt F), ss.reg = st.reg →
      (code.foldl (fun s i ↦ i.exec (slotMachine ctx) s) ss).reg =
          (code.foldl (fun s i ↦ i.exec (fieldMachine ctx) s) st).reg ∧
        (code.foldl (fun s i ↦ i.exec (slotMachine ctx) s) ss).t =
          ss.t + (accWeights code).length ∧
        (∀ i < ss.t, (code.foldl (fun s i ↦ i.exec (slotMachine ctx) s) ss).slot i = ss.slot i) ∧
        ∀ j, (code.foldl (fun s i ↦ i.exec (fieldMachine ctx) s) st).acc j =
          st.acc j + ((accWeights code).zipIdx.map fun (w, i) ↦
            (code.foldl (fun s i ↦ i.exec (slotMachine ctx) s) ss).slot (ss.t + i) *
              ctx.weight w j).sum
  | [], st, ss, h => by
    refine ⟨h, rfl, fun _ _ ↦ rfl, fun _ ↦ ?_⟩
    simp only [List.foldl_nil, accWeights, List.zipIdx_nil, List.map_nil, List.sum_nil, add_zero]
  | ins :: code, st, ss, h => by
    simp only [List.foldl_cons]
    cases ins with
    | load d src =>
      obtain ⟨h1, h2, h3, h4⟩ := run_slots ctx code _ _ (show (Instr.exec (slotMachine ctx)
        (Instr.load d src) ss).reg = (Instr.exec (fieldMachine ctx) (Instr.load d src) st).reg by
          simp only [Instr.exec, slotMachine, fieldMachine, h])
      exact ⟨h1, h2, h3, h4⟩
    | scalar d i =>
      obtain ⟨h1, h2, h3, h4⟩ := run_slots ctx code _ _ (show (Instr.exec (slotMachine ctx)
        (Instr.scalar d i) ss).reg = (Instr.exec (fieldMachine ctx) (Instr.scalar d i) st).reg by
          simp only [Instr.exec, slotMachine, fieldMachine, h])
      exact ⟨h1, h2, h3, h4⟩
    | bin o d a b =>
      obtain ⟨h1, h2, h3, h4⟩ := run_slots ctx code _ _ (show (Instr.exec (slotMachine ctx)
        (Instr.bin o d a b) ss).reg = (Instr.exec (fieldMachine ctx) (Instr.bin o d a b) st).reg by
          simp only [Instr.exec, slotMachine, fieldMachine, h, Opd.valR_eq])
      exact ⟨h1, h2, h3, h4⟩
    | acc a w =>
      obtain ⟨h1, h2, h3, h4⟩ := run_slots ctx code _ _ (show (Instr.exec (slotMachine ctx)
        (Instr.acc a w) ss).reg = (Instr.exec (fieldMachine ctx) (Instr.acc a w) st).reg by
          simp only [Instr.exec, slotMachine, fieldMachine, h])
      have ht : (Instr.exec (slotMachine ctx) (Instr.acc a w) ss).t = ss.t + 1 := rfl
      have hs0 := h3 ss.t (by rw [ht]; omega)
      refine ⟨h1, by rw [h2, ht, accWeights, List.length_cons]; omega, fun i hi ↦ ?_, fun j ↦ ?_⟩
      · rw [h3 i (by rw [ht]; omega)]
        show Function.update ss.slot ss.t _ i = _
        rw [Function.update_of_ne (by omega)]
      · rw [h4 j, accWeights, List.zipIdx_cons, List.map_cons, List.sum_cons, ht]
        simp only [Nat.add_zero, Nat.zero_add]
        rw [hs0]
        show st.acc j + a.val ctx st * ctx.weight w j + _ =
          st.acc j + (Function.update ss.slot ss.t (a.valR ctx ss.reg) ss.t * ctx.weight w j + _)
        rw [Function.update_self, h, Opd.valR_eq, add_assoc]
        congr 2
        rw [List.zipIdx_eq_map_add (l := accWeights code) (i := 1)]
        simp only [List.map_map]
        refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
        simp only [Function.comp_apply]
        rw [Nat.add_assoc, Nat.add_comm 1]

/-! ### Words of a fused chunk's buffer -/

section Words
variable {p : ℕ} [Mont32Field p] {env : GroupEnv} {n R C : Nat}

local notation "FF" => FastField p

/-- Sixteen words hold the field elements `G 0, …, G 15`. -/
def Lanes.Is (L : Lanes) (G : Nat → FF) : Prop := ∀ k < 16, L.get k = (G k).val

theorem Lanes.is_mk (G : Nat → FF) :
    Lanes.Is ⟨(G 0).val, (G 1).val, (G 2).val, (G 3).val, (G 4).val, (G 5).val, (G 6).val,
      (G 7).val, (G 8).val, (G 9).val, (G 10).val, (G 11).val, (G 12).val, (G 13).val,
      (G 14).val, (G 15).val⟩ G := by
  intro k hk
  interval_cases k <;> rfl

theorem Lanes.is_rep (x : FF) : (Lanes.rep x.val).Is fun _ ↦ x := by
  intro k hk
  interval_cases k <;> rfl

theorem Lanes.is_zip (f : UInt32 → UInt32 → UInt32) (g : FF → FF → FF)
    (hf : ∀ x y : FF, f x.val y.val = (g x y).val) {A B : Lanes} {GA GB : Nat → FF}
    (hA : A.Is GA) (hB : B.Is GB) : (Lanes.zip f A B).Is fun k ↦ g (GA k) (GB k) := by
  intro k hk
  have e : (Lanes.zip f A B).get k = f (A.get k) (B.get k) := by
    interval_cases k <;> rfl
  rw [e, hA k hk, hB k hk, hf]

/-- A register's words as stored: entries `16 r, …, 16 r + 15` of the encoded buffer. -/
theorem ldLanes_is (h : FusedOk env n R C) (b : Buf n) (X : Array FF) (hb : b.1 = encode X)
    (r : Nat) (hr : r < R) : (ldLanes h b r).Is fun k ↦ X.getD (16 * r + k) 0 := by
  intro k hk
  obtain ⟨b, hb'⟩ := b
  dsimp only at hb
  subst hb
  have e : ∀ (j : Nat) (hj : j ≤ 15),
      ldR env h ⟨encode X, hb'⟩ r hr j hj = (X.getD (16 * r + j) 0).val := by
    intro j hj
    unfold ldR
    rw [ld_encode, fOff_toNat h hr]
  unfold ldLanes
  rw [dite_eq_left_of_eq_true (eq_true hr)]
  interval_cases k <;> exact e _ (by decide)

theorem ld_eq_of {b b' : ByteArray} (e : b = b') (i : USize) (h : Win b i) (k : Nat)
    (hk : k ≤ 15) : ld b i h k hk = ld b' i (e ▸ h) k hk := by
  subst e; rfl

/-- The group's current rows of a column of the encoded view. -/
theorem colLanes_is (h : FusedOk env n R C) (V : Array FF) (hv : env.view = encode V) (c : Nat)
    (hc : c ≤ C) :
    (colLanes h c).Is fun k ↦ V.getD (env.cb.toNat + c * env.cs.toNat + k) 0 := by
  intro k hk
  have e : ∀ (j : Nat) (hj : j ≤ 15),
      ldC env h c hc j hj = (V.getD (env.cb.toNat + c * env.cs.toNat + j) 0).val := by
    intro j hj
    unfold ldC
    rw [ld_eq_of hv, ld_encode, colOff_fused h hc]
  unfold colLanes
  rw [dite_eq_left_of_eq_true (eq_true hc)]
  interval_cases k <;> exact e _ (by decide)

/-- Words stored into a register: entries `16 r, …, 16 r + 15` of the encoded buffer replaced. -/
theorem stLanes_upd (h : FusedOk env n R C) (b : Buf n) (X : Array FF) (hb : b.1 = encode X)
    (hX : X.size = 16 * R) (r : Nat) (hr : r < R) (L : Lanes) (G : Nat → FF) (hL : L.Is G) :
    (stLanes h b r L).1 = encode (updR X (16 * r) 16 G) := by
  obtain ⟨b, hb'⟩ := b
  dsimp only at hb
  subst hb
  have hn : n < USize.size := h.2.1
  have hs : (encode X).size < USize.size := by rw [hb']; exact hn
  unfold stLanes stR
  rw [dite_eq_left_of_eq_true (eq_true hr)]
  dsimp only
  rw [st16_eq _ _ _ hs]
  have e : ∀ k (hk : k < 16), L.get k = (G k).val := hL
  rw [show L.w0 = (G 0).val from e 0 (by decide), show L.w1 = (G 1).val from e 1 (by decide),
    show L.w2 = (G 2).val from e 2 (by decide), show L.w3 = (G 3).val from e 3 (by decide),
    show L.w4 = (G 4).val from e 4 (by decide), show L.w5 = (G 5).val from e 5 (by decide),
    show L.w6 = (G 6).val from e 6 (by decide), show L.w7 = (G 7).val from e 7 (by decide),
    show L.w8 = (G 8).val from e 8 (by decide), show L.w9 = (G 9).val from e 9 (by decide),
    show L.w10 = (G 10).val from e 10 (by decide), show L.w11 = (G 11).val from e 11 (by decide),
    show L.w12 = (G 12).val from e 12 (by decide), show L.w13 = (G 13).val from e 13 (by decide),
    show L.w14 = (G 14).val from e 14 (by decide), show L.w15 = (G 15).val from e 15 (by decide)]
  have ho := fOff_toNat h hr
  rw [CompPoly.CPolynomial.NTTFast.Packed.Native.write16U_encode _ _ hs (by rw [ho, hX]; omega),
    ho]
  have := splice_updR X (16 * r) 0 G (by rw [hX]; omega)
  rw [updR_zero, Nat.add_zero] at this
  exact congrArg encode this

end Words

/-! ### The fused machine on the rows' values -/

section Rel
variable {p : ℕ} [Mont32Field p]

local notation "FF" => FastField p

/-- The words of a fused chunk's buffer for the rows' slot states `ss` (row `k` of the group in
`ss k`): register `r < R0` of row `k` at entry `16 r + k`, slot `t < K` at `16 (R0 + t) + k`. -/
def ftab (R0 K : Nat) (ss : Nat → SlotSt FF) : Array FF :=
  tab (16 * (R0 + K)) fun idx ↦
    if idx / 16 < R0 then (ss (idx % 16)).reg (idx / 16) else (ss (idx % 16)).slot (idx / 16 - R0)

theorem size_ftab (R0 K : Nat) (ss : Nat → SlotSt FF) : (ftab R0 K ss).size = 16 * (R0 + K) :=
  size_tab ..

theorem ftab_congr (R0 K : Nat) {ss ss' : Nat → SlotSt FF}
    (h : ∀ k, (ss k).reg = (ss' k).reg ∧ (ss k).slot = (ss' k).slot) :
    ftab R0 K ss = ftab R0 K ss' := by
  unfold ftab
  refine tab_congr fun idx _ ↦ ?_
  rw [(h (idx % 16)).1, (h (idx % 16)).2]

theorem ftab_reg (R0 K : Nat) (ss : Nat → SlotSt FF) (r k : Nat) (hr : r < R0) (hk : k < 16) :
    (ftab R0 K ss).getD (16 * r + k) 0 = (ss k).reg r := by
  unfold ftab
  rw [getD_tab _ _ _ (by omega)]
  have h1 : (16 * r + k) / 16 = r := by omega
  have h2 : (16 * r + k) % 16 = k := by omega
  rw [h1, h2, ite_eq_left hr]

theorem ftab_slot (R0 K : Nat) (ss : Nat → SlotSt FF) (t k : Nat) (ht : t < K) (hk : k < 16) :
    (ftab R0 K ss).getD (16 * (R0 + t) + k) 0 = (ss k).slot t := by
  unfold ftab
  rw [getD_tab _ _ _ (by omega)]
  have h1 : (16 * (R0 + t) + k) / 16 = R0 + t := by omega
  have h2 : (16 * (R0 + t) + k) % 16 = k := by omega
  rw [h1, h2, ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- Register `d`'s entries replaced: the rows' registers `d` set. -/
theorem updR_ftab_reg (R0 K : Nat) (ss : Nat → SlotSt FF) (d : Nat) (hd : d < R0)
    (G : Nat → FF) :
    updR (ftab R0 K ss) (16 * d) 16 G =
      ftab R0 K fun k ↦ { ss k with reg := Function.update (ss k).reg d (G k) } := by
  apply array_eq_of_getD _ _ 0 (by rw [size_updR, size_ftab, size_ftab])
  intro idx
  rw [getD_updR, size_ftab]
  unfold ftab
  by_cases hi : idx < 16 * (R0 + K)
  · rw [getD_tab _ _ _ hi, getD_tab _ _ _ hi]
    by_cases hq : idx / 16 = d
    · rw [ite_eq_left ⟨hi, by omega, by omega⟩, ite_eq_left (by omega), hq]
      simp only [Function.update_self]
      congr 1
      omega
    · rw [ite_eq_right (by omega)]
      split
      · simp only [Function.update_of_ne hq]
      · rfl
  · rw [ite_eq_right (by omega), Montgomery.Native32.Words.getD_eq_zero _ _ (by rw [size_tab]; omega),
      Montgomery.Native32.Words.getD_eq_zero _ _ (by rw [size_tab]; omega)]

/-- Slot `t`'s entries replaced: the rows' slots `t` set. -/
theorem updR_ftab_slot (R0 K : Nat) (ss : Nat → SlotSt FF) (t : Nat) (G : Nat → FF) :
    updR (ftab R0 K ss) (16 * (R0 + t)) 16 G =
      ftab R0 K fun k ↦ { ss k with slot := Function.update (ss k).slot t (G k) } := by
  apply array_eq_of_getD _ _ 0 (by rw [size_updR, size_ftab, size_ftab])
  intro idx
  rw [getD_updR, size_ftab]
  unfold ftab
  by_cases hi : idx < 16 * (R0 + K)
  · rw [getD_tab _ _ _ hi, getD_tab _ _ _ hi]
    by_cases hq : idx / 16 = R0 + t
    · rw [ite_eq_left ⟨hi, by omega, by omega⟩, ite_eq_right (by omega)]
      rw [show idx / 16 - R0 = t by omega]
      simp only [Function.update_self]
      congr 1
      omega
    · rw [ite_eq_right (by omega)]
      split
      · rfl
      · simp only [Function.update_of_ne (show idx / 16 - R0 ≠ t by omega)]
  · rw [ite_eq_right (by omega), Montgomery.Native32.Words.getD_eq_zero _ _ (by rw [size_tab]; omega),
      Montgomery.Native32.Words.getD_eq_zero _ _ (by rw [size_tab]; omega)]

end Rel

/-- An operand a fused chunk reads: a register below `R0`, a column up to `C`, or a constant. -/
def Opd.FIn (R0 C : Nat) : Opd F → Prop
  | .reg r => r < R0
  | .cur c => c ≤ C
  | .const _ => True

/-- An instruction a fused chunk runs: registers below `R0`, columns up to `C`. -/
def Instr.FIn (R0 C : Nat) : Instr F → Prop
  | .load d _ => d < R0
  | .scalar d _ => d < R0
  | .bin _ d a b => d < R0 ∧ a.FIn R0 C ∧ b.FIn R0 C
  | .acc a _ => a.FIn R0 C

section Machine
variable {p : ℕ} [Mont32Field p] {env : GroupEnv} {n R0 K C : Nat}

local notation "FF" => FastField p

/-- A fused state holds the rows' slot states: its buffer encodes them, its slot is theirs, and
the words it holds are their registers'. -/
def FRel (R0 K : Nat) (st : FState n) (ss : Nat → SlotSt FF) : Prop :=
  st.b.1 = encode (ftab R0 K ss) ∧ (∀ k, (ss k).t = st.t) ∧
    ∀ r L, st.v r = some L → r < R0 ∧ L.Is fun k ↦ (ss k).reg r

/-- What the rows `ctx 0, …, ctx 15` of a group read: the encoded view's current rows and the
scalars' words. -/
structure GroupCtx (env : GroupEnv) (C : Nat) (ctx : Nat → Ctx FF) : Prop where
  view : ∃ V : Array FF, env.view = encode V ∧
    ∀ k < 16, ∀ c ≤ C, (ctx k).cur c = V.getD (env.cb.toNat + c * env.cs.toNat + k) 0
  scal : ∀ k < 16, ∀ i, scalAt env i = ((ctx k).scalar i).val

theorem readL_rel (h : FusedOk env n (R0 + K) C) (ctx : Nat → Ctx FF) (hc : GroupCtx env C ctx)
    (st : FState n) (ss : Nat → SlotSt FF) (hrel : FRel R0 K st ss) (a : Opd FF) (ha : a.FIn R0 C) :
    FRel R0 K (readL h st a).1 ss ∧
      (readL h st a).2.Is fun k ↦ (a.valR (ctx k) (ss k).reg) := by
  obtain ⟨hb, ht, hv⟩ := hrel
  cases a with
  | reg r =>
    rcases hL : st.v r with _ | L
    · have e : readL (p := p) h st (.reg r) =
          (⟨st.b, updL st.v r (ldLanes h st.b r), st.t⟩, ldLanes h st.b r) := by
        simp only [readL, hL]
      have hl : (ldLanes h st.b r).Is fun k ↦ (ss k).reg r := fun k hk ↦ by
        rw [ldLanes_is h st.b _ hb r (by have : r < R0 := ha; omega) k hk]
        dsimp only
        rw [ftab_reg R0 K ss r k ha hk]
      rw [e]
      refine ⟨⟨hb, ht, fun r' L' hL' ↦ ?_⟩, hl⟩
      dsimp only [updL] at hL'
      split at hL'
      · rename_i e'
        subst e'
        cases hL'
        exact ⟨ha, hl⟩
      · exact hv r' L' hL'
    · have e : readL (p := p) h st (.reg r) = (st, L) := by simp only [readL, hL]
      rw [e]
      exact ⟨⟨hb, ht, hv⟩, (hv r L hL).2⟩
  | cur c =>
    obtain ⟨V, hV, hcur⟩ := hc.view
    refine ⟨⟨hb, ht, hv⟩, fun k hk ↦ ?_⟩
    show (colLanes h c).get k = _
    rw [colLanes_is h V hV c ha k hk]
    show _ = ((ctx k).cur c).val
    rw [hcur k hk c ha]
  | const x => exact ⟨⟨hb, ht, hv⟩, fun k hk ↦ by interval_cases k <;> rfl⟩

/-- A load of a group into register `d`: its kernel writes the rows' loaded values. -/
def LoadOk (env : GroupEnv) (ctx : Nat → Ctx FF) (N d : Nat) (src : Src) : Prop :=
  ∀ X : Array FF, X.size = N →
    loadF env d src (encode X) = encode (updR X (16 * d) 16 fun k ↦ (ctx k).src src)

theorem frel_regs (st : FState n) (ss ss' : Nat → SlotSt FF) (b : Buf n) (d : Nat) (L : Lanes)
    (hrel : FRel R0 K st ss) (hb : b.1 = encode (ftab R0 K ss')) (hd : d < R0)
    (hL : L.Is fun k ↦ (ss' k).reg d) (hreg : ∀ k, ∀ r ≠ d, (ss' k).reg r = (ss k).reg r)
    (ht : ∀ k, (ss' k).t = (ss k).t) :
    FRel R0 K ⟨b, updL st.v d L, st.t⟩ ss' := by
  obtain ⟨-, ht0, hv⟩ := hrel
  refine ⟨hb, fun k ↦ (ht k).trans (ht0 k), fun r L' hL' ↦ ?_⟩
  dsimp only [updL] at hL'
  split at hL'
  · rename_i e
    subst e
    cases hL'
    exact ⟨hd, hL⟩
  · rename_i e
    obtain ⟨h1, h2⟩ := hv r L' hL'
    exact ⟨h1, fun k hk ↦ by rw [h2 k hk]; dsimp only; rw [hreg k r e]⟩

theorem exec_rel (ops : Op → UInt32 → UInt32 → UInt32)
    (hops : ∀ o x y, ops o x y = Op.wordG p o x y) (h : FusedOk env n (R0 + K) C)
    (ctx : Nat → Ctx FF) (hc : GroupCtx env C ctx) (st : FState n) (ss : Nat → SlotSt FF)
    (hrel : FRel R0 K st ss) (ins : Instr FF) (hin : ins.FIn R0 C)
    (hld : ∀ d src, ins = .load d src → LoadOk env ctx (16 * (R0 + K)) d src)
    (hslot : ∀ a w, ins = .acc a w → st.t < K) :
    FRel R0 K (ins.exec (fusedMachine ops R0 h) st) fun k ↦ ins.exec (slotMachine (ctx k)) (ss k) := by
  have hsz : ∀ ss' : Nat → SlotSt FF, (ftab R0 K ss').size = 16 * (R0 + K) := size_ftab R0 K
  cases ins with
  | load d src =>
    have hd : d < R0 := hin
    have hb : (keep st.b (loadF env d src st.b.1) (size_loadF env d src st.b.1)).1 =
        encode (ftab R0 K fun k ↦ (Instr.load d src).exec (slotMachine (ctx k)) (ss k)) := by
      show loadF env d src st.b.1 = _
      rw [hrel.1, hld d src rfl _ (hsz ss), updR_ftab_reg R0 K ss d hd]
      rfl
    refine frel_regs st ss _ _ d _ hrel hb hd (fun k hk ↦ ?_) (fun k r hr ↦ ?_) (fun _ ↦ rfl)
    · rw [ldLanes_is h _ _ hb d (by omega) k hk]
      dsimp only
      rw [ftab_reg R0 K _ d k hd hk]
    · show Function.update (ss k).reg d ((ctx k).src src) r = (ss k).reg r
      rw [Function.update_of_ne hr]
  | scalar d i =>
    have hd : d < R0 := hin
    have hL : (Lanes.rep (scalAt env i)).Is fun k ↦ (ctx k).scalar i := fun k hk ↦ by
      rw [hc.scal k hk i]
      interval_cases k <;> rfl
    have hb : (stLanes h st.b d (Lanes.rep (scalAt env i))).1 =
        encode (ftab R0 K fun k ↦ (Instr.scalar d i).exec (slotMachine (ctx k)) (ss k)) := by
      rw [stLanes_upd h st.b _ hrel.1 (hsz ss) d (by omega) _ _ hL, updR_ftab_reg R0 K ss d hd]
      rfl
    refine frel_regs st ss _ _ d _ hrel hb hd (fun k hk ↦ ?_) (fun k r hr ↦ ?_) (fun _ ↦ rfl)
    · rw [hL k hk]
      show _ = (Function.update (ss k).reg d ((ctx k).scalar i) d).val
      rw [Function.update_self]
    · show Function.update (ss k).reg d ((ctx k).scalar i) r = (ss k).reg r
      rw [Function.update_of_ne hr]
  | bin o d a b =>
    obtain ⟨hd, ha, hb'⟩ := hin
    have r1 := readL_rel h ctx hc st ss hrel a ha
    show FRel R0 K ⟨stLanes h (readL h (readL h st a).1 b).1.b d
      (Lanes.zip (ops o) (readL h st a).2 (readL h (readL h st a).1 b).2),
      updL (readL h (readL h st a).1 b).1.v d
        (Lanes.zip (ops o) (readL h st a).2 (readL h (readL h st a).1 b).2),
      (readL h (readL h st a).1 b).1.t⟩ _
    generalize readL h st a = A at r1 ⊢
    obtain ⟨st1, La⟩ := A
    obtain ⟨r1, hLa⟩ := r1
    have r2 := readL_rel h ctx hc st1 ss r1 b hb'
    generalize readL h st1 b = B at r2 ⊢
    obtain ⟨st2, Lb⟩ := B
    obtain ⟨r2, hLb⟩ := r2
    dsimp only at hLa hLb ⊢
    have hL := Lanes.is_zip (ops o) (o.eval) (fun x y ↦ by rw [hops, Op.wordG_val]) hLa hLb
    have hb : (stLanes h st2.b d (Lanes.zip (ops o) La Lb)).1 =
        encode (ftab R0 K fun k ↦ (Instr.bin o d a b).exec (slotMachine (ctx k)) (ss k)) := by
      rw [stLanes_upd h _ _ r2.1 (hsz ss) d (by omega) _ _ hL, updR_ftab_reg R0 K ss d hd]
      rfl
    refine frel_regs st2 ss _ _ d _ r2 hb hd (fun k hk ↦ ?_) (fun k r hr ↦ ?_) (fun _ ↦ rfl)
    · rw [hL k hk]
      show _ = (Function.update (ss k).reg d
        (o.eval (a.valR (ctx k) (ss k).reg) (b.valR (ctx k) (ss k).reg)) d).val
      rw [Function.update_self]
    · show Function.update (ss k).reg d
        (o.eval (a.valR (ctx k) (ss k).reg) (b.valR (ctx k) (ss k).reg)) r = (ss k).reg r
      rw [Function.update_of_ne hr]
  | acc a w =>
    have r1 := readL_rel h ctx hc st ss hrel a hin
    have hts : (readL h st a).1.t = st.t := by
      cases a with
      | reg r => rcases hL : st.v r with _ | L <;> simp only [readL, hL]
      | cur c => rfl
      | const x => rfl
    have hlt := hslot a w rfl
    show FRel R0 K ⟨stLanes h (readL h st a).1.b (R0 + (readL h st a).1.t) (readL h st a).2,
      (readL h st a).1.v, (readL h st a).1.t + 1⟩ _
    generalize readL h st a = A at r1 hts ⊢
    obtain ⟨st1, La⟩ := A
    obtain ⟨⟨hb1, ht1, hv1⟩, hLa⟩ := r1
    dsimp only at hLa hts ⊢
    have hslot' : ∀ k, (Instr.acc a w).exec (slotMachine (ctx k)) (ss k) =
        ⟨(ss k).reg, Function.update (ss k).slot st1.t (a.valR (ctx k) (ss k).reg),
          st1.t + 1⟩ := fun k ↦ by
      show (⟨(ss k).reg, Function.update (ss k).slot (ss k).t (a.valR (ctx k) (ss k).reg),
        (ss k).t + 1⟩ : SlotSt FF) = _
      rw [ht1 k]
    refine ⟨?_, fun k ↦ by dsimp only; rw [hslot' k], fun r L hL ↦ ?_⟩
    · rw [stLanes_upd h _ _ hb1 (hsz ss) _ (by omega) _ _ hLa, updR_ftab_slot R0 K ss st1.t]
      exact congrArg encode (ftab_congr R0 K fun k ↦ by rw [hslot' k]; exact ⟨rfl, rfl⟩)
    · obtain ⟨h1, h2⟩ := hv1 r L hL
      exact ⟨h1, fun k hk ↦ by rw [h2 k hk]; dsimp only; rw [hslot' k]⟩

theorem readL_t (h : FusedOk env n (R0 + K) C) (st : FState n) (a : Opd FF) :
    (readL h st a).1.t = st.t := by
  cases a with
  | reg r => rcases hL : st.v r with _ | L <;> simp only [readL, hL]
  | cur c => rfl
  | const x => rfl

theorem exec_t (ops : Op → UInt32 → UInt32 → UInt32) (h : FusedOk env n (R0 + K) C)
    (st : FState n) (ins : Instr FF) :
    (ins.exec (fusedMachine ops R0 h) st).t = st.t + (accWeights [ins]).length := by
  cases ins with
  | load d src => rfl
  | scalar d i => rfl
  | bin o d a b =>
    show (readL h (readL h st a).1 b).1.t = st.t + 0
    rw [readL_t, readL_t]
    rfl
  | acc a w =>
    show (readL h st a).1.t + 1 = st.t + 1
    rw [readL_t]

/-- **A fused chunk's instructions** run the slot machine on every row of the group. -/
theorem run_rel (ops : Op → UInt32 → UInt32 → UInt32)
    (hops : ∀ o x y, ops o x y = Op.wordG p o x y) (h : FusedOk env n (R0 + K) C)
    (ctx : Nat → Ctx FF) (hc : GroupCtx env C ctx) :
    ∀ (code : List (Instr FF)) (st : FState n) (ss : Nat → SlotSt FF), FRel R0 K st ss →
      (∀ i ∈ code, i.FIn R0 C) →
      (∀ d src, Instr.load d src ∈ code → LoadOk env ctx (16 * (R0 + K)) d src) →
      st.t + (accWeights code).length ≤ K →
      FRel R0 K (code.foldl (fun st i ↦ i.exec (fusedMachine ops R0 h) st) st)
        fun k ↦ code.foldl (fun s i ↦ i.exec (slotMachine (ctx k)) s) (ss k)
  | [], _, _, hrel, _, _, _ => hrel
  | ins :: code, st, ss, hrel, hin, hld, hK => by
    simp only [List.foldl_cons]
    have hK' : st.t + (accWeights [ins]).length + (accWeights code).length ≤ K := by
      cases ins <;> simp only [accWeights, List.length_cons, List.length_nil] at hK ⊢ <;> omega
    have hslot : ∀ a w, ins = Instr.acc a w → st.t < K := fun a w e ↦ by
      subst e
      simp only [accWeights, List.length_cons, List.length_nil] at hK'
      omega
    have hld1 : ∀ d src, ins = Instr.load d src → LoadOk env ctx (16 * (R0 + K)) d src :=
      fun d src e ↦ hld d src (e ▸ List.mem_cons_self)
    exact run_rel ops hops h ctx hc code _ _ (exec_rel ops hops h ctx hc st ss hrel ins
      (hin ins List.mem_cons_self) hld1 hslot) (fun i hi ↦ hin i (List.mem_cons_of_mem _ hi))
      (fun d src hm ↦ hld d src (List.mem_cons_of_mem _ hm)) (by rw [exec_t]; exact hK')

/-- **A fused chunk** on a group whose buffer holds the rows' slot states runs the slot machine on
every row, its accumulations in slots `0, 1, …`. -/
theorem fusedChunk_rel (ops : Op → UInt32 → UInt32 → UInt32)
    (hops : ∀ o x y, ops o x y = Op.wordG p o x y) (code : List (Instr FF))
    (ctx : Nat → Ctx FF) (hc : GroupCtx env C ctx) (ss : Nat → SlotSt FF)
    (hss : ∀ k, (ss k).t = 0) (hok : FusedOk env (4 * (16 * (R0 + K))) (R0 + K) C)
    (hin : ∀ i ∈ code, i.FIn R0 C)
    (hld : ∀ d src, Instr.load d src ∈ code → LoadOk env ctx (16 * (R0 + K)) d src)
    (hK : (accWeights code).length ≤ K) :
    fusedChunk ops R0 K C code env (encode (ftab R0 K ss)) =
      encode (ftab R0 K fun k ↦ code.foldl (fun s i ↦ i.exec (slotMachine (ctx k)) s) (ss k)) := by
  have hsz : (encode (ftab R0 K ss)).size = 4 * (16 * (R0 + K)) := by
    rw [size_encode_fields, size_ftab]
  unfold fusedChunk
  rw [dite_eq_left_of_eq_true (eq_true (hsz ▸ hok))]
  generalize hsz ▸ hok = h
  have h0 : FRel R0 K (⟨bufOf _, fun _ ↦ none, 0⟩ : FState _) ss :=
    ⟨rfl, hss, fun _ _ e ↦ (by cases e)⟩
  exact (run_rel ops hops h ctx hc code _ ss h0 hin hld (by rw [Nat.zero_add]; exact hK)).1

end Machine

/-! ### A group of a block -/

section Group
variable {p : ℕ} [Mont32Field p]

local notation "FF" => FastField p

/-- The block environment of a block of `B` rows. -/
abbrev blockOf (na B : Nat) (V : Array FF) (cb cs : Nat) (L : LoadsF p) (SC WT : Array FF) :
    GroupEnv :=
  blockEnv na B ⟨encode V, cb, cs⟩ L.enc (SC.map (·.val)) (WT.map (·.val))

theorem fOff_toNat' (d : Nat) (h : 16 * d < USize.size) : (fOff d).toNat = 16 * d :=
  USize.toNat_ofNat_of_lt' h

theorem tcolOff_group (na B g : Nat) (V : Array FF) (cb cs : Nat) (L : LoadsF p)
    (SC WT : Array FF) (c m : Nat) (hc : c * B + B ≤ m) (hm : 4 * m < USize.size)
    (hg : 16 * g + 16 ≤ B) :
    (tcolOff (groupEnv (blockOf na B V cb cs L SC WT) g) c).toNat = c * B + 16 * g := by
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hB : B.toUSize.toNat = B := USize.toNat_ofNat_of_lt' (by omega)
  have hg' : (16 * g).toUSize.toNat = 16 * g := USize.toNat_ofNat_of_lt' (by omega)
  have hcB : (c.toUSize * B.toUSize).toNat = c * B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [USize.toNat_mul, hB, h0, Nat.mul_zero, Nat.mul_zero, Nat.zero_mod]
    · have : c ≤ c * B := Nat.le_mul_of_pos_right c h0
      rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' (by omega), hB, hsz,
        Nat.mod_eq_of_lt (by omega)]
  simp only [tcolOff, groupEnv, blockOf, blockEnv]
  rw [USize.toNat_add, USize.toNat_add, hcB, hg', USize.toNat_zero, hsz,
    Nat.mod_eq_of_lt (show 0 + 16 * g < USize.size by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem sb_group (na B g : Nat) (V : Array FF) (cb cs : Nat) (L : LoadsF p) (SC WT : Array FF)
    (m : Nat) (hr : L.r0 + B ≤ m) (hm : 4 * m < USize.size) (hg : 16 * g + 16 ≤ B) :
    ((groupEnv (blockOf na B V cb cs L SC WT) g).sb).toNat = L.r0 + 16 * g := by
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have e : L.enc.r0 = L.r0 := rfl
  simp only [groupEnv, blockOf, blockEnv, e]
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega), USize.toNat_ofNat_of_lt' (by omega),
    hsz, Nat.mod_eq_of_lt (by omega)]

/-- **A load of a group of a block** writes the group's rows' loaded values. -/
theorem loadOk_group (na B g : Nat) (V : Array FF) (cb cs : Nat) (L : LoadsF p)
    (SC WT : Array FF) (hg : 16 * g + 16 ≤ B) (hL : L.Addr) (N d : Nat) (src : Src)
    (hs : L.InRange B src) (hd : 16 * d + 16 ≤ N) (hN : 4 * N < USize.size) :
    LoadOk (groupEnv (blockOf na B V cb cs L SC WT) g)
      (fun k ↦ blockCtx na V cb cs L SC WT B (16 * g + k)) N d src := by
  intro X hX
  obtain ⟨hM, hP, hPT, hQ, hQT, hPER, hFS, hLS, hTS⟩ := hL
  have hXs : 4 * X.size < USize.size := by rw [hX]; exact hN
  have hrd : 16 * d + 16 * 1 ≤ X.size := by rw [hX]; omega
  have hro : (fOff d).toNat = 16 * d := fOff_toNat' d (by omega)
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hgo (m : Nat) (hm : 16 * g + 16 ≤ m) (hM : 4 * m < USize.size) (x : USize)
      (hx : x.toNat + 16 * g + 16 ≤ m) : (x + (16 * g).toUSize).toNat = x.toNat + 16 * g := by
    rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega), hsz, Nat.mod_eq_of_lt (by omega)]
  have hseq (hS : L.Seq B) : L.nseq = true → ∀ k < 16 * 1,
      L.next.getD (L.r0 + 16 * g + k) 0 = L.next.getD (L.r0 + 16 * g) 0 + k := fun hn k hk ↦ by
    rw [Nat.add_assoc, hS hn _ (by omega), hS hn _ (by omega)]
    omega
  have hsrc : (updR X (16 * d) (16 * 1) fun k ↦ L.src B (16 * g + k) src) =
      updR X (16 * d) 16 fun k ↦ (blockCtx na V cb cs L SC WT B (16 * g + k)).src src := rfl
  rw [← hsrc]
  cases src <;> simp only [LoadsF.InRange] at hs
  case next c =>
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src]
    have := gather_upd X L.M 1 (16 * d) c (L.r0 + 16 * g) L.next L.nseq (fOff d) hro hXs hM
      hrd (fun k hk ↦ by rw [Nat.add_assoc]; exact hs.1 _ (by omega)) (hseq hs.2)
    rw [this]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case prepNext c =>
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src]
    have := gather_upd X L.P 1 (16 * d) c (L.r0 + 16 * g) L.next L.nseq (fOff d) hro hXs hP
      hrd (fun k hk ↦ by rw [Nat.add_assoc]; exact hs.1 _ (by omega)) (hseq hs.2)
    rw [this]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case permNext c =>
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src]
    have := gather_upd X L.Q 1 (16 * d) c (L.r0 + 16 * g) L.next L.nseq (fOff d) hro hXs hQ
      hrd (fun k hk ↦ by rw [Nat.add_assoc]; exact hs.1 _ (by omega)) (hseq hs.2)
    rw [this]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case prepCur c =>
    have ht : (tcolOff (groupEnv (blockOf na B V cb cs L SC WT) g) c).toNat = c * B + 16 * g :=
      tcolOff_group na B g V cb cs L SC WT c L.PT.size hs hPT hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copy_upd X L.PT 1 (16 * d) (c * B + 16 * g) (fOff d) _ hro ht hXs hPT hrd (by omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc, Nat.add_comm (c * B)]
  case permCur c =>
    have ht : (tcolOff (groupEnv (blockOf na B V cb cs L SC WT) g) c).toNat = c * B + 16 * g :=
      tcolOff_group na B g V cb cs L SC WT c L.QT.size hs hQT hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copy_upd X L.QT 1 (16 * d) (c * B + 16 * g) (fOff d) _ hro ht hXs hQT hrd (by omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc, Nat.add_comm (c * B)]
  case periodic j =>
    have ht : j < L.PER.size → ((groupEnv (blockOf na B V cb cs L SC WT) g).sb).toNat =
        L.r0 + 16 * g := fun hj ↦ by
      have hc : (L.PER.getD j #[]) ∈ L.PER := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
        exact Array.getElem_mem hj
      exact sb_group na B g V cb cs L SC WT _ (hs hj) (hPER _ hc) hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copyPer_upd X L.PER 1 (16 * d) j (L.r0 + 16 * g) (fOff d) _ hro ht hXs hPER hrd
      (fun hj ↦ by have := hs hj; omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case isFirstRow =>
    have ht := sb_group na B g V cb cs L SC WT _ hs hFS hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copy_upd X L.FS 1 (16 * d) (L.r0 + 16 * g) (fOff d) _ hro ht hXs hFS hrd (by omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case isLastRow =>
    have ht := sb_group na B g V cb cs L SC WT _ hs hLS hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copy_upd X L.LS 1 (16 * d) (L.r0 + 16 * g) (fOff d) _ hro ht hXs hLS hrd (by omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]
  case isTransition =>
    have ht := sb_group na B g V cb cs L SC WT _ hs hTS hg
    simp only [loadF, groupEnv, blockOf, blockEnv, LoadsF.enc, LoadsF.src] at ht ⊢
    rw [copy_upd X L.TS 1 (16 * d) (L.r0 + 16 * g) (fOff d) _ hro ht hXs hTS hrd (by omega)]
    refine congrArg encode (updR_congr fun k _ ↦ ?_)
    rw [Nat.add_assoc]

end Group

end CompStark.Stark.Prog
