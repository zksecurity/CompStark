/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgGroup

/-! # Fused code on one group of rows

The words a fused chunk (`CompStark/Stark/ProgGen.lean`, `#gen_fused_chunks`) reads and writes on
one group of sixteen rows: the registers below `R`, sixteen words apart after the accumulators, and
the group's current rows of the columns up to `C`. One check of the group's shape (`FusedOk`) puts
every word the chunk addresses in its buffer (`regWin`, `colWin`), so the chunk reads and writes
them unchecked: operands as sixteen words (`ldR`, `ldC`), results as sixteen words stored
(`stR`). The kernels of loads and accumulations keep the buffer's size (`size_gather` and its kin).
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompPoly.CPolynomial.NTTFast.Packed.Native (Buf)
open Montgomery.Native32 (Mont32Field FastField)

/-- Register `r`'s sixteen words in a fused chunk's buffer. -/
@[inline] def fOff (r : Nat) : USize := (16 * r).toUSize

/-- A group of sixteen rows on which a fused chunk addresses the registers below `R`, sixteen words
each from word `0`, in a buffer of `n` bytes, and the current rows of the columns up to `C`. -/
def FusedOk (env : GroupEnv) (n R C : Nat) : Prop :=
  4 * (16 * R) ≤ n ∧ n < USize.size ∧
    4 * (env.cb.toNat + C * env.cs.toNat + 16) ≤ env.view.size ∧ env.view.size < USize.size

instance instDecidableFusedOk (env : GroupEnv) (n R C : Nat) :
    Decidable (FusedOk env n R C) := by
  unfold FusedOk; infer_instance

theorem fOff_toNat {env : GroupEnv} {n R C r : Nat} (h : FusedOk env n R C) (hr : r < R) :
    (fOff r).toNat = 16 * r := by
  obtain ⟨h1, h2, -⟩ := h
  exact USize.toNat_ofNat_of_lt' (by omega)

/-- Register `r < R`'s sixteen words are in the buffer. -/
theorem regWin {env : GroupEnv} {n R C r : Nat} {b : ByteArray} (h : FusedOk env n R C)
    (hb : b.size = n) (hr : r < R) : Win b (fOff r) := by
  have e := fOff_toNat h hr
  obtain ⟨h1, h2, -⟩ := h
  unfold Win
  rw [e, hb]
  omega

theorem colOff_fused {env : GroupEnv} {n R C c : Nat} (h : FusedOk env n R C) (hc : c ≤ C) :
    (colOff env c).toNat = env.cb.toNat + c * env.cs.toNat := by
  obtain ⟨-, -, h4, h5⟩ := h
  have hsz : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hcs : c * env.cs.toNat ≤ C * env.cs.toNat := Nat.mul_le_mul_right _ hc
  have hm : (c.toUSize * env.cs).toNat = c * env.cs.toNat := by
    rcases Nat.eq_zero_or_pos env.cs.toNat with h0 | h0
    · rw [USize.toNat_mul, h0, Nat.mul_zero, Nat.mul_zero, Nat.zero_mod]
    · have hc' : c < USize.size := by
        have := Nat.le_mul_of_pos_right c h0
        omega
      rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hc', hsz, Nat.mod_eq_of_lt (by omega)]
  unfold colOff
  rw [USize.toNat_add, hm, hsz, Nat.mod_eq_of_lt (by omega)]

/-- The current rows of column `c ≤ C` are in the view. -/
theorem colWin {env : GroupEnv} {n R C c : Nat} (h : FusedOk env n R C) (hc : c ≤ C) :
    Win env.view (colOff env c) := by
  have e := colOff_fused h hc
  obtain ⟨-, -, h4, h5⟩ := h
  have hcs : c * env.cs.toNat ≤ C * env.cs.toNat := Nat.mul_le_mul_right _ hc
  unfold Win
  rw [e]
  omega

/-- Word `k` of register `r`. -/
@[inline] def ldR (env : @& GroupEnv) {n R C : Nat} (h : FusedOk env n R C) (b : @& Buf n)
    (r : Nat) (hr : r < R) (k : Nat) (hk : k ≤ 15) : UInt32 :=
  ld b.1 (fOff r) (regWin h b.2 hr) k hk

/-- Word `k` of the group's current rows of column `c`. -/
@[inline] def ldC (env : @& GroupEnv) {n R C : Nat} (h : FusedOk env n R C) (c : Nat)
    (hc : c ≤ C) (k : Nat) (hk : k ≤ 15) : UInt32 :=
  ld env.view (colOff env c) (colWin h hc) k hk

/-- Sixteen words stored into register `r`. -/
@[inline] def stR (env : @& GroupEnv) {n R C : Nat} (h : FusedOk env n R C) (b : Buf n) (r : Nat)
    (hr : r < R) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : Buf n :=
  ⟨st16 b.1 (fOff r) (regWin h b.2 hr) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
    (size_st16 ..).trans b.2⟩

/-- A loaded column into register `d` of a fused chunk's buffer, on one group. -/
@[noinline] def loadF (env : @& GroupEnv) (d : Nat) (src : Src) (s : ByteArray) : ByteArray :=
  match src with
  | .next c => gather 1 s (fOff d) env.L.main c env.L.next env.L.r0 env.L.nseq
  | .prepCur c => copy 1 s env.L.prepT (fOff d) (tcolOff env c)
  | .prepNext c => gather 1 s (fOff d) env.L.prep c env.L.next env.L.r0 env.L.nseq
  | .permCur c => copy 1 s env.L.permT (fOff d) (tcolOff env c)
  | .permNext c => gather 1 s (fOff d) env.L.perm c env.L.next env.L.r0 env.L.nseq
  | .periodic j => copyPer 1 s env.L.per j (fOff d) env.sb
  | .isFirstRow => copy 1 s env.L.first (fOff d) env.sb
  | .isLastRow => copy 1 s env.L.last (fOff d) env.sb
  | .isTransition => copy 1 s env.L.trans (fOff d) env.sb

/-- A buffer as a buffer of its size. -/
@[inline] def bufOf (s : ByteArray) : Buf s.size := ⟨s, rfl⟩

/-- A buffer of the same size. -/
@[inline] def keep {n : Nat} (b : Buf n) (s : ByteArray) (h : s.size = b.1.size) : Buf n :=
  ⟨s, h.trans b.2⟩

theorem size_runW {n : Nat} (nm : Nat) (hnm : 16 * nm < USize.size)
    (step : Buf n → (o : USize) → o.toNat + 16 ≤ 16 * nm → Buf n) (s : Buf n) :
    (runW nm hnm step s).1.size = n := (runW nm hnm step s).2

theorem size_fill (nm : Nat) (s : ByteArray) (d : USize) (c : UInt32) :
    (fill nm s d c).size = s.size := by
  unfold fill; split
  · exact size_runW ..
  · rfl

theorem size_kEW (f : UInt32 → UInt32 → UInt32) (nm : Nat) (s : ByteArray) (e : ByteArray)
    (d a : USize) (c : UInt32) : (kEW f nm s e d a c).size = s.size := by
  unfold kEW; split
  · exact size_runW ..
  · rfl

theorem size_copy (nm : Nat) (s : ByteArray) (e : ByteArray) (d a : USize) :
    (copy nm s e d a).size = s.size := size_kEW ..

theorem size_gather (nm : Nat) (s : ByteArray) (d : USize) (m : Cols) (c : Nat)
    (next : Array Nat) (r0 : Nat) (nseq : Bool) :
    (gather nm s d m c next r0 nseq).size = s.size := by
  unfold gather
  dsimp only
  split
  · exact size_kEW ..
  · split
    · exact size_runW ..
    · rfl

theorem size_copyPer (nm : Nat) (s : ByteArray) (per : Array ByteArray) (j : Nat) (d a : USize) :
    (copyPer nm s per j d a).size = s.size := by
  unfold copyPer; split
  · exact size_copy ..
  · exact size_fill ..

theorem size_loadF (env : GroupEnv) (d : Nat) (src : Src) (s : ByteArray) :
    (loadF env d src s).size = s.size := by
  unfold loadF
  split
  all_goals first | exact size_gather .. | exact size_copy .. | exact size_copyPer ..

/-! ### The fused machine

A fused chunk is straight-line code on one group of sixteen rows, its values sixteen words in
locals. Its meaning is a machine (`fusedMachine`): the buffer, sixteen words per register from word
`0` and then a slot of sixteen words per accumulation, every result stored; the words of every
register as the chunk holds them (`v`), read from the buffer until written; and the next slot. -/

/-- Sixteen words, one per row of a group. -/
structure Lanes where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  w8 : UInt32
  w9 : UInt32
  w10 : UInt32
  w11 : UInt32
  w12 : UInt32
  w13 : UInt32
  w14 : UInt32
  w15 : UInt32

/-- Sixteen copies of a word. -/
@[inline] def Lanes.rep (x : UInt32) : Lanes := ⟨x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x⟩

/-- Word `k` of sixteen words. -/
def Lanes.get (L : Lanes) : Nat → UInt32
  | 0 => L.w0
  | 1 => L.w1
  | 2 => L.w2
  | 3 => L.w3
  | 4 => L.w4
  | 5 => L.w5
  | 6 => L.w6
  | 7 => L.w7
  | 8 => L.w8
  | 9 => L.w9
  | 10 => L.w10
  | 11 => L.w11
  | 12 => L.w12
  | 13 => L.w13
  | 14 => L.w14
  | 15 => L.w15
  | _ => 0

/-- Words combined word by word. -/
@[inline] def Lanes.zip (f : UInt32 → UInt32 → UInt32) (A B : Lanes) : Lanes :=
  ⟨f A.w0 B.w0, f A.w1 B.w1, f A.w2 B.w2, f A.w3 B.w3, f A.w4 B.w4, f A.w5 B.w5, f A.w6 B.w6,
    f A.w7 B.w7, f A.w8 B.w8, f A.w9 B.w9, f A.w10 B.w10, f A.w11 B.w11, f A.w12 B.w12,
    f A.w13 B.w13, f A.w14 B.w14, f A.w15 B.w15⟩

section
variable {env : GroupEnv} {n R C : Nat}

/-- Register `r`'s words in the buffer. -/
@[inline] def ldLanes (h : FusedOk env n R C) (b : Buf n) (r : Nat) : Lanes :=
  if hr : r < R then
    ⟨ldR env h b r hr 0 (by decide), ldR env h b r hr 1 (by decide),
    ldR env h b r hr 2 (by decide), ldR env h b r hr 3 (by decide),
    ldR env h b r hr 4 (by decide), ldR env h b r hr 5 (by decide),
    ldR env h b r hr 6 (by decide), ldR env h b r hr 7 (by decide),
    ldR env h b r hr 8 (by decide), ldR env h b r hr 9 (by decide),
    ldR env h b r hr 10 (by decide), ldR env h b r hr 11 (by decide),
    ldR env h b r hr 12 (by decide), ldR env h b r hr 13 (by decide),
    ldR env h b r hr 14 (by decide), ldR env h b r hr 15 (by decide)⟩
  else Lanes.rep 0

/-- The group's current rows of column `c`. -/
@[inline] def colLanes (h : FusedOk env n R C) (c : Nat) : Lanes :=
  if hc : c ≤ C then
    ⟨ldC env h c hc 0 (by decide), ldC env h c hc 1 (by decide), ldC env h c hc 2 (by decide),
    ldC env h c hc 3 (by decide), ldC env h c hc 4 (by decide), ldC env h c hc 5 (by decide),
    ldC env h c hc 6 (by decide), ldC env h c hc 7 (by decide), ldC env h c hc 8 (by decide),
    ldC env h c hc 9 (by decide), ldC env h c hc 10 (by decide), ldC env h c hc 11 (by decide),
    ldC env h c hc 12 (by decide), ldC env h c hc 13 (by decide), ldC env h c hc 14 (by decide),
    ldC env h c hc 15 (by decide)⟩
  else Lanes.rep 0

/-- Words stored into register `r`. -/
@[inline] def stLanes (h : FusedOk env n R C) (b : Buf n) (r : Nat) (L : Lanes) : Buf n :=
  if hr : r < R then
    stR env h b r hr L.w0 L.w1 L.w2 L.w3 L.w4 L.w5 L.w6 L.w7 L.w8 L.w9 L.w10 L.w11 L.w12 L.w13
      L.w14 L.w15
  else b

end

/-- The words held of every register, with register `d`'s set to `L`. -/
def updL (v : Nat → Option Lanes) (d : Nat) (L : Lanes) : Nat → Option Lanes := fun r ↦
  if r = d then some L else v r

/-- The state of a fused chunk: its buffer, the words it holds of the registers, and the next
slot. -/
structure FState (n : Nat) where
  b : Buf n
  v : Nat → Option Lanes
  t : Nat

/-- The operation `o` on two words by `fa`, `fs` or `fm`. -/
@[inline] def opsOf (fa fs fm : UInt32 → UInt32 → UInt32) (o : Op) (x y : UInt32) : UInt32 :=
  match o with
  | .add => fa x y
  | .sub => fs x y
  | .mul => fm x y

section
variable {p : ℕ} [Mont32Field p] {env : GroupEnv} {n R C : Nat}

/-- An operand's words: a register's as held, else read from the buffer and then held. -/
@[inline] def readL (h : FusedOk env n R C) (st : FState n) : Opd (FastField p) → FState n × Lanes
  | .reg r => match st.v r with
    | some L => (st, L)
    | none => let L := ldLanes h st.b r; (⟨st.b, updL st.v r L, st.t⟩, L)
  | .cur c => (st, colLanes h c)
  | .const x => (st, Lanes.rep x.val)

/-- A fused chunk's instructions on its state, the operations on words `ops`, the slots from
register `R0` on. -/
def fusedMachine (ops : Op → UInt32 → UInt32 → UInt32) (R0 : Nat) (h : FusedOk env n R C) :
    Machine (FastField p) (FState n) where
  load d src st :=
    let b := keep st.b (loadF env d src st.b.1) (size_loadF env d src st.b.1)
    ⟨b, updL st.v d (ldLanes h b d), st.t⟩
  scalar d i st :=
    let L := Lanes.rep (scalAt env i)
    ⟨stLanes h st.b d L, updL st.v d L, st.t⟩
  bin o d a b st :=
    let ra := readL h st a
    let rb := readL h ra.1 b
    let L := Lanes.zip (ops o) ra.2 rb.2
    ⟨stLanes h rb.1.b d L, updL rb.1.v d L, rb.1.t⟩
  acc a _ st :=
    let ra := readL h st a
    ⟨stLanes h ra.1.b (R0 + ra.1.t) ra.2, ra.1.v, ra.1.t + 1⟩

end

/-- A fused chunk: the instructions `code` on one group, the registers below `R0`, the `K` slots
from register `R0` on, its first accumulation in slot `0`, the columns up to `C`. -/
def fusedChunk {p : ℕ} [Mont32Field p] (ops : Op → UInt32 → UInt32 → UInt32) (R0 K C : Nat)
    (code : List (Instr (FastField p))) (env : GroupEnv) (s : ByteArray) : ByteArray :=
  if h : FusedOk env s.size (R0 + K) C then
    (code.foldl (fun st i ↦ i.exec (fusedMachine ops R0 h) st)
      (⟨bufOf s, fun _ ↦ none, 0⟩ : FState s.size)).b.1
  else s

/-- Group `g` of a block: its sixteen rows from the block's row `16 g`, the view's current rows,
the loads, the transposed traces and the selectors shifted by `16 g`. -/
@[inline] def groupEnv (env : GroupEnv) (g : Nat) : GroupEnv :=
  let o := (16 * g).toUSize
  let L : Loads := { env.L with r0 := env.L.r0 + 16 * g }
  ⟨env.na, 1, 16, env.view, env.cb + o, env.cs, L, env.tcb + o, env.tcs, env.sb + o, env.scal,
    env.wts⟩

/-! ### Fused kernels -/

/-- The weights of a code's accumulations, in order: slot `t` holds the `t`-th accumulation. -/
def accWeights {F : Type} : List (Instr F) → List Nat
  | [] => []
  | .acc _ w :: is => w :: accWeights is
  | _ :: is => accWeights is

/-- An operand a fused chunk reads: a register below `R0`, a column up to `C`, or a constant. -/
def Opd.fin {F : Type} (R0 C : Nat) : Opd F → Bool
  | .reg r => r < R0
  | .cur c => c ≤ C
  | .const _ => true

/-- An instruction a fused chunk runs: registers below `R0`, columns up to `C`. -/
def Instr.fin {F : Type} (R0 C : Nat) : Instr F → Bool
  | .load d _ => d < R0
  | .scalar d _ => d < R0
  | .bin _ d a b => d < R0 && a.fin R0 C && b.fin R0 C
  | .acc a _ => a.fin R0 C

/-- A fused chunk with its meaning: `fusedChunk` of its operations and code. -/
structure FChunk (p : ℕ) [Mont32Field p] (R0 K C : Nat) where
  run : GroupEnv → ByteArray → ByteArray
  ops : Op → UInt32 → UInt32 → UInt32
  code : List (Instr (FastField p))
  ops_eq : ∀ o x y, ops o x y = Op.wordG p o x y
  run_eq : ∀ env s, run env s = fusedChunk ops R0 K C code env s

/-- A program's fused code: chunks in order, on the registers below `R0`, `K` slots from register
`R0` on and the columns up to `C`. -/
structure FusedKernel (p : ℕ) [Mont32Field p] where
  R0 : Nat
  K : Nat
  C : Nat
  chunks : List (FChunk p R0 K C)

namespace FusedKernel
variable {p : ℕ} [Mont32Field p]

/-- The program's code: the chunks' in order. -/
def code (k : FusedKernel p) : Array (Instr (FastField p)) :=
  (k.chunks.map (·.code)).flatten.toArray

/-- The check of a fused kernel: its instructions read registers below `R0` and columns up to
`C`, and every chunk has at most `K` accumulations. -/
def ok (k : FusedKernel p) : Bool :=
  k.code.all (·.fin k.R0 k.C) && k.chunks.all fun c ↦ (accWeights c.code).length ≤ k.K

/-- The chunks on group `g` of a block, from the buffer `sc`. -/
def runGroup (k : FusedKernel p) (env : GroupEnv) (g : Nat) (sc : ByteArray) : ByteArray :=
  runChunks (k.chunks.map fun c ↦ c.run (groupEnv env g)) sc

end FusedKernel

/-- The weights' word `i` of a group. -/
@[inline] def wtAt (env : @& GroupEnv) (i : Nat) : UInt32 := env.wts.getD i 0

/-! ### Accumulation chunks

After a chunk, its slots times their weights are added to the group's accumulators, one
accumulation chunk per chunk and number of accumulators: straight-line code holding the
accumulators' words in locals, every result stored (`accChunk`). -/

/-- The words an accumulation chunk reads and writes: `m` slots of sixteen words from register
`R0` of a chunk's buffer of `n` bytes, and `na` accumulators of sixteen words in a buffer of
`a` bytes. -/
def AccOk (n a R0 m na : Nat) : Prop :=
  4 * (16 * (R0 + m)) ≤ n ∧ n < USize.size ∧ 4 * (16 * na) ≤ a ∧ a < USize.size

instance instDecidableAccOk (n a R0 m na : Nat) : Decidable (AccOk n a R0 m na) := by
  unfold AccOk; infer_instance

section
variable {n a R0 m na : Nat}

theorem slotWin (h : AccOk n a R0 m na) {b : ByteArray} (hb : b.size = n) {t : Nat}
    (ht : t < m) : Win b (fOff (R0 + t)) := by
  obtain ⟨h1, h2, -⟩ := h
  have e : (fOff (R0 + t)).toNat = 16 * (R0 + t) := USize.toNat_ofNat_of_lt' (by omega)
  unfold Win
  rw [e, hb]
  omega

theorem planeWin (h : AccOk n a R0 m na) {b : ByteArray} (hb : b.size = a) {j : Nat}
    (hj : j < na) : Win b (fOff j) := by
  obtain ⟨-, -, h3, h4⟩ := h
  have e : (fOff j).toNat = 16 * j := USize.toNat_ofNat_of_lt' (by omega)
  unfold Win
  rw [e, hb]
  omega

/-- Word `k` of slot `t`. -/
@[inline] def ldS (h : AccOk n a R0 m na) (sc : @& ByteArray) (hsc : sc.size = n) (t : Nat)
    (ht : t < m) (k : Nat) (hk : k ≤ 15) : UInt32 :=
  ld sc (fOff (R0 + t)) (slotWin h hsc ht) k hk

/-- Word `k` of accumulator `j`. -/
@[inline] def ldP (h : AccOk n a R0 m na) (b : @& Buf a) (j : Nat) (hj : j < na) (k : Nat)
    (hk : k ≤ 15) : UInt32 :=
  ld b.1 (fOff j) (planeWin h b.2 hj) k hk

/-- Sixteen words stored into accumulator `j`. -/
@[inline] def stP (h : AccOk n a R0 m na) (b : Buf a) (j : Nat) (hj : j < na)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : Buf a :=
  ⟨st16 b.1 (fOff j) (planeWin h b.2 hj) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
    (size_st16 ..).trans b.2⟩

/-- Slot `t`'s words. -/
@[inline] def slotLanes (h : AccOk n a R0 m na) (sc : @& ByteArray) (hsc : sc.size = n)
    (t : Nat) : Lanes :=
  if ht : t < m then
    ⟨ldS h sc hsc t ht 0 (by decide), ldS h sc hsc t ht 1 (by decide),
    ldS h sc hsc t ht 2 (by decide), ldS h sc hsc t ht 3 (by decide),
    ldS h sc hsc t ht 4 (by decide), ldS h sc hsc t ht 5 (by decide),
    ldS h sc hsc t ht 6 (by decide), ldS h sc hsc t ht 7 (by decide),
    ldS h sc hsc t ht 8 (by decide), ldS h sc hsc t ht 9 (by decide),
    ldS h sc hsc t ht 10 (by decide), ldS h sc hsc t ht 11 (by decide),
    ldS h sc hsc t ht 12 (by decide), ldS h sc hsc t ht 13 (by decide),
    ldS h sc hsc t ht 14 (by decide), ldS h sc hsc t ht 15 (by decide)⟩
  else Lanes.rep 0

/-- Accumulator `j`'s words. -/
@[inline] def planeLanes (h : AccOk n a R0 m na) (b : Buf a) (j : Nat) : Lanes :=
  if hj : j < na then
    ⟨ldP h b j hj 0 (by decide), ldP h b j hj 1 (by decide), ldP h b j hj 2 (by decide),
    ldP h b j hj 3 (by decide), ldP h b j hj 4 (by decide), ldP h b j hj 5 (by decide),
    ldP h b j hj 6 (by decide), ldP h b j hj 7 (by decide), ldP h b j hj 8 (by decide),
    ldP h b j hj 9 (by decide), ldP h b j hj 10 (by decide), ldP h b j hj 11 (by decide),
    ldP h b j hj 12 (by decide), ldP h b j hj 13 (by decide), ldP h b j hj 14 (by decide),
    ldP h b j hj 15 (by decide)⟩
  else Lanes.rep 0

/-- Words stored into accumulator `j`. -/
@[inline] def stPlane (h : AccOk n a R0 m na) (b : Buf a) (j : Nat) (L : Lanes) : Buf a :=
  if hj : j < na then
    stP h b j hj L.w0 L.w1 L.w2 L.w3 L.w4 L.w5 L.w6 L.w7 L.w8 L.w9 L.w10 L.w11 L.w12 L.w13
      L.w14 L.w15
  else b

end

/-- Words combined word by word with four words of four operands each. -/
@[inline] def Lanes.zip4 (f : UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 →
    UInt32 → UInt32) (A B C D : Lanes) (a b c d : UInt32) : Lanes :=
  ⟨f A.w0 a B.w0 b C.w0 c D.w0 d, f A.w1 a B.w1 b C.w1 c D.w1 d,
    f A.w2 a B.w2 b C.w2 c D.w2 d, f A.w3 a B.w3 b C.w3 c D.w3 d,
    f A.w4 a B.w4 b C.w4 c D.w4 d, f A.w5 a B.w5 b C.w5 c D.w5 d,
    f A.w6 a B.w6 b C.w6 c D.w6 d, f A.w7 a B.w7 b C.w7 c D.w7 d,
    f A.w8 a B.w8 b C.w8 c D.w8 d, f A.w9 a B.w9 b C.w9 c D.w9 d,
    f A.w10 a B.w10 b C.w10 c D.w10 d, f A.w11 a B.w11 b C.w11 c D.w11 d,
    f A.w12 a B.w12 b C.w12 c D.w12 d, f A.w13 a B.w13 b C.w13 c D.w13 d,
    f A.w14 a B.w14 b C.w14 c D.w14 d, f A.w15 a B.w15 b C.w15 c D.w15 d⟩

/-- The words of the accumulators with accumulator `j`'s set to `L`. -/
def updA (v : Nat → Lanes) (j : Nat) (L : Lanes) : Nat → Lanes := fun i ↦
  if i = j then L else v i

/-- The state of an accumulation chunk: its accumulators' buffer and their words. -/
structure AState (a : Nat) where
  b : Buf a
  v : Nat → Lanes

/-- Accumulator `j` plus the words `L`. -/
@[inline] def AState.add {a : Nat} {n R0 m na : Nat} (ops : Op → UInt32 → UInt32 → UInt32)
    (h : AccOk n a R0 m na) (st : AState a) (j : Nat) (L : Lanes) : AState a :=
  let L := Lanes.zip (ops .add) (st.v j) L
  ⟨stPlane h st.b j L, updA st.v j L⟩

/-- An accumulation chunk: the `na` accumulators plus the slots `t` of the chunk's buffer `sc`
times the coordinates of their weights `ws[t]`, four slots at a time by `mul4` (four products
summed and reduced once), the last slots one at a time, the operations on words `ops`. -/
def accChunk (ops : Op → UInt32 → UInt32 → UInt32)
    (mul4 : UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32)
    (R0 na : Nat) (ws : List Nat) (env : @& GroupEnv) (sc : @& ByteArray) (acc : ByteArray) :
    ByteArray :=
  if h : AccOk sc.size acc.size R0 ws.length na then
    let S := slotLanes h sc rfl
    let c (t j : Nat) : UInt32 := wtAt env (na * ws.getD t 0 + j)
    let st := (List.range (ws.length / 4)).foldl (fun st q ↦ (List.range na).foldl (fun st j ↦
      st.add ops h j (Lanes.zip4 mul4 (S (4 * q)) (S (4 * q + 1)) (S (4 * q + 2)) (S (4 * q + 3))
        (c (4 * q) j) (c (4 * q + 1) j) (c (4 * q + 2) j) (c (4 * q + 3) j))) st)
      (⟨bufOf acc, planeLanes h (bufOf acc)⟩ : AState acc.size)
    ((List.range' (4 * (ws.length / 4)) (ws.length % 4)).foldl (fun st t ↦
      (List.range na).foldl (fun st j ↦
        st.add ops h j (Lanes.zip (ops .mul) (S t) (Lanes.rep (c t j)))) st) st).b.1
  else acc

end CompStark.Stark.Prog
