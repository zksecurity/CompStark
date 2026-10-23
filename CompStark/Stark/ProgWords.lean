/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Prog
public import CompStark.Stark.Words

/-! # Programs on blocks of packed words

A program (`Prog`) runs on a block of `B` rows at once: the four accumulators and the registers
are buffers of `B` packed Montgomery words (`Regs`), accumulator `j` the `j`-th and register `r`
the `(4 + r)`-th, and every instruction is a pass over the block in place, sixteen words at a time.
An operand on the trace's current row is read where it is: column `c` of the block's view at words
`cb + c · cs` of its buffer. A constant operand is one word for every row.
-/

@[expose] public section
namespace CompStark.Stark.Prog
open CompStark.Poseidon2.Packed (Fits)
open CompStark.Words (rd)
open CompPoly.CPolynomial.NTTFast.Packed (add sub mul)
open Montgomery.Native32 (Mont32Field FastField)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read write write16U zeroWords)

/-! ### Sixteen-word kernels -/

/-- Sixteen results of `f` on the words `x k`, `y k`, stored from word `io` of `out`. -/
@[inline] def lanes16 (f : UInt32 → UInt32 → UInt32) (x y : (k : Nat) → k ≤ 15 → UInt32)
    (out : ByteArray) (io : USize) : ByteArray :=
  write16U out io (f (x 0 (by decide)) (y 0 (by decide))) (f (x 1 (by decide)) (y 1 (by decide)))
    (f (x 2 (by decide)) (y 2 (by decide))) (f (x 3 (by decide)) (y 3 (by decide)))
    (f (x 4 (by decide)) (y 4 (by decide))) (f (x 5 (by decide)) (y 5 (by decide)))
    (f (x 6 (by decide)) (y 6 (by decide))) (f (x 7 (by decide)) (y 7 (by decide)))
    (f (x 8 (by decide)) (y 8 (by decide))) (f (x 9 (by decide)) (y 9 (by decide)))
    (f (x 10 (by decide)) (y 10 (by decide))) (f (x 11 (by decide)) (y 11 (by decide)))
    (f (x 12 (by decide)) (y 12 (by decide))) (f (x 13 (by decide)) (y 13 (by decide)))
    (f (x 14 (by decide)) (y 14 (by decide))) (f (x 15 (by decide)) (y 15 (by decide)))

/-- `f` on words `ia, …` and `ib, …` of the registers into words `io, …`. -/
@[noinline, specialize] def k16RR (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (io ia ib : USize) (ha : Fits out ia 15) (hb : Fits out ib 15) : ByteArray :=
  lanes16 f (fun k hk ↦ rd out ia k ha hk) (fun k hk ↦ rd out ib k hb hk) out io

/-- `f` on words `ia, …` of the registers and `ib, …` of `e` into words `io, …`. -/
@[noinline, specialize] def k16RX (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (e : @& ByteArray) (io ia ib : USize) (ha : Fits out ia 15) (hb : Fits e ib 15) :
    ByteArray :=
  lanes16 f (fun k hk ↦ rd out ia k ha hk) (fun k hk ↦ rd e ib k hb hk) out io

/-- `f` on words `ia, …` of `e` and `ib, …` of the registers into words `io, …`. -/
@[noinline, specialize] def k16XR (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (e : @& ByteArray) (io ia ib : USize) (ha : Fits e ia 15) (hb : Fits out ib 15) :
    ByteArray :=
  lanes16 f (fun k hk ↦ rd e ia k ha hk) (fun k hk ↦ rd out ib k hb hk) out io

/-- `f` on words `ia, …` of `ea` and `ib, …` of `eb` into words `io, …`. -/
@[noinline, specialize] def k16XX (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (ea eb : @& ByteArray) (io ia ib : USize) (ha : Fits ea ia 15) (hb : Fits eb ib 15) :
    ByteArray :=
  lanes16 f (fun k hk ↦ rd ea ia k ha hk) (fun k hk ↦ rd eb ib k hb hk) out io

/-- `f` on words `ia, …` of the registers and the word `c` into words `io, …`. -/
@[noinline, specialize] def k16RW (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (io ia : USize) (c : UInt32) (ha : Fits out ia 15) : ByteArray :=
  lanes16 f (fun k hk ↦ rd out ia k ha hk) (fun _ _ ↦ c) out io

/-- `f` on words `ia, …` of `e` and the word `c` into words `io, …`. -/
@[noinline, specialize] def k16XW (f : UInt32 → UInt32 → UInt32) (out : ByteArray)
    (e : @& ByteArray) (io ia : USize) (c : UInt32) (ha : Fits e ia 15) : ByteArray :=
  lanes16 f (fun k hk ↦ rd e ia k ha hk) (fun _ _ ↦ c) out io

theorem size_lanes16 (f : UInt32 → UInt32 → UInt32) (x y : (k : Nat) → k ≤ 15 → UInt32)
    (out : ByteArray) (io : USize) : (lanes16 f x y out io).size = out.size := by
  simp only [lanes16, write16U, CompPoly.CPolynomial.NTTFast.Packed.Native.size_storeWords]

/-! ### Passes over a block

A pass runs a kernel on `n` groups of sixteen words, the offsets advancing by sixteen, in a buffer
of `S` bytes whose bounds were checked once for the whole pass. An operand is read from the buffer
itself (`ra`), or from another buffer (`ea`, `eb`). -/

/-- The bound of an operand's buffer: the buffer's own `S` bytes, or `e`'s. -/
abbrev bnd (self : Bool) (S : Nat) (e : ByteArray) : Nat := if self then S else e.size

theorem fits_grp {b : ByteArray} {i n : Nat} (h : 4 * (i + 16 * (n + 1)) ≤ b.size)
    (hs : b.size < USize.size) : Fits b (USize.ofNatLT i (by omega)) 15 := by
  simp only [Fits, USize.toNat_ofNatLT]; omega

theorem size_k16RR (f : UInt32 → UInt32 → UInt32) (out : ByteArray) (io ia ib ha hb) :
    (k16RR f out io ia ib ha hb).size = out.size := size_lanes16 ..
theorem size_k16RX (f : UInt32 → UInt32 → UInt32) (out e : ByteArray) (io ia ib ha hb) :
    (k16RX f out e io ia ib ha hb).size = out.size := size_lanes16 ..
theorem size_k16XR (f : UInt32 → UInt32 → UInt32) (out e : ByteArray) (io ia ib ha hb) :
    (k16XR f out e io ia ib ha hb).size = out.size := size_lanes16 ..
theorem size_k16XX (f : UInt32 → UInt32 → UInt32) (out ea eb : ByteArray) (io ia ib ha hb) :
    (k16XX f out ea eb io ia ib ha hb).size = out.size := size_lanes16 ..
theorem size_k16RW (f : UInt32 → UInt32 → UInt32) (out : ByteArray) (io ia c ha) :
    (k16RW f out io ia c ha).size = out.size := size_lanes16 ..
theorem size_k16XW (f : UInt32 → UInt32 → UInt32) (out e : ByteArray) (io ia c ha) :
    (k16XW f out e io ia c ha).size = out.size := size_lanes16 ..

theorem bnd_true {ra : Bool} {S : Nat} {e : ByteArray} (h : ra = true) : bnd ra S e = S := by
  simp only [bnd, h, ite_true]

theorem bnd_false {ra : Bool} {S : Nat} {e : ByteArray} (h : ¬ra = true) :
    bnd ra S e = e.size := by
  simp only [bnd, h, Bool.false_eq_true, ite_false]

/-- `f` on `n` groups from words `ia` of `a` (the buffer itself if `ra`, else `ea`) and `ib` of `b`
(the buffer itself if `rb`, else `eb`) into the buffer from `io`. -/
@[specialize] def groupsBin (f : UInt32 → UInt32 → UInt32) (ea eb : @& ByteArray) (ra rb : Bool)
    (S : Nat) (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size) :
    (n io ia ib : Nat) → (out : ByteArray) → out.size = S → 4 * (io + 16 * n) ≤ S →
      4 * (ia + 16 * n) ≤ bnd ra S ea → 4 * (ib + 16 * n) ≤ bnd rb S eb → ByteArray
  | 0, _, _, _, out, _, _, _, _ => out
  | n + 1, io, ia, ib, out, hout, hd, ha, hb =>
    have hs : out.size < USize.size := by omega
    let next (out' : ByteArray) (h' : out'.size = S) : ByteArray :=
      groupsBin f ea eb ra rb S hS hEa hEb n (io + 16) (ia + 16) (ib + 16) out' h' (by omega)
        (by omega) (by omega)
    let iou := USize.ofNatLT io (by omega)
    if hra : ra = true then
      have ha' : 4 * (ia + 16 * (n + 1)) ≤ out.size := by rw [bnd_true hra] at ha; omega
      let iau := USize.ofNatLT ia (by omega)
      if hrb : rb = true then
        have hb' : 4 * (ib + 16 * (n + 1)) ≤ out.size := by rw [bnd_true hrb] at hb; omega
        next (k16RR f out iou iau (USize.ofNatLT ib (by omega)) (fits_grp ha' hs)
          (fits_grp hb' hs)) (by rw [size_k16RR, hout])
      else
        have hb' : 4 * (ib + 16 * (n + 1)) ≤ eb.size := by rw [bnd_false hrb] at hb; omega
        next (k16RX f out eb iou iau (USize.ofNatLT ib (by omega)) (fits_grp ha' hs)
          (fits_grp hb' hEb)) (by rw [size_k16RX, hout])
    else
      have ha' : 4 * (ia + 16 * (n + 1)) ≤ ea.size := by rw [bnd_false hra] at ha; omega
      let iau := USize.ofNatLT ia (by omega)
      if hrb : rb = true then
        have hb' : 4 * (ib + 16 * (n + 1)) ≤ out.size := by rw [bnd_true hrb] at hb; omega
        next (k16XR f out ea iou iau (USize.ofNatLT ib (by omega)) (fits_grp ha' hEa)
          (fits_grp hb' hs)) (by rw [size_k16XR, hout])
      else
        have hb' : 4 * (ib + 16 * (n + 1)) ≤ eb.size := by rw [bnd_false hrb] at hb; omega
        next (k16XX f out ea eb iou iau (USize.ofNatLT ib (by omega)) (fits_grp ha' hEa)
          (fits_grp hb' hEb)) (by rw [size_k16XX, hout])

/-- `f` on `n` groups from words `ia` of `a` (the buffer itself if `ra`, else `ea`) and the word
`c` into the buffer from `io`. -/
@[specialize] def groupsWord (f : UInt32 → UInt32 → UInt32) (ea : @& ByteArray) (ra : Bool)
    (c : UInt32) (S : Nat) (hS : S < USize.size) (hEa : ea.size < USize.size) :
    (n io ia : Nat) → (out : ByteArray) → out.size = S → 4 * (io + 16 * n) ≤ S →
      4 * (ia + 16 * n) ≤ bnd ra S ea → ByteArray
  | 0, _, _, out, _, _, _ => out
  | n + 1, io, ia, out, hout, hd, ha =>
    have hs : out.size < USize.size := by omega
    let next (out' : ByteArray) (h' : out'.size = S) : ByteArray :=
      groupsWord f ea ra c S hS hEa n (io + 16) (ia + 16) out' h' (by omega) (by omega)
    let iou := USize.ofNatLT io (by omega)
    if hra : ra = true then
      have ha' : 4 * (ia + 16 * (n + 1)) ≤ out.size := by rw [bnd_true hra] at ha; omega
      next (k16RW f out iou (USize.ofNatLT ia (by omega)) c (fits_grp ha' hs))
        (by rw [size_k16RW, hout])
    else
      have ha' : 4 * (ia + 16 * (n + 1)) ≤ ea.size := by rw [bnd_false hra] at ha; omega
      next (k16XW f out ea iou (USize.ofNatLT ia (by omega)) c (fits_grp ha' hEa))
        (by rw [size_k16XW, hout])

theorem size_groupsBin (f : UInt32 → UInt32 → UInt32) (ea eb : ByteArray) (ra rb : Bool) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size) :
    ∀ n io ia ib out hout hd ha hb,
      (groupsBin f ea eb ra rb S hS hEa hEb n io ia ib out hout hd ha hb).size = S
  | 0, _, _, _, _, hout, _, _, _ => hout
  | n + 1, io, ia, ib, out, hout, hd, ha, hb => by
    simp only [groupsBin]
    split <;> (try split) <;> exact size_groupsBin f ea eb ra rb S hS hEa hEb n _ _ _ _ _ _ _ _

theorem size_groupsWord (f : UInt32 → UInt32 → UInt32) (ea : ByteArray) (ra : Bool) (c : UInt32)
    (S : Nat) (hS : S < USize.size) (hEa : ea.size < USize.size) :
    ∀ n io ia out hout hd ha, (groupsWord f ea ra c S hS hEa n io ia out hout hd ha).size = S
  | 0, _, _, _, hout, _, _ => hout
  | n + 1, io, ia, out, hout, hd, ha => by
    simp only [groupsWord]
    split <;> exact size_groupsWord f ea ra c S hS hEa n _ _ _ _ _ _

theorem size_write (b : ByteArray) (i : Nat) (x : UInt32) : (write b i x).size = b.size :=
  CompPoly.CPolynomial.NTTFast.Packed.Native.size_storeWords ..

/-- `f` word by word on words `k, …, k + n - 1` of a pass (`passBin`). -/
@[specialize] def tailBin (f : UInt32 → UInt32 → UInt32) (ea eb : @& ByteArray) (ra rb : Bool)
    (od oa ob : Nat) : (k n : Nat) → ByteArray → ByteArray
  | _, 0, out => out
  | k, n + 1, out =>
    let x := if ra then read out (oa + k) else read ea (oa + k)
    let y := if rb then read out (ob + k) else read eb (ob + k)
    tailBin f ea eb ra rb od oa ob (k + 1) n (write out (od + k) (f x y))

/-- `f` word by word on words `k, …, k + n - 1` of a pass (`passWord`). -/
@[specialize] def tailWord (f : UInt32 → UInt32 → UInt32) (ea : @& ByteArray) (ra : Bool)
    (c : UInt32) (od oa : Nat) : (k n : Nat) → ByteArray → ByteArray
  | _, 0, out => out
  | k, n + 1, out =>
    let x := if ra then read out (oa + k) else read ea (oa + k)
    tailWord f ea ra c od oa (k + 1) n (write out (od + k) (f x c))

theorem size_tailBin (f : UInt32 → UInt32 → UInt32) (ea eb : ByteArray) (ra rb : Bool)
    (od oa ob : Nat) : ∀ k n out, (tailBin f ea eb ra rb od oa ob k n out).size = out.size
  | _, 0, _ => rfl
  | k, n + 1, out => by rw [tailBin, size_tailBin, size_write]

theorem size_tailWord (f : UInt32 → UInt32 → UInt32) (ea : ByteArray) (ra : Bool) (c : UInt32)
    (od oa : Nat) : ∀ k n out, (tailWord f ea ra c od oa k n out).size = out.size
  | _, 0, _ => rfl
  | k, n + 1, out => by rw [tailWord, size_tailWord, size_write]

/-- `f` on `B` words from `oa` of `a` (the buffer itself if `ra`, else `ea`) and from `ob` of `b`
(the buffer itself if `rb`, else `eb`) into the buffer from `od`: whole groups of sixteen, then word
by word. -/
@[specialize] def passBin (f : UInt32 → UInt32 → UInt32) (ea eb : @& ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size) (od : Nat)
    (ra : Bool) (oa : Nat) (rb : Bool) (ob : Nat) (B : Nat) (regs : ByteArray)
    (hr : regs.size = S) : ByteArray :=
  let G := B / 16
  if h : 4 * (od + 16 * G) ≤ S ∧ 4 * (oa + 16 * G) ≤ bnd ra S ea ∧
      4 * (ob + 16 * G) ≤ bnd rb S eb then
    tailBin f ea eb ra rb od oa ob (16 * G) (B - 16 * G)
      (groupsBin f ea eb ra rb S hS hEa hEb G od oa ob regs hr h.1 h.2.1 h.2.2)
  else tailBin f ea eb ra rb od oa ob 0 B regs

/-- `f` on `B` words from `oa` of the buffer itself (if `ra`) or `ea`, and the word `c`, into the
buffer from `od`. -/
@[specialize] def passWord (f : UInt32 → UInt32 → UInt32) (ea : @& ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (od : Nat) (ra : Bool) (oa : Nat)
    (c : UInt32) (B : Nat) (regs : ByteArray) (hr : regs.size = S) : ByteArray :=
  let G := B / 16
  if h : 4 * (od + 16 * G) ≤ S ∧ 4 * (oa + 16 * G) ≤ bnd ra S ea then
    tailWord f ea ra c od oa (16 * G) (B - 16 * G)
      (groupsWord f ea ra c S hS hEa G od oa regs hr h.1 h.2)
  else tailWord f ea ra c od oa 0 B regs

theorem size_passBin (f : UInt32 → UInt32 → UInt32) (ea eb : ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size) (od : Nat)
    (ra : Bool) (oa : Nat) (rb : Bool) (ob B : Nat) (regs : ByteArray) (hr : regs.size = S) :
    (passBin f ea eb S hS hEa hEb od ra oa rb ob B regs hr).size = S := by
  unfold passBin
  dsimp only
  split
  · rw [size_tailBin]; exact size_groupsBin ..
  · rw [size_tailBin]; exact hr

theorem size_passWord (f : UInt32 → UInt32 → UInt32) (ea : ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (od : Nat) (ra : Bool) (oa : Nat)
    (c : UInt32) (B : Nat) (regs : ByteArray) (hr : regs.size = S) :
    (passWord f ea S hS hEa od ra oa c B regs hr).size = S := by
  unfold passWord
  dsimp only
  split
  · rw [size_tailWord]; exact size_groupsWord ..
  · rw [size_tailWord]; exact hr

/-! ### Running a program on a block -/

/-- The trace's current rows on a block: column `c` at words `cb + c · cs` of `buf`. -/
structure View where
  buf : ByteArray
  cb : Nat
  cs : Nat

/-- A matrix's columns in blocks of rows: entry `(r, c)` is word `r % rows` of
`cols[r / rows * width + c]`. -/
structure Cols where
  cols : Array ByteArray
  width : Nat
  rows : Nat

/-- Entry `(r, c)` of columns in blocks of rows. -/
@[inline] def Cols.at (m : @& Cols) (r c : Nat) : UInt32 :=
  read (m.cols.getD (r / m.rows * m.width + c) .empty) (r % m.rows)

/-- What a program loads on a block of `B` rows from row `r0`: the trace, the preprocessed trace
and the permutation trace as columns, with the next row of row `r` at `next[r]`, and the block's
current rows of the last two transposed (`prepT`, `permT`: column `c` at words `c B`); the
periodic columns, one buffer each; and the selectors. -/
structure Loads where
  main : Cols
  prep : Cols
  prepT : ByteArray
  perm : Cols
  permT : ByteArray
  r0 : Nat
  next : Array Nat
  per : Array ByteArray
  first : ByteArray
  last : ByteArray
  trans : ByteArray

/-- A block's accumulators and registers, `S` bytes each: accumulator `j` the `j`-th, register `r`
the `(4 + r)`-th. -/
abbrev Regs (S : Nat) := Array {b : ByteArray // b.size = S}

/-- Buffer `i` of the registers, empty beyond them. -/
def regBuf {S : Nat} (regs : @& Regs S) (i : Nat) : ByteArray :=
  match regs[i]? with
  | some r => r.1
  | none => .empty

theorem size_regBuf {S : Nat} (regs : Regs S) (i : Nat) : (regBuf regs i).size ≤ S := by
  unfold regBuf
  split
  · rename_i r _; exact Nat.le_of_eq r.2
  · simp only [ByteArray.size_empty, Nat.zero_le]

/-- Update buffer `i` of the registers in place. -/
@[inline] def modReg {S : Nat} (regs : Regs S) (i : Nat)
    (f : (b : ByteArray) → b.size = S → ByteArray) (hf : ∀ b h, (f b h).size = S) : Regs S :=
  regs.modify i fun r ↦ ⟨f r.1 r.2, hf r.1 r.2⟩

variable {F : Type}

/-- An operand read from buffer `t` of the registers, written in place: register `t - 4`. -/
def Opd.isReg (t : Nat) : Opd F → Bool
  | .reg r => 4 + r == t
  | _ => false

/-- The buffer an operand of an instruction writing buffer `d` of the registers reads from: another
register's, or the view's; empty for buffer `d` itself, which is updated in place. -/
def Opd.buf {S : Nat} (d : Nat) (regs : @& Regs S) (v : @& View) : Opd F → ByteArray
  | .reg r => if 4 + r == d then .empty else regBuf regs (4 + r)
  | _ => v.buf

/-- The operand's first word in its buffer: `0` for a register, `cb + c · cs` for a column. -/
@[inline] def Opd.off (v : @& View) : Opd F → Nat
  | .reg _ => 0
  | .cur c => v.cb + c * v.cs
  | .const _ => 0

theorem size_opdBuf {S : Nat} (d : Nat) (regs : Regs S) (v : View) (a : Opd F)
    (hS : S < USize.size) (hE : v.buf.size < USize.size) : (a.buf d regs v).size < USize.size := by
  cases a with
  | reg r =>
    simp only [Opd.buf]
    split
    · simp only [ByteArray.size_empty]; omega
    · exact Nat.lt_of_le_of_lt (size_regBuf ..) hS
  | _ => exact hE

/-- Copy `B` words from word `o` of `src` into the buffer. -/
def copyWords (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (src : @& ByteArray) (o B : Nat) : ByteArray :=
  if hE : src.size < USize.size then
    passBin (fun x _ ↦ x) src src S hS hE hE 0 false o false o B regs hr
  else regs

theorem size_copyWords (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (src : ByteArray) (o B : Nat) : (copyWords S hS regs hr src o B).size = S := by
  unfold copyWords
  split
  · exact size_passBin ..
  · exact hr

/-- `B` copies of the word `c` in the buffer. -/
def fillWord (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (c : UInt32) (B : Nat) : ByteArray :=
  passWord (fun _ c ↦ c) .empty S hS (by simp only [ByteArray.size_empty]; omega) 0 true 0 c B
    regs hr

theorem size_fillWord (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (c : UInt32) (B : Nat) : (fillWord S hS regs hr c B).size = S :=
  size_passWord ..

/-- Column `c` of columns `m` at the rows `next[r0 + k]`, into the buffer, word by word. -/
def nextInto (m : @& Cols) (c : Nat) (next : @& Array Nat) (r0 : Nat) :
    (k n : Nat) → ByteArray → ByteArray
  | _, 0, out => out
  | k, n + 1, out =>
    nextInto m c next r0 (k + 1) n (write out k (m.at (next.getD (r0 + k) 0) c))

theorem size_nextInto (m : Cols) (c : Nat) (next : Array Nat) (r0 : Nat) :
    ∀ k n out, (nextInto m c next r0 k n out).size = out.size
  | _, 0, _ => rfl
  | k, n + 1, out => by rw [nextInto, size_nextInto, size_write]

/-- Load a source into the buffer. -/
def loadSrc (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (L : @& Loads) (B : Nat) : Src → ByteArray
  | .next c => nextInto L.main c L.next L.r0 0 B regs
  | .prepCur c => copyWords S hS regs hr L.prepT (c * B) B
  | .prepNext c => nextInto L.prep c L.next L.r0 0 B regs
  | .permCur c => copyWords S hS regs hr L.permT (c * B) B
  | .permNext c => nextInto L.perm c L.next L.r0 0 B regs
  | .periodic j =>
    match L.per[j]? with
    | some c => copyWords S hS regs hr c L.r0 B
    | none => fillWord S hS regs hr 0 B
  | .isFirstRow => copyWords S hS regs hr L.first L.r0 B
  | .isLastRow => copyWords S hS regs hr L.last L.r0 B
  | .isTransition => copyWords S hS regs hr L.trans L.r0 B

theorem size_loadSrc (S : Nat) (hS : S < USize.size) (regs : ByteArray) (hr : regs.size = S)
    (L : Loads) (B : Nat) (s : Src) : (loadSrc S hS regs hr L B s).size = S := by
  cases s <;> simp only [loadSrc, size_nextInto, hr] <;> try exact size_copyWords ..
  split
  · exact size_copyWords ..
  · exact size_fillWord ..

variable (p : ℕ) [Mont32Field p]

/-- The word operation of an operation. -/
@[inline] def Op.word : Op → UInt32 → UInt32 → UInt32
  | .add => CompPoly.CPolynomial.NTTFast.Packed.add p
  | .sub => CompPoly.CPolynomial.NTTFast.Packed.sub p
  | .mul => CompPoly.CPolynomial.NTTFast.Packed.mul p

/-- `o` on an operand (`a`'s buffer, offset and whether it is the destination itself) and the
constant `c` on the right, into the buffer: a product by two is a sum. -/
def constPass (o : Op) (ea : @& ByteArray) (S : Nat) (hS : S < USize.size)
    (hEa : ea.size < USize.size) (ra : Bool) (oa : Nat) (c : FastField p) (B : Nat)
    (regs : ByteArray) (hr : regs.size = S) : ByteArray :=
  match o with
  | .mul =>
    if c = 2 then passBin (add p) ea ea S hS hEa hEa 0 ra oa ra oa B regs hr
    else passWord (mul p) ea S hS hEa 0 ra oa c.val B regs hr
  | o => passWord (Op.word p o) ea S hS hEa 0 ra oa c.val B regs hr

theorem size_constPass (o : Op) (ea : ByteArray) (S : Nat) (hS : S < USize.size)
    (hEa : ea.size < USize.size) (ra : Bool) (oa : Nat) (c : FastField p) (B : Nat)
    (regs : ByteArray) (hr : regs.size = S) :
    (constPass p o ea S hS hEa ra oa c B regs hr).size = S := by
  unfold constPass
  split
  · split
    · exact size_passBin ..
    · exact size_passWord ..
  · exact size_passWord ..

/-- An operation on two operands into register `d`'s buffer: the operands' buffers, offsets and
whether they are `d` itself. -/
def binPass (o : Op) (d : Nat) (a b : Opd (FastField p)) (ea eb : @& ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size)
    (oa ob B : Nat) (regs : ByteArray) (hr : regs.size = S) : ByteArray :=
  match a, b with
  | .const x, .const y => fillWord S hS regs hr (Op.word p o x.val y.val) B
  | a, .const y => constPass p o ea S hS hEa (a.isReg (4 + d)) oa y B regs hr
  | .const x, b =>
    match o with
    | .sub => passWord (fun x c ↦ sub p c x) eb S hS hEb 0 (b.isReg (4 + d)) ob x.val B regs hr
    | o => constPass p o eb S hS hEb (b.isReg (4 + d)) ob x B regs hr
  | a, b =>
    passBin (Op.word p o) ea eb S hS hEa hEb 0 (a.isReg (4 + d)) oa (b.isReg (4 + d)) ob B regs hr

theorem size_binPass (o : Op) (d : Nat) (a b : Opd (FastField p)) (ea eb : ByteArray) (S : Nat)
    (hS : S < USize.size) (hEa : ea.size < USize.size) (hEb : eb.size < USize.size)
    (oa ob B : Nat) (regs : ByteArray) (hr : regs.size = S) :
    (binPass p o d a b ea eb S hS hEa hEb oa ob B regs hr).size = S := by
  unfold binPass
  split
  · exact size_fillWord ..
  · exact size_constPass ..
  · split
    · exact size_passWord ..
    · exact size_constPass ..
  · exact size_passBin ..

/-- Accumulator `j` plus an operand (`ea` from `oa`, or the constant `c`) times the word `w`. -/
def accPass (a : Opd (FastField p)) (ea : @& ByteArray) (S : Nat) (hS : S < USize.size)
    (hEa : ea.size < USize.size) (oa : Nat) (w : UInt32) (B : Nat) (regs : ByteArray)
    (hr : regs.size = S) : ByteArray :=
  match a with
  | .const c => passWord (fun x c ↦ add p x (mul p c w)) ea S hS hEa 0 true 0 c.val B regs hr
  | _ => passBin (fun x y ↦ add p x (mul p y w)) ea ea S hS hEa hEa 0 true 0 false oa B regs hr

theorem size_accPass (a : Opd (FastField p)) (ea : ByteArray) (S : Nat) (hS : S < USize.size)
    (hEa : ea.size < USize.size) (oa : Nat) (w : UInt32) (B : Nat) (regs : ByteArray)
    (hr : regs.size = S) : (accPass p a ea S hS hEa oa w B regs hr).size = S := by
  unfold accPass
  split
  · exact size_passWord ..
  · exact size_passBin ..

/-- One instruction on a block of `B` rows, the registers of `S` bytes each: the trace's columns in
`v`, the loaded sources in `L`, the scalars and the weights' coordinates as words. -/
def execBlock (v : @& View) (L : @& Loads) (scal wts : @& Array (FastField p)) (B S : Nat)
    (hS : S < USize.size) (hE : v.buf.size < USize.size) (regs : Regs S) :
    Instr (FastField p) → Regs S
  | .load d s =>
    modReg regs (4 + d) (fun b h ↦ loadSrc S hS b h L B s) (fun _ _ ↦ size_loadSrc ..)
  | .scalar d i =>
    modReg regs (4 + d) (fun b h ↦ fillWord S hS b h (scal.getD i 0).val B)
      (fun _ _ ↦ size_fillWord ..)
  | .bin o d a b =>
    let ea := a.buf (4 + d) regs v
    let eb := b.buf (4 + d) regs v
    modReg regs (4 + d) (fun r h ↦ binPass p o d a b ea eb S hS
      (size_opdBuf (4 + d) regs v a hS hE) (size_opdBuf (4 + d) regs v b hS hE) (a.off v)
      (b.off v) B r h) (fun _ _ ↦ size_binPass ..)
  | .acc a w =>
    let ea := a.buf 0 regs v
    let hEa := size_opdBuf 0 regs v a hS hE
    let step (regs : Regs S) (j : Nat) : Regs S :=
      modReg regs j (fun r h ↦ accPass p a ea S hS hEa (a.off v) (wts.getD (4 * w + j) 0).val B r h)
        (fun _ _ ↦ size_accPass ..)
    step (step (step (step regs 0) 1) 2) 3

/-- A program's code on a block, the accumulators and registers in `regs`. -/
def runBlock {S : Nat} (code : @& Array (Instr (FastField p))) (v : @& View) (L : @& Loads)
    (scal wts : @& Array (FastField p)) (B : Nat) (hS : S < USize.size) (regs : Regs S) :
    Regs S :=
  if hE : v.buf.size < USize.size then
    code.foldl (fun regs ins ↦ execBlock p v L scal wts B S hS hE regs ins) regs
  else regs

/-- The accumulators cleared. -/
def clearAcc {S : Nat} (hS : S < USize.size) (B : Nat) (regs : Regs S) : Regs S :=
  let z (regs : Regs S) (j : Nat) : Regs S :=
    modReg regs j (fun r h ↦ fillWord S hS r h 0 B) (fun _ _ ↦ size_fillWord ..)
  z (z (z (z regs 0) 1) 2) 3

/-- `B` words of `b` from `o`. -/
def wordsAt (b : @& ByteArray) (o B : Nat) : ByteArray := b.extract (4 * o) (4 * (o + B))

/-- The outputs' words on a block after its run: a register's, a column's or a constant's. -/
def outWords {S : Nat} (outs : @& Array (Opd (FastField p))) (v : @& View) (regs : @& Regs S)
    (B : Nat) : Array ByteArray :=
  outs.map fun o ↦ match o with
    | .reg r => wordsAt (regBuf regs (4 + r)) 0 B
    | .cur c => wordsAt v.buf (v.cb + c * v.cs) B
    | .const x => Words.replicateWord x.val B

end CompStark.Stark.Prog
