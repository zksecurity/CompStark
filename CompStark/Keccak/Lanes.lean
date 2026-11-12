/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BinaryFields.Basic
public import CompStark.BinaryFields.Generator
public import VCVio.Algorithms.Keccak

/-!
# Keccak cells, lanes, and bytes

The lane order is `x + 5*y`, as in VCVio's permutation. Each lane is the polynomial-basis
64-bit word in little-endian byte order. The even and odd layouts differ only on rate cells
0 through 8; the capacity always occupies cells 9 through 12. The unused input half-cell is
ignored, whereas the unused output half-cell and every output top limb are zero.
-/

namespace CompStark.Keccak.Lanes

open CompStark.BinaryFields

@[expose] public section

/-- A complete Keccak state, indexed in VCVio's `x + 5*y` lane order. -/
abbrev KeccakState := Fin 25 → UInt64

/-- Convert a field lane to its 64-bit polynomial-basis word, without arithmetic casting. -/
def laneWord (a : K) : UInt64 := ⟨a.toBitVec⟩

/-- Convert a 64-bit lane word to the corresponding polynomial-basis field element. -/
def wordLane (a : UInt64) : K := BF64.ofBitVec a.toBitVec

/-- Word conversion preserves the exact field-lane bit pattern. -/
@[simp] theorem wordLane_laneWord (a : K) : wordLane (laneWord a) = a :=
  BF64.toBitVec_injective rfl

/-- Lane conversion preserves the exact 64-bit word. -/
@[simp] theorem laneWord_wordLane (a : UInt64) : laneWord (wordLane a) = a := rfl

/-- Unpack thirteen canonical cells using the selected rate alignment. -/
def cellsToState (odd : Bool) (cells : Fin 13 → E) : KeccakState := fun i ↦
  let shifted := if odd || decide (17 ≤ i.val) then i.val + 1 else i.val
  laneWord ((cells ⟨shifted / 2, by dsimp [shifted]; split <;> omega⟩).limb
    ⟨shifted % 2, by omega⟩)

/-- Pack the state into thirteen cells, setting the unused half-cell and top limbs to zero. -/
def stateToCells (odd : Bool) (state : KeccakState) : Fin 13 → E := fun c ↦
  if odd then
    if h : c.val = 0 then E.ofLimbs 0 (wordLane (state 0)) 0
    else E.ofLimbs (wordLane (state ⟨2 * c.val - 1, by omega⟩))
      (wordLane (state ⟨2 * c.val, by omega⟩)) 0
  else
    if h : c.val < 8 then
      E.ofLimbs (wordLane (state ⟨2 * c.val, by omega⟩))
        (wordLane (state ⟨2 * c.val + 1, by omega⟩)) 0
    else if h' : c.val = 8 then E.ofLimbs (wordLane (state 16)) 0 0
    else E.ofLimbs (wordLane (state ⟨2 * c.val - 1, by omega⟩))
      (wordLane (state ⟨2 * c.val, by omega⟩)) 0

/-- Packing and unpacking preserve all 25 lanes in either alignment. -/
@[simp] theorem cellsToState_stateToCells (odd : Bool) (state : KeccakState) :
    cellsToState odd (stateToCells odd state) = state := by
  funext i
  cases odd <;> fin_cases i <;> simp [cellsToState, stateToCells]

/-- Packed cells all have zero top limb. -/
theorem stateToCells_canonical (odd : Bool) (state : KeccakState) (c : Fin 13) :
    IsCanonical128 (stateToCells odd state c) := by
  unfold stateToCells
  split <;> split_ifs <;> exact limb_ofLimbs _ _ _ 2

/-- The unused low half-cell in odd output is zero. -/
@[simp] theorem stateToCells_odd_padding (state : KeccakState) :
    (stateToCells true state 0).limb 0 = 0 := rfl

/-- The unused high half-cell in even output is zero. -/
@[simp] theorem stateToCells_even_padding (state : KeccakState) :
    (stateToCells false state 8).limb 1 = 0 := rfl

/-- Serialize a state as 200 bytes: eight little-endian bytes per lane, in lane order. -/
def stateBytes (state : KeccakState) : ByteArray :=
  VCVio.Algorithms.Keccak.squeeze (Array.ofFn state) 200

/-- VCVio's byte extraction reads eight little-endian bytes from each lane. -/
private theorem squeeze_get (state : Array UInt64) (n k : ℕ) (hk : k < n) :
    (VCVio.Algorithms.Keccak.squeeze state n)[k]! =
      ((state[k / 8]! >>> ((k % 8) * 8).toUInt64) &&& 0xFF).toUInt8 := by
  rw [getElem!_pos (VCVio.Algorithms.Keccak.squeeze state n) k
    (by simpa only [VCVio.Algorithms.Keccak.squeeze_size] using hk)]
  exact Array.getElem_ofFn _

/-- The byte at `8*i + j` is bits `8*j` through `8*j+7` of lane `i`. -/
theorem stateBytes_get (state : KeccakState) (i : Fin 25) (j : Fin 8) :
    (stateBytes state)[8 * i.val + j.val]! =
      ((state i >>> (8 * j.val).toUInt64) &&& 0xFF).toUInt8 := by
  rw [stateBytes, squeeze_get _ _ _ (by omega)]
  have hd : (8 * i.val + j.val) / 8 = i.val := by omega
  have hm : (8 * i.val + j.val) % 8 = j.val := by omega
  rw [hd, hm, getElem!_pos (Array.ofFn state) i.val (by simp),
    Array.getElem_ofFn, Nat.mul_comm]

/-- A Keccak round has exactly 25 output lanes. -/
private theorem keccakRound_size (state : Array UInt64) (rc : UInt64) :
    (VCVio.Algorithms.Keccak.round state rc).size = 25 := by
  simp only [VCVio.Algorithms.Keccak.round, Array.size_set!, Array.size_map,
    List.size_toArray, List.length_range]

/-- The permutation preserves the complete 25-lane state shape. -/
theorem keccakArray_size (state : KeccakState) :
    (VCVio.Algorithms.Keccak.f1600 (Array.ofFn state)).size = 25 := by
  have h : ∀ (rounds : List ℕ) (s : Array UInt64), s.size = 25 →
      (rounds.foldl (fun a r ↦ VCVio.Algorithms.Keccak.round a
        VCVio.Algorithms.Keccak.roundConstants[r]!) s).size = 25 := by
    intro rounds
    induction rounds with
    | nil => intro s hs; exact hs
    | cons r rounds ih =>
      intro s _
      exact ih _ (keccakRound_size s _)
  exact h (List.range 24) _ Array.size_ofFn

/-- The VM permutation is VCVio's complete 24-round Keccak-f[1600], in the same lane order. -/
def keccakState (state : KeccakState) : KeccakState := fun i ↦
  (VCVio.Algorithms.Keccak.f1600 (Array.ofFn state))[i.val]!

/-- The Keccak instruction relation checks all input top limbs and the entire packed output. -/
def KeccakCells (oddIn oddOut : Bool) (inputs outputs : Fin 13 → E) : Prop :=
  (∀ c, IsCanonical128 (inputs c)) ∧
    ∀ c, outputs c = stateToCells oddOut (keccakState (cellsToState oddIn inputs)) c

/-- The cell relation has an executable equality check on its finite coordinates. -/
instance (oddIn oddOut : Bool) (inputs outputs : Fin 13 → E) :
    Decidable (KeccakCells oddIn oddOut inputs outputs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Read `n` consecutive exponent-addressed cells, failing on any invalid address. -/
def readCells (read : K → Option E) (fp base : K) : (n : ℕ) → Option (Fin n → E)
  | 0 => some Fin.elim0
  | n + 1 => do
    let head ← read (fp * base)
    let tail ← readCells read fp (g * base) n
    pure (Fin.cases head tail)

/-- Read the four independent cells, four tail cells, rate-end cell, then four capacity cells. -/
def readKeccakInputs (read : K → Option E) (fp : K) (om : Fin 4 → K)
    (otail ob8 ocap : K) : Option (Fin 13 → E) := do
  let m0 ← read (fp * om 0)
  let m1 ← read (fp * om 1)
  let m2 ← read (fp * om 2)
  let m3 ← read (fp * om 3)
  let tail ← readCells read fp otail 4
  let b8 ← read (fp * ob8)
  let cap ← readCells read fp ocap 4
  pure fun c ↦ if h : c.val < 4 then ![m0, m1, m2, m3] ⟨c.val, h⟩
    else if h' : c.val < 8 then tail ⟨c.val - 4, by omega⟩
    else if c.val = 8 then b8 else cap ⟨c.val - 9, by omega⟩

end
end CompStark.Keccak.Lanes
