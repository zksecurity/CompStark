/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Bytes

/-! Pure overwrite duplex from §8.4 and the pinned Rust prover/verifier. The state keeps
only capacity and pending items: output rate lanes never survive into the next input.
Grinding checks consume their own squeeze and never expose it as a protocol challenge. -/

namespace CompStark.Keccak.Transcript
open CompStark.BinaryFields CompStark.Keccak.Lanes CompStark.Keccak.Commit
@[expose] public section

/-- The two distinct nonzero domains in the fourth lane of an absorbed item. -/
inductive Item where
  /-- A transmitted field scalar, including either half of a digest. -/
  | scalar (value : E)
  /-- A grinding nonce; the verifier permits all three limbs. -/
  | nonce (value : E)

/-- Four lanes encoding one item, with domain 1 for scalars and 4 for nonces. -/
def Item.lanes : Item → List UInt64
  | .scalar x => [laneWord (x.limb 0), laneWord (x.limb 1), laneWord (x.limb 2), 1]
  | .nonce x => [laneWord (x.limb 0), laneWord (x.limb 1), laneWord (x.limb 2), 4]

/-- A padded rate input, valid for at most four pending items. -/
def rateBlock (items : List Item) : List UInt64 :=
  items.flatMap Item.lanes ++ List.replicate (16 - 4 * items.length) 0

/-- Decode one four-lane slot; zero padding is not an item. -/
def decodeSlot : List UInt64 → Option Item
  | [a, b, c, 1] => some (.scalar (E.ofLimbs (wordLane a) (wordLane b) (wordLane c)))
  | [a, b, c, 4] => some (.nonce (E.ofLimbs (wordLane a) (wordLane b) (wordLane c)))
  | _ => none

/-- Decode the occupied prefix of four rate slots; malformed or nonterminal padding fails. -/
def decodeRate : ℕ → List UInt64 → Option (List Item)
  | 0, [] => some []
  | 0, _ => none
  | n + 1, xs =>
      if xs.take 4 = [0, 0, 0, 0] then
        if xs = List.replicate (4 * (n + 1)) 0 then some [] else none
      else do
        let x ← decodeSlot (xs.take 4)
        let tail ← decodeRate n (xs.drop 4)
        pure (x :: tail)

/-- Each tagged item occupies exactly four lanes. -/
theorem Item.lanes_length (item : Item) : item.lanes.length = 4 := by
  cases item <;> rfl

/-- Decoding a tagged item recovers all three limbs and its scalar/nonce domain. -/
theorem decodeSlot_lanes (item : Item) : decodeSlot item.lanes = some item := by
  cases item <;> simp only [Item.lanes, decodeSlot, wordLane_laneWord, ofLimbs_limb]

/-- A nonzero domain lane keeps an occupied slot distinct from rate padding. -/
theorem Item.lanes_ne_zero (item : Item) : item.lanes ≠ [0, 0, 0, 0] := by
  cases item <;> simp [Item.lanes]

/-- An unoccupied rate consists entirely of zero slots. -/
theorem decodeRate_zeros (slots : ℕ) :
    decodeRate slots (List.replicate (4 * slots) 0) = some [] := by
  cases slots with
  | zero => rfl
  | succ slots =>
      have h : min 4 (4 * (slots + 1)) = 4 := by omega
      simp only [decodeRate, List.take_replicate, h,
        show List.replicate 4 (0 : UInt64) = [0,0,0,0] from rfl, ↓reduceIte]

/-- Decoding any bounded list of tagged items ignores exactly its trailing zero slots. -/
theorem decodeRate_padded (items : List Item) (slots : ℕ) (h : items.length ≤ slots) :
    decodeRate slots (items.flatMap Item.lanes ++
      List.replicate (4 * (slots - items.length)) 0) = some items := by
  induction items generalizing slots with
  | nil => simpa only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.sub_zero]
      using decodeRate_zeros slots
  | cons item items ih =>
      cases slots with
      | zero => simp only [List.length_cons] at h; omega
      | succ slots =>
          have hitems : items.length ≤ slots := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h
          have htail := ih slots hitems
          simp only [List.flatMap_cons, List.length_cons, Nat.add_sub_add_right,
            List.append_assoc]
          rw [decodeRate]
          have take : (item.lanes ++ (items.flatMap Item.lanes ++
              List.replicate (4 * (slots - items.length)) 0)).take 4 = item.lanes := by
            rw [← item.lanes_length, List.take_left]
          have drop : (item.lanes ++ (items.flatMap Item.lanes ++
              List.replicate (4 * (slots - items.length)) 0)).drop 4 =
                items.flatMap Item.lanes ++ List.replicate (4 * (slots - items.length)) 0 := by
            rw [← item.lanes_length, List.drop_left]
          rw [take, ite_eq_right item.lanes_ne_zero, decodeSlot_lanes, drop, htail]
          rfl

/-- Tags and zero padding uniquely recover the occupied rate prefix, including sent zeros. -/
theorem decodeRate_rateBlock (items : List Item) (h : items.length ≤ 4) :
    decodeRate 4 (rateBlock items) = some items := by
  have size : 16 - 4 * items.length = 4 * (4 - items.length) := by omega
  simpa only [rateBlock, size] using decodeRate_padded items 4 h

/-- Padded rate encoding is injective on lists of at most four items, before hashing. -/
theorem rateBlock_injective (a b : List Item) (ha : a.length ≤ 4) (hb : b.length ≤ 4)
    (h : rateBlock a = rateBlock b) : a = b := by
  have decoded := congrArg (decodeRate 4) h
  simpa only [decodeRate_rateBlock a ha, decodeRate_rateBlock b hb, Option.some.injEq] using decoded

/-- Capacity lanes 16–24 and at most four pending tagged scalars. -/
structure State where
  /-- Capacity carried from the preceding permutation. -/
  capacity : Fin 9 → UInt64
  /-- Items absorbed since that permutation. -/
  pending : List Item
  /-- Absorption flushes before inserting a fifth item. -/
  bounded : pending.length ≤ 4

/-- One permutation of padded pending items and the retained capacity. -/
def permutation (s : State) : KeccakState := keccakState fun i ↦
  if h : i.val < 16 then (rateBlock s.pending)[i.val]!
  else s.capacity ⟨i.val - 16, by omega⟩

/-- Every squeeze permutes independently, emits lanes 0–2, and clears the pending rate. -/
def squeeze (s : State) : E × State :=
  let out := permutation s
  (E.ofLimbs (wordLane (out 0)) (wordLane (out 1)) (wordLane (out 2)),
   ⟨fun i ↦ out ⟨16 + i.val, by omega⟩, [], by decide⟩)

/-- Compute the permutation array before storing its capacity lanes in the next state. -/
def squeezeExec (s : State) : E × State :=
  let rate := rateBlock s.pending
  let lanes := VCVio.Algorithms.Keccak.f1600 (Array.ofFn fun i : Fin 25 =>
    if h : i.val < 16 then rate[i.val]!
    else s.capacity ⟨i.val - 16, by omega⟩)
  (E.ofLimbs (wordLane lanes[0]!) (wordLane lanes[1]!) (wordLane lanes[2]!),
    ⟨fun i => lanes[16 + i.val]!, [], by decide⟩)

/-- Array-backed capacity shares one permutation while preserving every squeeze output. -/
@[csimp] theorem squeeze_code : squeeze = squeezeExec := rfl

/-- Absorb an item, first flushing four occupied slots if necessary. -/
def absorb (s : State) (item : Item) : State :=
  let base := if s.pending.length = 4 then (squeeze s).2 else s
  ⟨base.capacity, base.pending ++ [item], by
    dsimp [base]; split <;> simp_all only [List.length_append, List.length_singleton]
    · simp only [squeeze, List.length_nil]; omega
    · have := s.bounded; omega⟩

/-- Absorb a complete item stream, preserving its batching across message boundaries. -/
def absorbAll (s : State) (items : List Item) : State := items.foldl absorb s

/-- The IV binds the fixed ASCII version tag followed by the serialized bytecode bytes. -/
def programIV (bytecode : ByteArray) : Digest := hash ("leanvm-v1".toUTF8 ++ bytecode)

/-- Seed with IV words in lanes 0–3, public-input words in 4–7, all other lanes zero. -/
def seedDigests (iv publicInput : Digest) : State :=
  let words := (List.range 4).map (fun i ↦ readWord ⟨iv.toArray⟩ (8 * i)) ++
    (List.range 4).map (fun i ↦ readWord ⟨publicInput.toArray⟩ (8 * i))
  let out := keccakState fun i ↦ words[i.val]?.getD 0
  ⟨fun i ↦ out ⟨16 + i.val, by omega⟩, [], by decide⟩

/-- Materialize the seed permutation before storing the nine capacity lanes. -/
def seedDigestsExec (iv publicInput : Digest) : State :=
  let words := (List.range 4).map (fun i ↦ readWord ⟨iv.toArray⟩ (8 * i)) ++
    (List.range 4).map (fun i ↦ readWord ⟨publicInput.toArray⟩ (8 * i))
  let lanes := VCVio.Algorithms.Keccak.f1600
    (Array.ofFn fun i : Fin 25 => words[i.val]?.getD 0)
  ⟨fun i => lanes[16 + i.val]!, [], by decide⟩

/-- The array-backed seed has exactly the specified capacity and pending stream. -/
@[csimp] theorem seedDigests_code : seedDigests = seedDigestsExec := rfl

/-- Seed the leanVM statement before any proof message or challenge. -/
def seed (bytecode : ByteArray) (publicInput : Digest) : State :=
  seedDigests (programIV bytecode) publicInput

/-- Test the verifier's contiguous low-bit grinding window, saturating at 64 bits. -/
def lowBitsZero (bits : ℕ) (challenge : E) : Bool :=
  decide ((laneWord (challenge.limb 0)).toNat % 2 ^ (min bits 64) = 0)

/-- Verifier grinding step. Even a zero-bit grind consumes a tagged nonce and a squeeze.
The honest prover uses `(nonce,0,0)`; the verifier only requires nonce zero when bits is zero. -/
def grindCheck (s : State) (bits : ℕ) (nonce : E) : Bool × State :=
  let probe := squeeze (absorb s (.nonce nonce))
  (if bits = 0 then decide (nonce = 0) else lowBitsZero bits probe.1, probe.2)

/-- Replay events include discarded squeezes, so consecutive empty draws remain distinguishable. -/
inductive Event where
  /-- Absorption of one tagged item. -/
  | absorb (item : Item)
  /-- A permutation whose output may be a challenge or a discarded grinding test. -/
  | squeeze

/-- Deterministic replay, including prior challenges and discarded grinding outputs. -/
def replay (s : State) (events : List Event) : State :=
  events.foldl (fun s event ↦ match event with
    | .absorb item => absorb s item
    | .squeeze => (squeeze s).2) s

/-- Encoding of a nonce-bearing move: the checking squeeze is part of this move, not a coin node. -/
def grindEvents (nonce : E) : List Event := [.absorb (.nonce nonce), .squeeze]

/-- Grinding's state transition equals replay of its two deterministic events. -/
theorem grindCheck_state (s : State) (bits : ℕ) (nonce : E) :
    (grindCheck s bits nonce).2 = replay s (grindEvents nonce) := by rfl

end
end CompStark.Keccak.Transcript
