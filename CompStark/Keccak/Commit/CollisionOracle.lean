/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Commit.Collision
public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! The collision game of the headline against a random oracle. The game is `Collision hash` on the
adversary's two byte strings; with the answers of a lazily sampled 256-bit random oracle it is
VCVio's random-oracle collision experiment, bounded by the birthday bound. -/

set_option autoImplicit false

@[expose] public section
namespace CompStark.Keccak.Commit
open OracleComp OracleSpec CollisionResistance
open scoped ENNReal

/-- Digests are finite through their fixed-width byte vector. -/
instance digestFintype : Fintype Digest := Fintype.ofEquiv _ (arrayVectorEquivFin UInt8 32).symm

/-- The digest carrier has exactly `2^256` elements. -/
theorem digest_fintype_card : Fintype.card Digest = 2 ^ 256 := by
  rw [Fintype.card_congr (arrayVectorEquivFin UInt8 32), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, ← pow_mul]

/-- The hash answers seen by the collision game: `left` hashes to `leftDigest`, every other input to
`rightDigest`. -/
def answered (left : ByteArray) (leftDigest rightDigest : Digest) : ByteArray → Digest :=
  Function.update (fun _ => rightDigest) left leftDigest

/-- The answered hash collides on the two inputs exactly when they differ and their answers agree. -/
theorem collision_answered (left right : ByteArray) (leftDigest rightDigest : Digest) :
    Collision (answered left leftDigest rightDigest) left right ↔
      left ≠ right ∧ leftDigest = rightDigest := by
  unfold Collision answered
  constructor
  · rintro ⟨different, same⟩
    rw [Function.update_self, Function.update_of_ne (Ne.symm different)] at same
    exact ⟨different, same⟩
  · rintro ⟨different, same⟩
    rw [Function.update_self, Function.update_of_ne (Ne.symm different)]
    exact ⟨different, same⟩

/-- The collision game against a random oracle: run the adversary, query both outputs, and decide the
generic collision predicate on the oracle's answers. -/
def collisionExperiment {t : ℕ} (A : BoundedROMCRAdversary ByteArray Digest t) :
    OracleComp (ROMHashSpec.cached ByteArray Digest)
      (Bool × QueryCache (ROMHashSpec.cached ByteArray Digest)) :=
  (simulateQ ROMHashSpec.cachingOracle (do
    let (left, right) ← A.run
    let leftDigest ← (ROMHashSpec ByteArray Digest).query left
    let rightDigest ← (ROMHashSpec ByteArray Digest).query right
    return decide (Collision (answered left leftDigest rightDigest) left right))).run ∅

/-- The collision game is VCVio's random-oracle collision experiment. -/
theorem collisionExperiment_eq {t : ℕ} (A : BoundedROMCRAdversary ByteArray Digest t) :
    collisionExperiment A = romCRExperiment A := by
  unfold collisionExperiment romCRExperiment
  congr 3
  funext pair
  obtain ⟨left, right⟩ := pair
  refine bind_congr fun leftDigest => bind_congr fun rightDigest => ?_
  exact congrArg pure (decide_eq_decide.mpr (collision_answered left right leftDigest rightDigest))

/-- The win probability of the collision game with uniformly distributed oracle answers. -/
noncomputable def collisionAdvantage {t : ℕ} (A : BoundedROMCRAdversary ByteArray Digest t) : ℝ≥0∞ :=
  letI : MeasurableSpace Digest := ⊤
  letI : UniformAnswerMeasure (ROMHashSpec.cached ByteArray Digest) :=
    UniformAnswerMeasure.ofFiniteNonempty _
  Pr{let z ← collisionExperiment A}[z.1 = true]

/-- A `t`-query adversary wins the Keccak-256 collision game against a random oracle with probability
at most `(t + 2) (t + 1) / 2²⁵⁷`, counting the game's two hash queries. -/
theorem collision_randomOracle_le {t : ℕ} (A : BoundedROMCRAdversary ByteArray Digest t) :
    collisionAdvantage A ≤ ((t + 2) * (t + 1) : ℕ) / (2 ^ 257 : ℝ≥0∞) := by
  have bound := romCRAdvantage_le_birthday A
  simp only [romCRAdvantage, ← collisionExperiment_eq] at bound
  rw [digest_fintype_card] at bound
  refine bound.trans_eq ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_succ']

end CompStark.Keccak.Commit
