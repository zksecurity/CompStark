/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Draws
public import ArkLib.Interaction.Oracle.Security.BcsCertificate
public import ArkLib.Interaction.Oracle.Security.BcsCodec
public import ArkLib.Interaction.Oracle.Security.HashChainSqueeze
public import CompStark.Fs.MerkleLog
public import CompStark.Fs.StarkWords
public import CompStark.Ni.Seed
public import CompStark.Interaction.StarkStateRestoration

/-! # The STARK's challenges as Plonky3's duplex challenger draws them

Plonky3's verifier draws the STARK's challenges from its duplex challenger with `K` samples per
squeeze (`Draws.lean`): `α` from the first squeeze after the domain separator, the trace's Merkle
cap, the preprocessed commitment and the public values; `ζ` after the quotient's cap and the
out-of-domain grinding witness; the batching challenge after the PCS's domain separator, the
claimed values and the batching witness; each folding challenge `β` after the committed word's cap
and its witness, the first after FRI's domain separator; the query positions after the final
polynomial and the query witness, over as many squeezes as their samples take.

* `Setup.decoder`, `Statement.decoder`: the draws at every challenge (`extDraw`, `queryDraw`);
* `Setup.ratio`, `Statement.ratio`: the draws' ratios, the grinding's `powFraction`, bounding
  the draws against the laws of the certificate with Plonky3's query positions
  (`Setup.queryPositions`, the residues of uniform elements of `F`, of slack `1/p`;
  `Statement.bounded_decoder`);
* `Setup.layout`, `Statement.layout`: what the verifier observes and how often it squeezes, with
  each oracle message committed by the cap of its Merkle tree, `2 ^ min capHeight depth` digests
  (`CapOf`, `capCommit`), and opened to the word read off a snapshot of the Merkle hashes under it
  (`merkleCache`, `StarkWords.lean`). Its observations are prefix-free
  (`Statement.layout_prefixFree`, with the domain separator's injectivity on the admitted lengths,
  `2 ^ 8 ≤ |F|` and two-adicity below `2 ^ 64`);
* `Statement.Input`, `Statement.tail`: the statement's elements observed before `α`, the
  preprocessed commitment's, of a length the statement fixes, and the public values, told apart
  by their observation (`Statement.tail_injective`);
* `Statement.coinCount`: the squeezes of the most demanding challenge, the coins' size.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.Ni OracleComp OracleSpec CompPoly
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-! ### Observed elements -/

/-- An element of `𝕂` as Plonky3 observes it: its coefficients, lowest first. -/
noncomputable def extElems (x : 𝕂) : List F := List.ofFn (extEquiv.symm x)

/-- Elements of `𝕂` as Plonky3 observes them, in order. -/
noncomputable def extsElems {n : ℕ} (x : Fin n → 𝕂) : List F := (List.ofFn x).flatMap extElems

/-- The grinding witness of an extension draw, observed if it grinds. -/
def extWitnessElems : (bits : ℕ) → (extDraw (F := F) (EF := EF) (K := K) (m := m) bits).Witness →
    List F
  | 0, _ => []
  | _ + 1, w => [w]

/-- The grinding witness of the query draw, observed if it grinds. -/
def queryWitnessElems (top t : ℕ) :
    (bits : ℕ) → (queryDraw (F := F) (K := K) (m := m) top t bits).Witness → List F
  | 0, _ => []
  | _ + 1, w => [w]

/-! ### Prefix-free observations -/

omit [BaseField F] in
/-- Blocks of one length concatenate to a list of the blocks' count times that length. -/
theorem length_flatMap_const {β : Type} {g : β → List F} {L : ℕ} (hl : ∀ b, (g b).length = L) :
    ∀ l : List β, (l.flatMap g).length = l.length * L
  | [] => by simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | b :: l => by
    simp only [List.flatMap_cons, List.length_append, hl, length_flatMap_const hl l,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

omit [BaseField F] in
/-- Equally many blocks of one length, injectively observed, concatenate injectively. -/
theorem flatMap_inj {β : Type} {g : β → List F} {L : ℕ} (hl : ∀ b, (g b).length = L)
    (hg : Function.Injective g) :
    ∀ l l' : List β, l.length = l'.length → l.flatMap g = l'.flatMap g → l = l'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, h => by
    simp only [List.flatMap_cons] at h
    have h' := List.append_inj h (by rw [hl, hl])
    rw [hg h'.1, flatMap_inj hl hg l l' (by simpa only [List.length_cons,
      Nat.add_right_cancel_iff] using hlen) h'.2]

/-- An element of `𝕂` is observed as `d` elements. -/
theorem length_extElems (x : 𝕂) : (extElems (F := F) x).length = Challenge.d EF := by
  simp only [extElems, List.length_ofFn]

/-- An element of `𝕂` is told by its observation. -/
theorem extElems_injective : Function.Injective (extElems (F := F) (EF := EF)) := fun _ _ h ↦
  extEquiv.symm.injective (List.ofFn_injective h)

/-- `n` elements of `𝕂` are observed as `n d` elements. -/
theorem length_extsElems {n : ℕ} (x : Fin n → 𝕂) :
    (extsElems (F := F) x).length = n * Challenge.d EF := by
  rw [extsElems, length_flatMap_const length_extElems, List.length_ofFn]

/-- Elements of `𝕂` are told by their observation. -/
theorem extsElems_injective {n : ℕ} : Function.Injective (extsElems (F := F) (EF := EF) (n := n)) :=
  fun _ _ h ↦ List.ofFn_injective (flatMap_inj length_extElems extElems_injective _ _
    (by simp only [List.length_ofFn]) h)

/-- Elements of `𝕂` after a constant seed are observed prefix-free. -/
theorem prefixFree_extsElems {n : ℕ} (seed : List F) :
    PrefixFree fun x : Fin n → 𝕂 ↦ seed ++ extsElems x :=
  prefixFree_of_length (fun _ _ h ↦ extsElems_injective (List.append_cancel_left h))
    fun _ _ ↦ by simp only [List.length_append, length_extsElems]

/-- An extension draw's witness is told by its observation. -/
theorem extWitnessElems_injective (bits : ℕ) :
    Function.Injective (extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits) := by
  cases bits with
  | zero => exact fun _ _ _ ↦ rfl
  | succ b => exact fun x y h ↦ (List.cons.inj (show ([x] : List F) = [y] from h)).1

/-- An extension draw's witnesses are observed with one length. -/
theorem length_extWitnessElems (bits : ℕ) (w w') :
    (extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits w).length =
      (extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits w').length := by
  cases bits <;> rfl

/-- The query draw's witness is told by its observation. -/
theorem queryWitnessElems_injective (top t bits : ℕ) :
    Function.Injective (queryWitnessElems (F := F) (K := K) (m := m) top t bits) := by
  cases bits with
  | zero => exact fun _ _ _ ↦ rfl
  | succ b => exact fun x y h ↦ (List.cons.inj (show ([x] : List F) = [y] from h)).1

/-- The query draw's witnesses are observed with one length. -/
theorem length_queryWitnessElems (top t bits : ℕ) (w w') :
    (queryWitnessElems (F := F) (K := K) (m := m) top t bits w).length =
      (queryWitnessElems (F := F) (K := K) (m := m) top t bits w').length := by
  cases bits <;> rfl

/-- An extension draw's witness observation is prefix-free and suffix-free. -/
theorem fixFree_extWitnessElems (bits : ℕ) :
    PrefixFree (extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits) ∧
      SuffixFree (extWitnessElems (F := F) (EF := EF) (K := K) (m := m) bits) :=
  ⟨prefixFree_of_length (extWitnessElems_injective bits) (length_extWitnessElems bits),
    suffixFree_of_length (extWitnessElems_injective bits) (length_extWitnessElems bits)⟩

/-- The query draw's witness observation is prefix-free and suffix-free. -/
theorem fixFree_queryWitnessElems (top t bits : ℕ) :
    PrefixFree (queryWitnessElems (F := F) (K := K) (m := m) top t bits) ∧
      SuffixFree (queryWitnessElems (F := F) (K := K) (m := m) top t bits) :=
  ⟨prefixFree_of_length (queryWitnessElems_injective top t bits)
      (length_queryWitnessElems top t bits),
    suffixFree_of_length (queryWitnessElems_injective top t bits)
      (length_queryWitnessElems top t bits)⟩

/-! ### Merkle caps -/

/-- Snapshots of the Merkle hashes are compared classically: the snapshot protocol only needs
their equality decided, never computed. -/
noncomputable instance : DecidableEq (merkleSpec F).QueryCache := Classical.decEq _

/-- The cap of a Merkle tree of depth `k` with cap height `h`, as Plonky3's verifier accepts it:
`2 ^ min h k` digests. -/
abbrev CapOf (F : Type) (h k : ℕ) : Type := Vector (Digest F) (2 ^ min h k)

/-- A cap of `w` digests as Plonky3 observes it (`observeCap`): its digests' elements in
order. -/
def capOfElems {w : ℕ} (c : Vector (Digest F) w) : List F := capElems c.toArray

omit [BaseField F] in
/-- A cap of `w` digests is observed as `8 w` elements. -/
theorem length_capOfElems {w : ℕ} (c : Vector (Digest F) w) : (capOfElems c).length = 8 * w := by
  simp only [capOfElems, length_capElems, Vector.size_toArray]

omit [BaseField F] in
/-- A cap is told by its observation. -/
theorem capOfElems_injective {w : ℕ} : Function.Injective (capOfElems (F := F) (w := w)) :=
  fun a b hab ↦ Vector.toArray_inj.mp (Array.toList_inj.mp (flatMap_inj
    (g := Vector.toList) (fun _ ↦ Vector.length_toList) (fun x y hxy ↦ Vector.toList_inj.mp hxy)
    _ _ (by simp only [Array.length_toList, Vector.size_toArray]) hab))

variable [DecidableEq F] in
/-- A Merkle commitment of a tree of depth `k` with cap height `h`: its cap, observed after
`seed`, opened on a snapshot of the Merkle hashes by `read` (`merkleCache`). -/
def capCommit {Messages : Type} (h k : ℕ) (seed : List F)
    (read : Merkle.Cache F (Digest F) → Cap F → Messages) :
    Bcs.Commit F (merkleSpec F).QueryCache Messages where
  Com := CapOf F h k
  observe c := seed ++ capOfElems c
  «open» T c := read (merkleCache T) c.toArray

omit [BaseField F] in
/-- A Merkle commitment is observed prefix-free. -/
theorem prefixFree_capCommit [DecidableEq F] {Messages : Type} (h k : ℕ) (seed : List F)
    (read : Merkle.Cache F (Digest F) → Cap F → Messages) :
    PrefixFree (capCommit h k seed read).observe :=
  prefixFree_of_length (fun _ _ hab ↦ capOfElems_injective (List.append_cancel_left hab))
    fun a b ↦ by
      simp only [capCommit, List.length_append]
      rw [length_capOfElems (w := 2 ^ min h k) a, length_capOfElems (w := 2 ^ min h k) b]

/-! ### Squeezes -/

/-- `⌈s / K⌉` squeezes of `K` samples hold `s` samples. -/
theorem le_squeezesFor_mul (hK : 0 < K) (s : ℕ) : s ≤ squeezesFor K s * K := by
  have h1 := Nat.div_add_mod (s + K - 1) K
  have h2 := Nat.mod_lt (s + K - 1) hK
  simp only [squeezesFor]
  rw [Nat.mul_comm]
  omega

/-- More samples take at least as many squeezes. -/
theorem squeezesFor_mono {a b : ℕ} (h : a ≤ b) : squeezesFor K a ≤ squeezesFor K b :=
  Nat.div_le_div_right (by omega)

/-! ### FRI -/

section Fri
variable (K m) (top d t commitBits queryBits : ℕ)

/-- FRI's draws: the folding challenges with `commitBits` of grinding, the query positions with
`queryBits`. -/
noncomputable def friDecoder : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    Decoder (Coins F K m) (Fri.Interaction.publicCoin 𝕂 top d t s)
  | _, .final => fun _ => (queryDraw top t queryBits, PUnit.unit)
  | _, .fold _ _ _ rest => (extDraw commitBits, friDecoder rest)

/-- The ratios of FRI's draws: the folds' `powFraction F commitBits`, the queries'
`powFraction F queryBits`. -/
noncomputable def friRatio : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    Errors (Fri.Interaction.publicCoin 𝕂 top d t s)
  | _, .final => fun _ ↦ Iop.powFraction F queryBits
  | n, .fold _ _ _ rest => fun node ↦
      Sum.elim (fun _ ↦ Iop.powFraction F commitBits) (fun node ↦ friRatio rest node.2)
        (node : Fri.Interaction.Word 𝕂 n × (PUnit ⊕ (PUnit × Prefix PUnit
          (Fri.Interaction.publicCoin 𝕂 top d t rest)))).2

variable {top d t commitBits queryBits}

/-- FRI's draws are bounded by their ratios against the laws of FRI's certificate with the
positions' law `queryLaw`, when their samples fit the coins. -/
theorem bounded_friDecoder (hc : extSamples (EF := EF) commitBits ≤ m * K)
    (hq : querySamples t queryBits ≤ m * K) (hb : 2 ^ top ∣ Nat.card F - 1)
    (inputs : (m : ℕ) → Fin (2 ^ m) → 𝕂) (δ loss : ℝ) (hd : 0 < d) (hloss : 0 ≤ loss) :
    ∀ {n : ℕ} (hn : n ≤ top) (ω : Domain.SmoothCosetFftDomain n 𝕂)
      (s : Fri.Interaction.Schedule n) (j : ℕ) (f : Fri.Interaction.Word 𝕂 n)
      (C : Finset (Fin (2 ^ top))),
    Decoder.Bounded (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder (F := F) K m top d t commitBits queryBits s)
      (friRatio (F := F) top d t commitBits queryBits s)
      (Fri.Interaction.certificate top d t inputs δ loss (queryLaw top t hb) hd hloss hn ω s j f
        C).challenges
  | _, _, _, .final, _, _, _ => fun _ ↦ ⟨bounded_queryDraw top t queryBits hq, fun _ ↦ trivial⟩
  | n, hn, ω, .fold k hk inject rest, j, f, C => fun word ↦
    ⟨bounded_extDraw commitBits hc, fun β ↦ bounded_friDecoder hc hq hb inputs δ loss hd hloss
      ((Nat.sub_le n k).trans hn) (ω.subdomain k) rest (j + 1)
      (Fri.Interaction.foldNext hk ω word β (Fri.Interaction.injected inputs (n - k) inject))
      (Fri.Interaction.commitConsistent top f word C)⟩

/-- At least one element of `𝕂` is observed nonempty. -/
theorem extsElems_ne_nil {n : ℕ} (hn : 0 < n) (x : Fin n → 𝕂) : extsElems (F := F) x ≠ [] :=
  List.ne_nil_of_length_pos (by
    rw [length_extsElems]
    exact Nat.mul_pos hn (Challenge.params EF).d_pos)

variable (top d t commitBits queryBits) in
/-- FRI's layout with Merkle caps of height `h`: each committed word of `2 ^ n` points folded by
`2 ^ k` committed by the cap of its tree of depth `n - k`, the first after `seed`, opened to the
word of `2 ^ k`-element fibers under the cap (`friWordOf`), and its witness before its folding
challenge, one squeeze each; the final polynomial and the query witness before the query
positions, over their squeezes. -/
noncomputable def friLayout (h : ℕ) : {n : ℕ} → (s : Fri.Interaction.Schedule n) → List F →
    Bcs.Layout F (merkleSpec F).QueryCache (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder (F := F) K m top d t commitBits queryBits s)
  | _, .final, seed => (fun c ↦ seed ++ extsElems c,
      fun _ ↦ (squeezesFor K (querySamples t queryBits), queryWitnessElems top t queryBits,
        PUnit.unit))
  | n, .fold k _ _ rest, seed =>
    (capCommit h (n - k) seed fun cache cap ↦ friWordOf (EF := EF) cache h cap n k,
      (squeezesFor K (extSamples (EF := EF) commitBits), extWitnessElems commitBits,
        friLayout h rest []))

/-- FRI's draws read only the layout's squeezes. -/
theorem reads_friLayout (hK : 0 < K) (h : ℕ) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    (seed : List F) → HashChain.Decoder.Reads (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder (F := F) K m top d t commitBits queryBits s)
      (friLayout K m top d t commitBits queryBits h s seed).squeezes
  | _, .final, _ => fun _ ↦ ⟨fun c c' hc ↦ reads_queryDraw hK top t queryBits c c' hc, trivial⟩
  | _, .fold _ _ _ rest, _ => fun _ ↦
    ⟨fun c c' hc ↦ reads_extDraw hK commitBits c c' hc, reads_friLayout hK h rest []⟩

/-- FRI's layout is prefix-free. -/
theorem prefixFree_friLayout (h : ℕ) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    (seed : List F) →
    (friLayout K m top d t commitBits queryBits h s seed).PrefixFree
      (Fri.Interaction.publicCoin 𝕂 top d t s) (friDecoder K m top d t commitBits queryBits s)
  | _, .final, seed => ⟨prefixFree_extsElems seed,
      fun _ ↦ ⟨(fixFree_queryWitnessElems top t queryBits).1,
        (fixFree_queryWitnessElems top t queryBits).2, trivial⟩⟩
  | _, .fold _ _ _ rest, seed => ⟨prefixFree_capCommit _ _ seed _,
      (fixFree_extWitnessElems commitBits).1, (fixFree_extWitnessElems commitBits).2,
      prefixFree_friLayout h rest []⟩

/-- FRI's layout squeezes at most as often as `s` samples take, when its draws' samples are at
most `s`. -/
theorem friLayout_squeezes_le {s : ℕ} (hc : extSamples (EF := EF) commitBits ≤ s)
    (hq : querySamples t queryBits ≤ s) (h : ℕ) : {n : ℕ} → (sch : Fri.Interaction.Schedule n) →
    (seed : List F) → (node : Prefix PUnit (Fri.Interaction.publicCoin 𝕂 top d t sch)) →
    (friLayout K m top d t commitBits queryBits h sch seed).squeezes node ≤ squeezesFor K s
  | _, .final, _, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : (_ : Fin d → 𝕂) × (PUnit ⊕ (PUnit × Empty)))
    · exact squeezesFor_mono hq
    · exact nomatch node
  | n, .fold _ _ _ rest, _, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : Fri.Interaction.Word 𝕂 n × (PUnit ⊕ (PUnit ×
      Prefix PUnit (Fri.Interaction.publicCoin 𝕂 top d t rest))))
    · exact squeezesFor_mono hc
    · exact friLayout_squeezes_le hc hq h rest [] node

end Fri

end CompStark.Fs

/-! ### The STARK at a length -/

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.HashChain
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]
variable (K m : ℕ) (S : Setup EF)

local notation "𝕂" => Challenge.Spec EF

/-- The claimed values as Plonky3 observes them: the trace at `ζ` and `ζ ω`, the quotient chunks'
coordinates, the preprocessed trace at `ζ` and `ζ ω`. -/
noncomputable def openingsElems (o : Openings S) : List F :=
  extsElems o.traceAt ++ extsElems o.traceNext ++
    (List.ofFn fun c ↦ extsElems (o.quotientAt c)).flatten ++ extsElems o.preprocessedAt ++
      extsElems o.preprocessedNext

/-- The arities of FRI's folds, as Plonky3's verifier computes them. -/
def friArities : List ℕ :=
  Fri.foldSchedule S.params.maxLogArity (S.params.logBlowup + S.params.logFinalPolyLen)
    (S.logN + S.params.logBlowup) [S.logN + S.params.logBlowup]

/-- FRI's domain separator, observed before the first committed word. -/
def friSeed : List F :=
  DomainSeparator.friSeed F EF S.friArities (2 ^ S.params.logFinalPolyLen) S.params.commitPowBits
    S.params.queryPowBits S.params.numQueries (S.logN + S.params.logBlowup) S.params.logBlowup
    S.params.maxLogArity

/-- The PCS's domain separator, observed before the claimed values. -/
def pcsSeed : List F := DomainSeparator.pcsSeed F EF (Ni.pcsCountsS S) S.params.batchPowBits

/-- The law of the query positions Plonky3's verifier draws: the residues of uniform elements of
`F` on `L`, of slack `1/p` (`queryLaw`). -/
noncomputable def queryPositions {lookups : List (Stark.Lookup F)} (T : Setup EF lookups) :
    T.QueryPositions :=
  queryLaw (T.logN + T.params.logBlowup) T.params.numQueries
    (BaseField.two_pow_dvd_card_sub_one_of_le T.valid.twoAdic)

/-- The STARK's draws: `α` without grinding, `ζ`, the batching challenge, FRI's. -/
noncomputable def decoder : Decoder (Coins F K m) S.publicCoin :=
  (extDraw 0, (extDraw S.params.oodPowBits, fun _ ↦ (extDraw S.params.batchPowBits,
    friDecoder K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      S.params.numQueries S.params.commitPowBits S.params.queryPowBits (S.friSchedule []))))

/-- The STARK's layout with Merkle caps of height `capHeight`, as Plonky3's verifier observes
it: the cap of the trace's tree on `L`, opened to the trace under it (`traceMessageOf`); the cap
of the quotient's tree on `L`, opened to the chunks under it (`quotientMessageOf`); the PCS's
domain separator and the claimed values; FRI's (`friLayout`); with the draws' witnesses, and the
draws' squeezes. -/
noncomputable def layout :
    Bcs.Layout F (merkleSpec F).QueryCache S.publicCoin (S.decoder K m) :=
  (capCommit S.params.capHeight (S.logN + S.params.logBlowup) [] S.traceMessageOf,
    (squeezesFor K (extSamples (EF := EF) 0), extWitnessElems 0,
    (capCommit S.params.capHeight (S.logN + S.params.logBlowup) [] S.quotientMessageOf,
      (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits),
      extWitnessElems S.params.oodPowBits,
      (fun o ↦ S.pcsSeed ++ S.openingsElems o, fun _ ↦
        (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits),
          extWitnessElems S.params.batchPowBits,
          friLayout K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
            S.params.numQueries S.params.commitPowBits S.params.queryPowBits S.params.capHeight
            (S.friSchedule []) S.friSeed))))))

/-- The draws' ratios: `1` at `α`, the grinding's `powFraction` at `ζ`, the batching challenge,
FRI's folds and its queries. -/
noncomputable def ratio : Errors S.publicCoin := fun node ↦
  match (node : S.TraceMessage × (PUnit ⊕ (PUnit × (S.QuotientMessage × (PUnit ⊕
      (PUnit × ((_ : Openings S) × (PUnit ⊕ (PUnit × S.FriPrefix))))))))) with
  | ⟨_, .inl _⟩ => 1
  | ⟨_, .inr ⟨_, _, .inl _⟩⟩ => Iop.powFraction F S.params.oodPowBits
  | ⟨_, .inr ⟨_, _, .inr ⟨_, _, .inl _⟩⟩⟩ => Iop.powFraction F S.params.batchPowBits
  | ⟨_, .inr ⟨_, _, .inr ⟨_, _, .inr ⟨_, node⟩⟩⟩⟩ =>
      friRatio (F := F) (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
        S.params.numQueries S.params.commitPowBits S.params.queryPowBits (S.friSchedule []) node

variable {K m S}

/-- An extension draw reads at most `d + 1` samples. -/
theorem extSamples_le (bits : ℕ) : extSamples (EF := EF) bits ≤ Challenge.d EF + 1 := by
  simp only [extSamples]
  split <;> omega

/-- The query draw reads at most `t + 1` samples. -/
theorem querySamples_le (t bits : ℕ) : querySamples t bits ≤ t + 1 := by
  simp only [querySamples]
  split <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- The STARK's draws are bounded by their ratios against the laws of its certificate with
Plonky3's query positions, when the coins hold the most demanding challenge's samples. -/
theorem bounded_decoder (hs : Challenge.d EF + S.params.numQueries + 1 ≤ m * K)
    (publicValues : List F) (δ δ' : ℝ≥0) (hδ' : (δ' : ℝ) < 1 - S.rate) (loss : ℝ≥0) :
    Decoder.Bounded S.publicCoin (S.decoder K m) (S.ratio (F := F))
      (S.certificate publicValues δ δ' hδ' loss S.queryPositions).challenges := by
  have he (bits : ℕ) : extSamples (EF := EF) bits ≤ m * K := by
    have := extSamples_le (EF := EF) bits
    omega
  have h0 := bounded_extDraw (F := F) (EF := EF) (K := K) (m := m) 0 (he 0)
  rw [Sound.powFraction_zero] at h0
  exact fun T ↦ ⟨h0, fun α Q ↦ ⟨bounded_extDraw _ (he _), fun ζ o ↦ ⟨bounded_extDraw _ (he _),
    fun a ↦ bounded_friDecoder K m (he _)
      ((querySamples_le S.params.numQueries _).trans (by omega)) _ _ _ _ _ _ _ _ _ _ _ _⟩⟩⟩

/-- The STARK's draws read only the layout's squeezes. -/
theorem reads_decoder (hK : 0 < K) :
    HashChain.Decoder.Reads S.publicCoin (S.decoder K m) (S.layout (F := F) K m).squeezes :=
  fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK 0 c c' h, fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
    fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
      reads_friLayout K m hK _ (S.friSchedule []) S.friSeed⟩⟩⟩

/-- No challenge of the STARK squeezes more often than the most demanding challenge's samples
take. -/
theorem layout_squeezes_le (node : Prefix PUnit S.publicCoin) :
    (S.layout (F := F) K m).squeezes node ≤
      squeezesFor K (Challenge.d EF + S.params.numQueries + 1) := by
  have he (bits : ℕ) : extSamples (EF := EF) bits ≤ Challenge.d EF + S.params.numQueries + 1 :=
    (extSamples_le bits).trans (by omega)
  obtain ⟨_, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, node⟩⟩⟩⟩ := (node : S.TraceMessage × (PUnit ⊕
    (PUnit × (S.QuotientMessage × (PUnit ⊕ (PUnit × ((_ : Openings S) × (PUnit ⊕
      (PUnit × S.FriPrefix)))))))))
  · exact squeezesFor_mono (he 0)
  · exact squeezesFor_mono (he _)
  · exact squeezesFor_mono (he _)
  · exact friLayout_squeezes_le K m (he _)
      ((querySamples_le S.params.numQueries _).trans (by omega)) _ _ _ node

/-- The quotient chunks' claimed values are observed chunk by chunk. -/
theorem flatten_ofFn_extsElems {n k : ℕ} (q : Fin n → Fin k → 𝕂) :
    (List.ofFn fun c ↦ extsElems (F := F) (q c)).flatten = (List.ofFn q).flatMap extsElems := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- The claimed values are observed with one length. -/
theorem length_openingsElems (o o' : Openings S) :
    (S.openingsElems (F := F) o).length = (S.openingsElems o').length := by
  simp only [openingsElems, flatten_ofFn_extsElems, List.length_append, length_extsElems,
    length_flatMap_const length_extsElems, List.length_ofFn]

/-- The claimed values are told by their observation. -/
theorem openingsElems_injective : Function.Injective (S.openingsElems (F := F)) := by
  intro o o' h
  have hl (n : ℕ) (x y : Fin n → 𝕂) : (extsElems (F := F) x).length = (extsElems y).length := by
    simp only [length_extsElems]
  have hq : ((List.ofFn fun c ↦ extsElems (F := F) (o.quotientAt c)).flatten).length =
      ((List.ofFn fun c ↦ extsElems (F := F) (o'.quotientAt c)).flatten).length := by
    simp only [flatten_ofFn_extsElems, length_flatMap_const length_extsElems, List.length_ofFn]
  simp only [openingsElems] at h
  obtain ⟨h, h5⟩ := List.append_inj h (by simp only [List.length_append, length_extsElems, hq])
  obtain ⟨h, h4⟩ := List.append_inj h (by simp only [List.length_append, length_extsElems, hq])
  obtain ⟨h, h3⟩ := List.append_inj h (by simp only [List.length_append, length_extsElems])
  obtain ⟨h1, h2⟩ := List.append_inj h (hl _ _ _)
  rw [flatten_ofFn_extsElems, flatten_ofFn_extsElems] at h3
  have h3' := List.ofFn_injective (flatMap_inj length_extsElems extsElems_injective _ _
    (by simp only [List.length_ofFn]) h3)
  cases o
  cases o'
  simp only [Openings.mk.injEq]
  exact ⟨extsElems_injective h1, extsElems_injective h2, h3', extsElems_injective h4,
    extsElems_injective h5, funext fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩

/-- The STARK's layout is prefix-free. -/
theorem layout_prefixFree : (S.layout (F := F) K m).PrefixFree S.publicCoin (S.decoder K m) :=
  ⟨prefixFree_capCommit _ _ [] _, (fixFree_extWitnessElems 0).1, (fixFree_extWitnessElems 0).2,
    prefixFree_capCommit _ _ [] _, (fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
    prefixFree_of_length (fun _ _ h ↦ openingsElems_injective (List.append_cancel_left h))
      (fun a b ↦ by
        show (S.pcsSeed ++ S.openingsElems a).length = (S.pcsSeed ++ S.openingsElems b).length
        rw [List.length_append, List.length_append, length_openingsElems a b]),
    fun _ ↦ ⟨(fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
      prefixFree_friLayout K m _ _ _⟩⟩

end CompStark.Iop.Setup

/-! ### The STARK for a statement -/

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.HashChain
open scoped ENNReal NNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The number of elements Plonky3 observes for the preprocessed commitment: none without
preprocessed columns, otherwise the cap of the preprocessed trace's tree on `L`
(`preprocessedDigest`). -/
def digestLength : ℕ :=
  if C.air.preprocessedWidth = 0 then 0
  else 8 * 2 ^ min C.params.capHeight (C.preprocessedLogN + C.params.logBlowup)

/-- The statement's elements Plonky3 observes before `α`: the preprocessed commitment's elements,
of `digestLength`, and the public values. -/
abbrev Input : Type := {z : List F × List F // z.1.length = C.digestLength}

variable {C} in
/-- The statement's elements as observed: the preprocessed commitment's, then the public
values. -/
def tail (z : C.Input) : List F := z.1.1 ++ z.1.2

/-- The statement's elements are told by their observation. -/
theorem tail_injective : Function.Injective (tail (C := C)) := fun a b h ↦ by
  obtain ⟨h1, h2⟩ := List.append_inj h (a.2.trans b.2.symm)
  exact Subtype.ext (Prod.ext h1 h2)

/-- The squeezes of the most demanding challenge: an extension element after a grinding sample,
or the query positions after theirs. -/
def coinCount : ℕ := squeezesFor K (Challenge.d EF + C.params.numQueries + 1)

variable (m : ℕ)

/-- The draws: at the length the prover sends, the STARK's. -/
noncomputable def decoder : Decoder (Coins F K m) (C.publicCoin EF) :=
  fun n ↦ (C.setup EF n).decoder K m

/-- The layout: the STARK's domain separator, which carries the length the prover sends, then
the STARK's layout at that length. -/
noncomputable def layout :
    Bcs.Layout F (merkleSpec F).QueryCache (C.publicCoin EF) (C.decoder EF K m) :=
  (fun n ↦ starkSeedOf EF C.params C.air n.1, fun n ↦ (C.setup EF n).layout K m)

/-- The draws' ratios: at each length, the STARK's. -/
noncomputable def ratio : Errors (C.publicCoin EF) := fun node ↦ (C.setup EF node.1).ratio node.2

variable {C EF K}

/-- Each draw is bounded by its ratio against the laws of the statement's certificate with
Plonky3's query positions, when the coins hold the most demanding challenge. -/
theorem bounded_decoder (hK : 0 < K) (publicValues : List F) (δ δ' : ℕ → ℝ≥0)
    (hδ' : ∀ n, C.Admits n → (δ' n : ℝ) < 1 - C.rate) (loss : C.Length → ℝ≥0) :
    Decoder.Bounded (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)) (C.ratio EF)
      (certificate EF publicValues δ δ' hδ' loss
        fun n ↦ (C.setup EF n).queryPositions).challenges :=
  fun n ↦ (C.setup EF n).bounded_decoder (le_squeezesFor_mul hK _) _ _ _ _ _

/-- No challenge squeezes more often than the coins hold. -/
theorem squeezes_le (node : Prefix PUnit (C.publicCoin EF)) :
    (C.layout EF K (C.coinCount EF K)).squeezes node ≤ C.coinCount EF K :=
  (C.setup EF node.1).layout_squeezes_le node.2

/-- Each draw reads only the layout's squeezes. -/
theorem reads_decoder (hK : 0 < K) :
    HashChain.Decoder.Reads (C.publicCoin EF) (C.decoder EF K m) (C.layout EF K m).squeezes :=
  fun n ↦ (C.setup EF n).reads_decoder (hK := hK)

/-- The layout is prefix-free: the domain separator tells the admitted lengths apart, on a base
field of at least `2 ^ 8` elements with two-adicity below `2 ^ 64`. -/
theorem layout_prefixFree (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64) :
    (C.layout EF K m).PrefixFree (C.publicCoin EF) (C.decoder EF K m) := by
  have h64' (n : C.Length) : n.1 < 2 ^ 64 := by
    have := n.2.sound.twoAdic
    omega
  exact ⟨prefixFree_of_length (fun a b h ↦ Subtype.ext
      (DomainSeparator.starkSeedOf_inj EF h8 _ _ (h64' a) (h64' b) h))
    (fun a b ↦ DomainSeparator.length_starkSeedOf EF _ _ a.1 b.1),
    fun n ↦ (C.setup EF n).layout_prefixFree⟩

end CompStark.Iop.Statement
