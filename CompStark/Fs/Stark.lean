/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Draws
public import CompStark.Fs.Codec
public import ArkLib.Interaction.Oracle.Security.HashChainSqueeze
public import CompStark.Ni.Seed
public import CompStark.Interaction.StarkStateRestoration

/-! # The STARK's challenges as Plonky3's duplex challenger draws them

Plonky3's verifier draws the STARK's challenges from its duplex challenger with `K` samples per
squeeze (`Draws.lean`): `α` from the first squeeze after the domain separator, the trace and the
public values; `ζ` after the quotient and the out-of-domain grinding witness; the batching
challenge after the PCS's domain separator, the claimed values and the batching witness; each
folding challenge `β` after the committed word and its witness, the first after FRI's domain
separator; the query positions after the final polynomial and the query witness, over as many
squeezes as their samples take. Here the commitments are the oracle messages themselves: a
committed word is observed in full where Plonky3 observes its Merkle cap.

* `Setup.decoder`, `Statement.decoder`: the draws at every challenge (`extDraw`, `queryDraw`);
* `Setup.ratio`, `Statement.ratio`: the draws' ratios, the grinding's `powFraction` and the query
  positions' bias, bounding the draws (`Statement.bounded_decoder`);
* `Setup.observer`, `Statement.observer`: what the verifier observes and how often it squeezes,
  the inputs of the chain (`Observer.encode`), which tell the keys apart
  (`Statement.observer_prefixFree`, with the domain separator's injectivity on the admitted
  lengths, `2 ^ 8 ≤ |F|` and two-adicity below `2 ^ 64`) and are never empty
  (`Statement.observer_fills`);
* `Statement.coinCount`: the squeezes of the most demanding challenge, the coins' size.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Sound CompStark.Iop CompStark.Ni OracleComp OracleSpec CompPoly
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-! ### Observed elements -/

/-- An element of `𝕂` as Plonky3 observes it: its coefficients, lowest first. -/
noncomputable def extElems (x : 𝕂) : List F := List.ofFn (extEquiv.symm x)

/-- Elements of `𝕂` as Plonky3 observes them, in order. -/
noncomputable def extsElems {n : ℕ} (x : Fin n → 𝕂) : List F := (List.ofFn x).flatMap extElems

/-- A word over `F` on a finite domain, observed in full in place of its commitment. -/
noncomputable def wordElems {α : Type} [Fintype α] (f : α → F) : List F :=
  List.ofFn (f ∘ (Fintype.equivFin α).symm)

/-- A word over `𝕂` on a finite domain, observed in full in place of its commitment. -/
noncomputable def extWordElems {α : Type} [Fintype α] (f : α → 𝕂) : List F :=
  extsElems (f ∘ (Fintype.equivFin α).symm)

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

omit [BaseField F] in
/-- Words are observed prefix-free. -/
theorem prefixFree_wordElems {α : Type} [Fintype α] : PrefixFree (wordElems (F := F) (α := α)) :=
  prefixFree_of_length (fun f g h ↦ by
    funext a
    have h' := congrFun (List.ofFn_injective h) (Fintype.equivFin α a)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h'
    exact h') fun _ _ ↦ by simp only [wordElems, List.length_ofFn]

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

/-- FRI's observations: each committed word, the first after `seed`, and its witness before its
folding challenge, one squeeze each; the final polynomial and the query witness before the query
positions, over their squeezes. -/
noncomputable def friObserver : {n : ℕ} → (s : Fri.Interaction.Schedule n) → List F →
    Observer F (Fri.Interaction.publicCoin 𝕂 top d t s) (friDecoder (F := F) K m top d t
      commitBits queryBits s)
  | _, .final, seed => (fun c ↦ seed ++ extsElems c,
      fun _ ↦ (squeezesFor K (querySamples t queryBits), queryWitnessElems top t queryBits,
        PUnit.unit))
  | _, .fold _ _ _ rest, seed => (fun w ↦ seed ++ extsElems w,
      (squeezesFor K (extSamples (EF := EF) commitBits), extWitnessElems commitBits,
        friObserver rest []))

/-- The ratios of FRI's draws: the folds' `powFraction F commitBits`, the queries'
`powFraction F queryBits * (2 ^ top * powFraction F top) ^ t`. -/
noncomputable def friRatio : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    Errors (Fri.Interaction.publicCoin 𝕂 top d t s)
  | _, .final => fun _ ↦ Iop.powFraction F queryBits * (2 ^ top * Iop.powFraction F top) ^ t
  | n, .fold _ _ _ rest => fun node ↦
      Sum.elim (fun _ ↦ Iop.powFraction F commitBits) (fun node ↦ friRatio rest node.2)
        (node : Fri.Interaction.Word 𝕂 n × (PUnit ⊕ (PUnit × Prefix PUnit
          (Fri.Interaction.publicCoin 𝕂 top d t rest)))).2

variable {top d t commitBits queryBits}

/-- FRI's draws are bounded by their ratios, when their samples fit the coins. -/
theorem bounded_friDecoder (hc : extSamples (EF := EF) commitBits ≤ m * K)
    (hq : querySamples t queryBits ≤ m * K) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    Decoder.Bounded (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder (F := F) K m top d t commitBits queryBits s)
      (friRatio (F := F) top d t commitBits queryBits s)
  | _, .final => fun _ ↦ ⟨bounded_queryDraw top t queryBits hq, trivial⟩
  | _, .fold _ _ _ rest => fun _ ↦
    ⟨bounded_extDraw commitBits hc, bounded_friDecoder hc hq rest⟩

/-- FRI's draws read only their squeezes. -/
theorem reads_friDecoder (hK : 0 < K) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    (seed : List F) → HashChain.Decoder.Reads (Fri.Interaction.publicCoin 𝕂 top d t s)
      (friDecoder (F := F) K m top d t commitBits queryBits s)
      ((friObserver K m top d t commitBits queryBits s seed).squeezes
        (Fri.Interaction.publicCoin 𝕂 top d t s) (friDecoder K m top d t commitBits queryBits s))
  | _, .final, _ => fun _ ↦ ⟨fun c c' h ↦ reads_queryDraw hK top t queryBits c c' h, trivial⟩
  | _, .fold _ _ _ rest, _ => fun _ ↦
    ⟨fun c c' h ↦ reads_extDraw hK commitBits c c' h, reads_friDecoder hK rest []⟩

/-- FRI's observations are prefix-free. -/
theorem prefixFree_friObserver : {n : ℕ} → (s : Fri.Interaction.Schedule n) → (seed : List F) →
    (friObserver K m top d t commitBits queryBits s seed).PrefixFree
      (Fri.Interaction.publicCoin 𝕂 top d t s) (friDecoder K m top d t commitBits queryBits s)
  | _, .final, seed => ⟨prefixFree_extsElems seed,
      fun _ ↦ ⟨(fixFree_queryWitnessElems top t queryBits).1,
        (fixFree_queryWitnessElems top t queryBits).2, trivial⟩⟩
  | _, .fold _ _ _ rest, seed => ⟨prefixFree_extsElems seed,
      (fixFree_extWitnessElems commitBits).1, (fixFree_extWitnessElems commitBits).2,
      prefixFree_friObserver rest []⟩

/-- FRI squeezes at most as often as `s` samples take, when its draws' samples are at most `s`. -/
theorem friObserver_squeezes_le {s : ℕ} (hc : extSamples (EF := EF) commitBits ≤ s)
    (hq : querySamples t queryBits ≤ s) : {n : ℕ} → (sch : Fri.Interaction.Schedule n) →
    (seed : List F) → (node : Prefix PUnit (Fri.Interaction.publicCoin 𝕂 top d t sch)) →
    (friObserver K m top d t commitBits queryBits sch seed).squeezes
      (Fri.Interaction.publicCoin 𝕂 top d t sch) (friDecoder K m top d t commitBits queryBits sch)
      node ≤ squeezesFor K s
  | _, .final, _, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : (_ : Fin d → 𝕂) × (PUnit ⊕ (PUnit × Empty)))
    · exact squeezesFor_mono hq
    · exact nomatch node
  | n, .fold _ _ _ rest, _, node => by
    obtain ⟨_, _ | ⟨_, node⟩⟩ := (node : Fri.Interaction.Word 𝕂 n × (PUnit ⊕ (PUnit ×
      Prefix PUnit (Fri.Interaction.publicCoin 𝕂 top d t rest))))
    · exact squeezesFor_mono hc
    · exact friObserver_squeezes_le hc hq rest [] node
/-- At least one element of `𝕂` is observed nonempty. -/
theorem extsElems_ne_nil {n : ℕ} (hn : 0 < n) (x : Fin n → 𝕂) : extsElems (F := F) x ≠ [] :=
  List.ne_nil_of_length_pos (by
    rw [length_extsElems]
    exact Nat.mul_pos hn (Challenge.params EF).d_pos)

/-- Every challenge of FRI that squeezes has observations since the last squeeze, when the final
polynomial has coefficients. -/
theorem friObserver_fills (hd : 0 < d) : {n : ℕ} → (s : Fri.Interaction.Schedule n) →
    (seed : List F) → (filled : Prop) →
    (friObserver K m top d t commitBits queryBits s seed).Fills
      (Fri.Interaction.publicCoin 𝕂 top d t s) (friDecoder K m top d t commitBits queryBits s)
      filled
  | _, .final, _, _ => fun c ↦
      ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _ (extsElems_ne_nil hd c))),
        fun _ ↦ trivial⟩
  | _, .fold _ _ _ rest, _, _ => fun w ↦
      ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_right_ne_nil _
          (extsElems_ne_nil (Nat.two_pow_pos _) w))),
        fun _ ↦ friObserver_fills hd rest [] _⟩

end Fri

end CompStark.Fs

/-! ### The STARK at a length -/

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Sound CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

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

/-- The STARK's draws: `α` without grinding, `ζ`, the batching challenge, FRI's. -/
noncomputable def decoder : Decoder (Coins F K m) S.publicCoin :=
  (extDraw 0, (extDraw S.params.oodPowBits, fun _ ↦ (extDraw S.params.batchPowBits,
    friDecoder K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
      S.params.numQueries S.params.commitPowBits S.params.queryPowBits (S.friSchedule []))))

/-- The STARK's observations: the trace, the quotient, the PCS's domain separator and the claimed
values, FRI's, with the draws' witnesses, and the draws' squeezes. -/
noncomputable def observer : Observer F S.publicCoin (S.decoder K m) :=
  (wordElems, (squeezesFor K (extSamples (EF := EF) 0), extWitnessElems 0,
    (wordElems, (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits),
      extWitnessElems S.params.oodPowBits,
      (fun o ↦ S.pcsSeed ++ S.openingsElems o, fun _ ↦
        (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits),
          extWitnessElems S.params.batchPowBits,
          friObserver K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
            S.params.numQueries S.params.commitPowBits S.params.queryPowBits (S.friSchedule [])
            S.friSeed))))))

/-- The draws' ratios: `1` at `α`, the grinding's `powFraction` at `ζ` and the batching
challenge, FRI's. -/
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

/-- The STARK's draws are bounded by their ratios, when the coins hold the most demanding
challenge's samples. -/
theorem bounded_decoder (hs : Challenge.d EF + S.params.numQueries + 1 ≤ m * K) :
    Decoder.Bounded S.publicCoin (S.decoder K m) (S.ratio (F := F)) := by
  have he (bits : ℕ) : extSamples (EF := EF) bits ≤ m * K := by
    have := extSamples_le (EF := EF) bits
    omega
  have h0 := bounded_extDraw (F := F) (EF := EF) (K := K) (m := m) 0 (he 0)
  rw [Sound.powFraction_zero] at h0
  exact fun _ ↦ ⟨h0, fun _ ↦ ⟨bounded_extDraw _ (he _), fun _ ↦ ⟨bounded_extDraw _ (he _),
    bounded_friDecoder K m (he _)
      ((querySamples_le S.params.numQueries _).trans (by omega)) _⟩⟩⟩

/-- The STARK's draws read only their squeezes. -/
theorem reads_decoder (hK : 0 < K) :
    HashChain.Decoder.Reads S.publicCoin (S.decoder K m)
      ((S.observer K m).squeezes S.publicCoin (S.decoder K m)) :=
  fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK 0 c c' h, fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
    fun _ ↦ ⟨fun c c' h ↦ reads_extDraw hK _ c c' h,
      reads_friDecoder K m hK (S.friSchedule []) S.friSeed⟩⟩⟩

/-- No challenge of the STARK squeezes more often than the most demanding challenge's samples
take. -/
theorem observer_squeezes_le (node : Prefix PUnit S.publicCoin) :
    (S.observer K m).squeezes S.publicCoin (S.decoder K m) node ≤
      squeezesFor K (Challenge.d EF + S.params.numQueries + 1) := by
  have he (bits : ℕ) : extSamples (EF := EF) bits ≤ Challenge.d EF + S.params.numQueries + 1 :=
    (extSamples_le bits).trans (by omega)
  obtain ⟨_, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, node⟩⟩⟩⟩ := (node : S.TraceMessage × (PUnit ⊕
    (PUnit × (S.QuotientMessage × (PUnit ⊕ (PUnit × ((_ : Openings S) × (PUnit ⊕
      (PUnit × S.FriPrefix)))))))))
  · exact squeezesFor_mono (he 0)
  · exact squeezesFor_mono (he _)
  · exact squeezesFor_mono (he _)
  · exact friObserver_squeezes_le K m (he _)
      ((querySamples_le S.params.numQueries _).trans (by omega)) _ _ node

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

/-- The STARK's observations are prefix-free. -/
theorem observer_prefixFree :
    (S.observer K m).PrefixFree S.publicCoin (S.decoder (F := F) K m) :=
  ⟨prefixFree_wordElems, (fixFree_extWitnessElems 0).1, (fixFree_extWitnessElems 0).2,
    prefixFree_wordElems, (fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
    prefixFree_of_length (fun _ _ h ↦ openingsElems_injective (List.append_cancel_left h))
      (fun a b ↦ by
        show (S.pcsSeed ++ S.openingsElems a).length = (S.pcsSeed ++ S.openingsElems b).length
        rw [List.length_append, List.length_append, length_openingsElems a b]),
    fun _ ↦ ⟨(fixFree_extWitnessElems _).1, (fixFree_extWitnessElems _).2,
      prefixFree_friObserver K m _ _⟩⟩

/-- Every challenge of the STARK that squeezes has observations since the last squeeze, when
`filled` holds before the trace. -/
theorem observer_fills {filled : Prop} (hf : filled) :
    (S.observer K m).Fills S.publicCoin (S.decoder (F := F) K m) filled := by
  have hQ (Q : S.QuotientMessage) : wordElems Q ≠ [] := List.ne_nil_of_length_pos (by
    simp only [wordElems, List.length_ofFn, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Challenge.params EF).d_pos)
      (Nat.two_pow_pos _))
  have hpcs : S.pcsSeed (F := F) ≠ [] := by
    simp only [pcsSeed, DomainSeparator.pcsSeed, DomainSeparator.toElems]
    exact List.cons_ne_nil _ _
  exact fun _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inl hf), fun _ Q ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (hQ Q)),
    fun _ _ ↦ ⟨fun _ _ ↦ Or.inl (Or.inr (List.append_ne_nil_of_left_ne_nil hpcs _)),
      fun _ ↦ friObserver_fills K m (Nat.two_pow_pos _) _ _ _⟩⟩⟩

end CompStark.Iop.Setup

/-! ### The STARK for a statement -/

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Sound CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The squeezes of the most demanding challenge: an extension element after a grinding sample,
or the query positions after theirs. -/
def coinCount : ℕ := squeezesFor K (Challenge.d EF + C.params.numQueries + 1)

variable (m : ℕ)

/-- The draws: at the length the prover sends, the STARK's. -/
noncomputable def decoder : Decoder (Coins F K m) (C.publicCoin EF) :=
  fun n ↦ (C.setup EF n).decoder K m

/-- The observations: the STARK's domain separator, which carries the length the prover sends,
then the STARK's at that length. -/
noncomputable def observer : Observer F (C.publicCoin EF) (C.decoder EF K m) :=
  (fun n ↦ starkSeedOf EF C.params C.air n.1, fun n ↦ (C.setup EF n).observer K m)

/-- The draws' ratios: at each length, the STARK's. -/
noncomputable def ratio : Errors (C.publicCoin EF) := fun node ↦ (C.setup EF node.1).ratio node.2

variable {C EF K}

/-- Each draw is bounded by its ratio, when the coins hold the most demanding challenge. -/
theorem bounded_decoder (hK : 0 < K) :
    Decoder.Bounded (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K)) (C.ratio EF) :=
  fun n ↦ (C.setup EF n).bounded_decoder (le_squeezesFor_mul hK _)

/-- No challenge squeezes more often than the coins hold. -/
theorem squeezes_le (node : Prefix PUnit (C.publicCoin EF)) :
    (C.observer EF K (C.coinCount EF K)).squeezes (C.publicCoin EF)
      (C.decoder EF K (C.coinCount EF K)) node ≤ C.coinCount EF K := by
  exact (C.setup EF node.1).observer_squeezes_le node.2

/-- Each draw reads only its squeezes. -/
theorem reads_decoder (hK : 0 < K) :
    HashChain.Decoder.Reads (C.publicCoin EF) (C.decoder EF K m)
      ((C.observer EF K m).squeezes (C.publicCoin EF) (C.decoder EF K m)) :=
  fun n ↦ (C.setup EF n).reads_decoder (hK := hK)

/-- The observations are prefix-free: the domain separator tells the admitted lengths apart, on a
base field of at least `2 ^ 8` elements with two-adicity below `2 ^ 64`. -/
theorem observer_prefixFree (h8 : 2 ^ 8 ≤ Nat.card F) (h64 : twoAdicity F < 2 ^ 64) :
    (C.observer EF K m).PrefixFree (C.publicCoin EF) (C.decoder EF K m) := by
  have h64' (n : C.Length) : n.1 < 2 ^ 64 := by
    have := n.2.sound.twoAdic
    omega
  exact ⟨prefixFree_of_length (fun a b h ↦ Subtype.ext
      (DomainSeparator.starkSeedOf_inj EF h8 _ _ (h64' a) (h64' b) h))
    (fun a b ↦ DomainSeparator.length_starkSeedOf EF _ _ a.1 b.1),
    fun n ↦ (C.setup EF n).observer_prefixFree⟩

/-- Every challenge that squeezes has observations since the last squeeze. -/
theorem observer_fills :
    (C.observer EF K m).Fills (C.publicCoin EF) (C.decoder EF K m) False := by
  refine fun n ↦ (C.setup EF n).observer_fills (Or.inr ?_)
  simp only [observer, starkSeedOf, DomainSeparator.starkSeed, DomainSeparator.toElems]
  exact List.cons_ne_nil _ _

end CompStark.Iop.Statement
