/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Stark

/-! # Honest openings of any heights verify

The commitment scheme's completeness for rounds of matrices of any heights (`verifyPcs_openPcs`):
when every committed matrix is the low-degree extension of polynomials onto its own height, at
least the final height, and is opened at points outside the base field, the verifier's
`verifyPcs` on the opened values accepts `openPcs`'s proof. The batched quotients are FRI's
inputs, one per distinct height, tallest first (`Fri.reduce`); FRI rolls each in at its height
(`verifyFri_proveFri`), the input openings are honest multi-openings of mixed heights
(`verifyInputs_honest`), and the verifier's batched quotients at a query are the prover's
(`reduceQuery_honest`).
-/

@[expose] public section
namespace CompStark.Stark
open CompStark.Fri CompStark.Complete

variable {F : Type} [BaseField F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

variable {EF : Type} [Challenge F EF]

/-- Two strictly decreasing lists of the same elements are equal. -/
theorem eq_of_pairwise_gt : ∀ (l₁ l₂ : List Nat), l₁.Pairwise (· > ·) → l₂.Pairwise (· > ·) →
    (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have hab : a = b := by
      have ha := (h a).mp List.mem_cons_self
      have hb := (h b).mpr List.mem_cons_self
      rcases List.mem_cons.mp ha with ha | ha
      · exact ha
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb.symm
      have := List.rel_of_pairwise_cons h₁ hb
      have := List.rel_of_pairwise_cons h₂ ha
      omega
    subst hab
    refine congrArg _ (eq_of_pairwise_gt l₁ l₂ h₁.of_cons h₂.of_cons fun x ↦ ?_)
    have h1 : ∀ x ∈ l₁, x < a := fun x hx ↦ List.rel_of_pairwise_cons h₁ hx
    have h2 : ∀ x ∈ l₂, x < a := fun x hx ↦ List.rel_of_pairwise_cons h₂ hx
    constructor
    · intro hx
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact absurd (h1 x hx) (Nat.lt_irrefl _)
      · exact hx'
    · intro hx
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact absurd (h2 x hx) (Nat.lt_irrefl _)
      · exact hx'

/-- Sorting tallest first and deduplicating gives a strictly decreasing list of the same
elements. -/
theorem pairwise_dedup_mergeSort (l : List Nat) :
    ((l.mergeSort fun a b ↦ b ≤ a).dedup).Pairwise (· > ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : Nat ↦ decide (b ≤ a))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hd := (hs.sublist (List.dedup_sublist _)).and (List.nodup_dedup _)
  exact hd.imp fun ⟨h1, h2⟩ ↦ by simp only [decide_eq_true_eq] at h1; omega

/-- A nonempty list has an element of largest key. -/
theorem exists_max {α : Type} (key : α → Nat) : ∀ l : List α, l ≠ [] →
    ∃ x ∈ l, ∀ y ∈ l, key y ≤ key x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_cons_self, fun y hy ↦ by rw [List.mem_singleton.mp hy]⟩
  | a :: b :: l, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max key (b :: l) (List.cons_ne_nil _ _)
    by_cases h : key a ≤ key x
    · exact ⟨x, List.mem_cons_of_mem _ hx, fun y hy ↦ by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact hmax y hy⟩
    · exact ⟨a, List.mem_cons_self, fun y hy ↦ by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · have := hmax y hy; omega⟩

theorem length_zip_openedOf (b : Nat) (m : Mat F) (zs : List EF) :
    ((zs.zip (openedOf b (m, zs))).map fun y ↦ (y.1, y.2.toList)).map (·.2.length) =
      (openedOf b (m, zs)).map (·.size) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [openedOf, List.map_cons, List.zip_cons_cons, Array.length_toList] at ih ⊢
    rw [ih]

variable [Poseidon2Field F]

/-- The committed matrices with their points and opened values. -/
def honestRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    List (Committed F × List (Mat F × List (EF × Array EF))) :=
  rounds.map fun r ↦ (r.1, r.2.map fun x ↦ (x.1, x.2.zip (openedOf b x)))

/-- The verifier's rounds: the commitments' roots, every matrix on its trace domain with its
points and opened values. -/
def verifierRounds (b : Nat) (rounds : List (Committed F × List (Mat F × List (EF × Array EF)))) :
    List (Round F EF) :=
  rounds.map fun r ↦ (r.1.root, r.2.map fun x ↦
    ((⟨1, Nat.log2 x.1.height - b⟩ : Domain F), x.2.map fun y ↦ (y.1, y.2.toList)))

/-- Rounds the specification prover opens honestly: some round, each committing to a nonempty
list of matrices, each matrix the extension of polynomials onto a height not below FRI's final
height, opened at a nonempty list of points outside the base field. -/
structure HonestRounds (P : Params) (rounds : List (OpenRound (specBackend EF))) : Prop where
  nonempty : rounds ≠ []
  commits : ∀ r ∈ rounds, r.2 ≠ [] ∧ r.1 = Committed.ofMats hashF compF (r.2.map (·.1))
  points : ∀ r ∈ rounds, ∀ x ∈ r.2, x.2 ≠ [] ∧ ∀ z ∈ x.2, Ext.OutsideBase z
  lde : ∀ r ∈ rounds, ∀ x ∈ r.2, ∃ h ps, CompStark.Mat.IsLde P.logBlowup h x.1 ps ∧
    P.logBlowup + P.logFinalPolyLen ≤ h

/-- The verifier's claimed evaluation counts are the prover's. -/
theorem claimCounts_verifierRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    claimCounts (verifierRounds b (honestRounds b rounds)) =
      countsOf (rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))) := by
  simp only [claimCounts, verifierRounds, honestRounds, countsOf, List.map_map]
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  exact length_zip_openedOf b x.1 x.2

/-- The verifier observes the prover's opened values. -/
theorem flat_verifierRounds (b : Nat) (rounds : List (OpenRound (specBackend EF))) :
    (verifierRounds b (honestRounds b rounds)).flatMap
        (fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
      (rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList) := by
  induction rounds with
  | nil => rfl
  | cons r rounds ih =>
    simp only [verifierRounds, honestRounds, List.map_cons, List.flatMap_cons,
      List.flatMap_append] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨c, ms⟩ := r
    dsimp only
    induction ms with
    | nil => rfl
    | cons x ms ihm =>
      simp only [List.map_cons, List.flatMap_cons, List.flatMap_append]
      rw [ihm, flatMap_zip_openedOf]

/-- The honest rounds' facts that the input checks and the batched quotients need. -/
theorem honestRounds_ok {P : Params} {rounds : List (OpenRound (specBackend EF))}
    (hr : HonestRounds P rounds) (logMax : Nat)
    (hmax : ∀ r ∈ rounds, ∀ x ∈ r.2, Nat.log2 x.1.height ≤ logMax) :
    ∀ r ∈ honestRounds P.logBlowup rounds, r.2 ≠ [] ∧
      r.1 = Committed.ofMats hashF compF (r.2.map (·.1)) ∧ ∃ H ≤ logMax,
        (∃ x ∈ r.2, x.1.height = 2 ^ H) ∧
          ∀ x ∈ r.2, x.2 ≠ [] ∧ ∃ h ≤ H, Deep.HonestItem P.logBlowup h x := by
  intro r' hr'
  obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hr'
  obtain ⟨hne, hc⟩ := hr.commits r hrm
  have hfst : (r.2.map fun x ↦ (x.1, x.2.zip (openedOf P.logBlowup x))).map (·.1) =
      r.2.map (·.1) := by rw [List.map_map]; rfl
  obtain ⟨xm, hxm, hmaxr⟩ := exists_max (fun x : Mat F × List EF ↦ Nat.log2 x.1.height) r.2 hne
  obtain ⟨hm, psm, hlm, -⟩ := hr.lde r hrm xm hxm
  refine ⟨by rwa [ne_eq, List.map_eq_nil_iff], by rw [hfst]; exact hc,
    Nat.log2 xm.1.height, hmax r hrm xm hxm,
    ⟨(xm.1, xm.2.zip (openedOf P.logBlowup xm)), List.mem_map_of_mem hxm,
      by rw [hlm.2.1, Nat.log2_two_pow]⟩, fun y hy ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hpne, hpts⟩ := hr.points r hrm x hx
  obtain ⟨h, ps, hl, -⟩ := hr.lde r hrm x hx
  have hz : x.2.zip (openedOf P.logBlowup x) ≠ [] := by
    obtain ⟨z, zs, hzs⟩ := List.exists_cons_of_ne_nil hpne
    simp only [openedOf, hzs, List.map_cons, List.zip_cons_cons, ne_eq, reduceCtorEq,
      not_false_eq_true]
  refine ⟨hz, h, ?_, honestItem_of _ _ _ _ ps hl hpts⟩
  have := hmaxr x hx
  rwa [hl.2.1, Nat.log2_two_pow] at this

/-- **Honest openings verify.** For rounds the specification prover opens honestly, the
verifier's `verifyPcs` on the opened values accepts `openPcs`'s proof from a transcript on
Plonky3's duplex, when the prover's grinder found its witnesses. -/
theorem verifyPcs_openPcs (P : Params) (rounds : List (OpenRound (specBackend EF)))
    (t : Transcript F 24) (hd : t.duplex = Poseidon2.duplex) (hr : HonestRounds P rounds)
    (hP : 0 < P.maxLogArity) (hq : 0 < P.numQueries) (hb : 0 < P.logBlowup)
    (hgrind : ((openPcs (specBackend EF) P rounds).run t).2.grindFailed = false) :
    verifyPcs (poseidon2 F) P (verifierRounds P.logBlowup (honestRounds P.logBlowup rounds))
      ((openPcs (specBackend EF) P rounds).run t).1.2 t =
      .ok ((), ((openPcs (specBackend EF) P rounds).run t).2) := by
  rw [openPcs_run] at hgrind ⊢
  dsimp only at hgrind ⊢
  set b := P.logBlowup with hbdef
  set drs := honestRounds b rounds with hdrs
  set vr := verifierRounds (EF := EF) b drs with hvr
  set opened := rounds.map fun r ↦ r.2.map fun x ↦ (openedOf b x, x.1, x.2.zip (openedOf b x))
    with hopened
  have hitems : opened.flatten.map (·.2) = drs.flatMap (·.2) := by
    rw [hopened, hdrs, honestRounds, List.flatMap_map, List.flatten_eq_flatMap,
      List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun r _ ↦ ?_
    simp only [id, List.map_map]; rfl
  set t1 := (t.observeList (DomainSeparator.pcsSeed F EF (countsOf opened)
    P.batchPowBits)).observeExts
      ((rounds.flatMap fun r ↦ r.2.flatMap (openedOf b)).flatMap (·.toList)) with ht1
  set g := t1.grind P.batchPowBits with hg
  clear_value g
  set alpha : EF := g.2.sampleExtValue with halpha
  clear_value alpha
  rw [hitems] at hgrind ⊢
  set items := drs.flatMap (·.2) with hitemsdef
  -- the items
  have hmem : ∀ x ∈ items, ∃ r ∈ rounds, ∃ y ∈ r.2, x = (y.1, y.2.zip (openedOf b y)) := by
    intro x hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨r, hrm, y, hy, rfl⟩
  have hhon : ∀ x ∈ items, ∃ h, b + P.logFinalPolyLen ≤ h ∧ Deep.HonestItem b h x := by
    intro x hx
    obtain ⟨r, hrm, y, hy, rfl⟩ := hmem x hx
    obtain ⟨h, ps, hl, hh⟩ := hr.lde r hrm y hy
    exact ⟨h, hh, honestItem_of _ _ _ _ ps hl (hr.points r hrm y hy).2⟩
  have hpow : ∀ x ∈ items, x.1.height = 2 ^ Nat.log2 x.1.height := fun x hx ↦ by
    obtain ⟨h, -, ps, hl, -⟩ := hhon x hx
    rw [hl.2.1, Nat.log2_two_pow]
  obtain ⟨hpw, hkeys, hsize⟩ := reduce_heights alpha items hpow
  have hlow := reduce_lowDegree b alpha items fun x hx ↦ by
    obtain ⟨h, -, hit⟩ := hhon x hx; exact ⟨h, hit⟩
  have hkey : ∀ x ∈ items, Nat.log2 x.1.height ∈ (Fri.reduce alpha items).map (·.1) :=
    fun x hx ↦ (hkeys _).mpr ⟨x, hx, rfl⟩
  have hfin : ∀ k ∈ (Fri.reduce alpha items).map (·.1), b + P.logFinalPolyLen ≤ k := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := (hkeys k).mp hk
    obtain ⟨h, hh, ps, hl, -⟩ := hhon x hx
    rw [hl.2.1, Nat.log2_two_pow]; exact hh
  -- the inputs: one per height, tallest first
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr.nonempty
  obtain ⟨y0, hy0⟩ := List.exists_mem_of_ne_nil _ (hr.commits r0 hr0).1
  have hx0 : (y0.1, y0.2.zip (openedOf b y0)) ∈ items :=
    List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hr0, List.mem_map_of_mem hy0⟩
  obtain ⟨⟨h0, f0⟩, L, hL⟩ : ∃ e L, Fri.reduce alpha items = e :: L := by
    cases hc : Fri.reduce alpha items with
    | nil =>
      have := hkey _ hx0
      rw [hc] at this
      exact absurd this List.not_mem_nil
    | cons e L => exact ⟨e, L, rfl⟩
  rw [hL] at hpw hkeys hsize hlow hkey hfin hgrind ⊢
  have hs0 : Nat.log2 f0.size = h0 := by
    rw [hsize _ List.mem_cons_self, Nat.log2_two_pow]
  have hmaxk : ∀ k ∈ (List.map (·.1) ((h0, f0) :: L)), k ≤ h0 := fun k hk ↦ by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact le_rfl
    · exact le_of_lt (List.rel_of_pairwise_cons hpw hk)
  have hg0 : Good P (Nat.log2 f0.size) f0 := by
    rw [hs0]
    exact ⟨hfin h0 List.mem_cons_self, hlow _ List.mem_cons_self⟩
  have hLsz : ∀ y ∈ L, Nat.log2 y.2.size = y.1 := fun y hy ↦ by
    rw [hsize y (List.mem_cons_of_mem _ hy), Nat.log2_two_pow]
  have hLmap : (L.map (·.2)).map (Nat.log2 ·.size) = L.map (·.1) := by
    rw [List.map_map]; exact List.map_congr_left hLsz
  have hpend : Pending P (L.map (·.2)) := by
    refine ⟨by rw [hLmap]; exact hpw.of_cons, fun v hv ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    rw [hLsz y hy]
    exact ⟨hfin _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)),
      hlow y (List.mem_cons_of_mem _ hy)⟩
  have hlt : ∀ v ∈ L.map (·.2), Nat.log2 v.size < Nat.log2 f0.size := fun v hv ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    rw [hLsz y hy, hs0]
    exact List.rel_of_pairwise_cons hpw (List.mem_map_of_mem hy)
  simp only [List.map_cons] at hgrind ⊢
  -- the grinding flags and the duplexes
  have hgB : g.2.grindFailed = false := by
    have h1 := flag_proveFri P rounds f0 (L.map (·.2)) g.1 (Transcript.sampleExtState EF g.2)
    have h2 := h1 hgrind
    rwa [flag_sampleExt] at h2
  have hd1 : t1.duplex = Poseidon2.duplex := by
    rw [ht1, duplex_observeExts, duplex_observeList, hd]
  have hd2 : (Transcript.sampleExtState EF g.2).duplex = Poseidon2.duplex := by
    rw [duplex_sampleExt, hg, duplex_grind, hd1]
  -- the verifier's transcript before the batching challenge is the prover's
  have hT : (t.observeList (DomainSeparator.pcsSeed F EF (claimCounts vr)
      P.batchPowBits)).observeExts (vr.flatMap fun r ↦ r.2.flatMap fun x ↦ x.2.flatMap (·.2)) =
      t1 := by
    rw [hvr, hdrs, claimCounts_verifierRounds, flat_verifierRounds]
  have hbw : ((proveFri (specBackend EF) P rounds (f0 :: L.map (·.2)) g.1).run
      (Transcript.sampleExtState EF g.2)).1.batchWitness = g.1 := by
    rw [proveFri_run]
  have hcB : checkWitness (poseidon2 F) P.batchPowBits g.1 t1 = .ok (true, g.2) := by
    have hc := checkWitness_grind t1 P.batchPowBits (by rw [← hg]; exact hgB)
    rw [← hg] at hc
    exact (checkWitness_run _ _ _ hd1).trans (congrArg Except.ok hc)
  rw [verifyPcs_run _ _ _ _ (by rw [hbw, hg]; exact grind_canonical _ _), hT, hbw, bind_ok hcB,
    ensure_true, pure_bind, bind_ok (sampleExt_run _), ← halpha]
  -- FRI
  have hround := honestRounds_ok hr h0 fun r hrm x hx ↦ hmaxk _ (by
    exact hkey _ (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hrm, List.mem_map_of_mem hx⟩))
  have hfst : drs.map (·.1) = rounds.map (·.1) := by
    rw [hdrs, honestRounds, List.map_map]; rfl
  have hF := verifyFri_proveFri P rounds f0 (L.map (·.2)) g.1 vr alpha
    (Transcript.sampleExtState EF g.2) hd2 hg0 hpend hlt hP hq hb
  refine hF hgrind ?_ ?_ ?_ ?_
  · obtain ⟨hne0, -⟩ := hr.commits r0 hr0
    refine List.any_eq_true.mpr ⟨_, List.mem_map_of_mem (List.mem_map_of_mem hr0), ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
      List.map_eq_nil_iff]
    exact hne0
  · have hblog : ∀ x ∈ items, Nat.log2 x.1.height - b + b = Nat.log2 x.1.height := by
      intro x hx
      obtain ⟨h, -, ps, hl, -⟩ := hhon x hx
      rw [hl.2.1, Nat.log2_two_pow]; exact Nat.sub_add_cancel hl.2.2.2.1
    rw [List.map_cons, hs0, hLmap]
    refine eq_of_pairwise_gt _ _ (pairwise_dedup_mergeSort _) (by simpa only [List.map_cons]
      using hpw) fun a ↦ ?_
    rw [List.mem_dedup, List.mem_mergeSort]
    change _ ↔ a ∈ ((h0, f0) :: L).map (·.1)
    rw [hkeys]
    constructor
    · intro ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      obtain ⟨r', hr', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      have hxi : x ∈ items := List.mem_flatMap.mpr ⟨r, hr, hx⟩
      exact ⟨x, hxi, (hblog x hxi).symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
      refine List.mem_map.mpr ⟨_, List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hr,
        List.mem_map_of_mem hxr⟩, hblog x hx⟩
  · intro indices t' hidx
    rw [hs0] at hidx ⊢
    rw [← map_fst_congr (fun c ↦ openMulti (specBackend EF) c
      (indices.map (· >>> (h0 - (specBackend EF).logHeight c)))) drs rounds hfst]
    exact verifyInputs_honest P h0 indices drs hidx hround t'
  · intro index t' hidx
    rw [hs0] at hidx ⊢
    rw [← map_fst_congr (fun c ↦ ((specBackend EF).openAt c
      (index >>> (h0 - (specBackend EF).logHeight c))).values.toList) drs rounds hfst]
    have hD := reduceQuery_honest P h0 index alpha drs hidx fun r hr' ↦ by
      obtain ⟨h1, h2, H, hH, htop, hall⟩ := hround r hr'
      exact ⟨h1, h2, H, hH, htop, fun x hx ↦ (hall x hx).2⟩
    rw [hL] at hD
    refine (congrFun hD t').trans ?_
    simp only [List.map_cons, Nat.sub_self, Nat.shiftRight_zero, roOf, List.map_map]
    refine congrArg (fun x ↦ Except.ok (x, t')) (congrArg _ (List.map_congr_left fun y hy ↦ ?_))
    simp only [Function.comp_apply, hLsz y hy]

end CompStark.Stark
