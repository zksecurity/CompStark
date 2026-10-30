/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Interaction.Stark
public import CompStark.Complete.Quotient
public import CompStark.Complete.Deep
public import CompStark.Ni.Setup

/-! # Completeness of the STARK on the interaction layer

The honest prover of a trace (`Setup.honestProver`) sends what Plonky3's prover commits to and
opens: the trace's extension onto `L`, the quotient's chunks extended onto `L`, and the values of
their polynomials at `ζ` and `ζ ω_n` (`honestOpened`, read in the spec field by `openingsOf`). If
the trace satisfies the AIR and `ζ` lies off the base field, so off the trace domain and `L`, its
strategy is accepted (`Setup.completeness`), discharging both conditions of
`Prover.strategy_accepts`:

* the honest quotient makes the check at `ζ` hold (`constraintsHoldAt_honest`): it is the
  specification prover's, whose openings pass the verifier's check (`checkConstraints_honest`),
  which is `ConstraintsHoldAt` in the spec field (`constraintsHoldAt_of_check`);
* DEEP quotients of codewords are codewords (`deepComponent_mem_code`, `deepWord_mem_code`): every
  opened word is the values on `L` of a polynomial of degree below `n`, claimed at its value there,
  so the DEEP word has low degree (`deepWord_honest_mem_code`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CompStark.Ni CompStark.Fri Polynomial _root_.Interaction
open _root_.Interaction.Oracle OracleComp OracleSpec

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-! ### DEEP quotients of codewords -/

/-- A word on the domain `g ⟨ω_m⟩` of `2 ^ m` points, claimed at a point off the base field, takes
the values there of a polynomial of degree below `n`, and its claimed value is the polynomial's
value at the point. -/
def OpensLow (m n : ℕ) (w : (Fin (2 ^ m) → F) × 𝕂 × 𝕂) : Prop :=
  (∀ y : F, w.2.1 ≠ algebraMap F 𝕂 y) ∧ ∃ P : F[X], P.degree < n ∧
    (∀ x, w.1 x = P.eval (basePoint m x)) ∧ w.2.2 = aeval w.2.1 P

/-- The DEEP quotient `(y - f(x)) / (z - x)` of a word that opens low is a codeword of its degree
bound on the domain `g ⟨ω_m⟩`. -/
theorem deepQuotient_mem_code {m n : ℕ} (D : Domain.SmoothCosetFftDomain m 𝕂)
    (hD : ∀ x, D x = algebraMap F 𝕂 (basePoint m x)) {w : (Fin (2 ^ m) → F) × 𝕂 × 𝕂}
    (hw : OpensLow m n w) :
    (fun x ↦ (w.2.2 - algebraMap F 𝕂 (w.1 x)) / (w.2.1 - D x)) ∈
      ReedSolomon.code (D : Fin (2 ^ m) ↪ 𝕂) n := by
  obtain ⟨hz, P, hP, hf, hy⟩ := hw
  set Q := Deep.divPoly (P.map (algebraMap F 𝕂)) w.2.1
  refine Submodule.mem_map.mpr ⟨Q, ?_, funext fun x ↦ ?_⟩
  · rw [Polynomial.mem_degreeLT]
    exact (Deep.degree_divPoly _ _ (degree_map_le.trans_lt hP)).trans_le
      (WithBot.coe_le_coe.mpr (Nat.sub_le _ _))
  · change Q.eval (D x) = (w.2.2 - algebraMap F 𝕂 (w.1 x)) / (w.2.1 - D x)
    rw [hD x, hy, Deep.eval_divPoly _ _ _ (sub_ne_zero.mpr (hz _)), div_eq_mul_inv, hf x,
      eval_map_algebraMap, eval_map, eval₂_at_apply]

section Deep
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- The points of `L`: `x_i = g ω ^ i`. -/
theorem Setup.domain_apply (x : S.Point) :
    S.domain x = algebraMap F 𝕂 (basePoint (S.logN + S.params.logBlowup) x) := by
  rw [Setup.domain, Sound.cosetDomain_apply, basePoint, map_mul, map_pow]

/-- **DEEP quotients of codewords are codewords.** If every opened word is the values on `L` of a
polynomial of degree below `n`, opened at a point off the base field to its value there, the DEEP
word is a codeword of degree below `n` on `L`. -/
theorem deepWord_mem_code {S : Setup EF lookups} (p : Prover S) (α ζ a : 𝕂)
    (h : ∀ w ∈ openedWords p α ζ, OpensLow (S.logN + S.params.logBlowup) S.n w) :
    deepWord p α ζ a ∈ S.code := by
  have hsum : (fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : ℕ) * components p α ζ k i) =
      ∑ k : Fin S.numOpened, a ^ (k : ℕ) • components p α ζ k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Sound.deepWord_eq, hsum]
  refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ ?_
  exact deepQuotient_mem_code S.domain (S.domain_apply) (h _ (List.getElem_mem _))

end Deep

/-! ### The honest prover -/

/-- The value at the point `x` of the domain of `2 ^ h` points of column `j` of a matrix whose rows
are the domain's points in bit-reversed order. -/
def rowValue (m : Stark.Mat F) (h j : ℕ) (x : Fin (2 ^ h)) : F :=
  m.values.getD (reverseBits x h * m.width + j) 0

/-- A column of a low-degree extension takes its polynomial's values on the coset. -/
theorem rowValue_eq {b h : ℕ} {m : Stark.Mat F} {ps : List F[X]} (hm : Mat.IsLde b h m ps)
    {j : ℕ} (hj : j < ps.length) (x : Fin (2 ^ h)) :
    rowValue m h j x = (ps.getD j 0).eval (basePoint h x) := by
  rw [rowValue, hm.2.2.2.2.2.2 _ (reverseBits_lt _ _) j hj, reverseBits_reverseBits x.isLt]
  rfl

/-- A point `ζ` off the base field, in the challenge field. -/
theorem outsideBase_symm {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    Ext.OutsideBase (Challenge.toSpec.symm ζ) :=
  Ext.outsideBase_iff.mpr fun y ↦ by rw [RingEquiv.apply_symm_apply]; exact hζ y

namespace Setup

section Generic
variable {lookups : List (Lookup F)} (S : Setup EF lookups) (trace : Array F)

/-- The honest trace's extension onto `L`: Plonky3's LDE, rows in bit-reversed order. -/
def honestExt : Stark.Mat F := ldeRef S.logN S.params.logBlowup gen S.air.width trace

variable {S}

/-- A column of a low-degree extension onto `L`, opened at a point `z` off the base field: its
values on `L` are its polynomial's, of degree below `n`, and its opening is the polynomial's value
at `z`. -/
theorem lde_opened {m : Stark.Mat F} {ps : List F[X]}
    (hm : Mat.IsLde S.params.logBlowup (S.logN + S.params.logBlowup) m ps) {j : ℕ}
    (hj : j < ps.length) {z : EF} (hz : Ext.OutsideBase z) :
    (ps.getD j 0).degree < S.n ∧
      (∀ x, rowValue m (S.logN + S.params.logBlowup) j x =
        (ps.getD j 0).eval (basePoint (S.logN + S.params.logBlowup) x)) ∧
      Challenge.toSpec ((Fri.openedAt S.params.logBlowup m z).getD j 0) =
        aeval (Challenge.toSpec z) (ps.getD j 0) := by
  refine ⟨?_, rowValue_eq hm hj, (openedAt_isLde _ _ m ps z hm hz).2 j hj⟩
  have hmem : ps.getD j 0 ∈ ps := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
  have := hm.2.2.2.2.2.1 _ hmem
  simpa only [Nat.add_sub_cancel] using this

/-- A column of a low-degree extension onto `L` opens low at a point off the base field. -/
theorem lde_opensLow {m : Stark.Mat F} {ps : List F[X]}
    (hm : Mat.IsLde S.params.logBlowup (S.logN + S.params.logBlowup) m ps) {j : ℕ}
    (hj : j < ps.length) {z : EF} (hz : Ext.OutsideBase z) :
    OpensLow (S.logN + S.params.logBlowup) S.n (rowValue m _ j, Challenge.toSpec z,
      Challenge.toSpec ((Fri.openedAt S.params.logBlowup m z).getD j 0)) :=
  let ⟨hdeg, hval, hopen⟩ := lde_opened hm hj hz
  ⟨Ext.outsideBase_iff.mp hz, _, hdeg, hval, hopen⟩

variable (S)

/-- The point `ζ ω_n` of a point `ζ` off the base field, in the challenge field: off the base field,
the spec field's `ζ ω_n`. -/
theorem outsideBase_next {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    Ext.OutsideBase (Challenge.toSpec.symm ζ * Ext.ofBase (twoAdicGen S.logN)) ∧
      Challenge.toSpec (Challenge.toSpec.symm ζ * Ext.ofBase (twoAdicGen S.logN)) =
        ζ * rootOfUnity S.logN := by
  have h24 := S.valid.twoAdic
  have hω0 : twoAdicGen (F := F) S.logN ≠ 0 := BaseField.twoAdicGen_ne_zero _ (by omega)
  refine ⟨Ext.outsideBase_mul_ofBase (outsideBase_symm hζ) hω0, ?_⟩
  rw [map_mul, RingEquiv.apply_symm_apply, Challenge.toSpec_ofBase]
  rfl

variable (chunks : List (Stark.Mat F)) (cur next : Array EF)

/-- The honest trace's columns open low at `ζ`. -/
theorem traceAt_opensLow {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y)
    (j : Fin S.air.width) :
    OpensLow (S.logN + S.params.logBlowup) S.n (rowValue (S.honestExt trace) _ j, ζ,
      (openingsOf S (honestOpened S.params.logBlowup S.air S.logN (S.honestExt trace) chunks
        (Challenge.toSpec.symm ζ)) cur next).traceAt j) := by
  obtain ⟨ps, hlde, -⟩ := matrix_lde S.params.logBlowup S.logN S.air.width trace S.valid.twoAdic
  have h := lde_opensLow hlde (j := j) (hlde.1 ▸ j.isLt) (outsideBase_symm hζ)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- The honest trace's columns of the next row open low at `ζ ω_n`. -/
theorem traceNext_opensLow {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y)
    (j : Fin S.air.mainNextWidth) :
    OpensLow (S.logN + S.params.logBlowup) S.n
      (rowValue (S.honestExt trace) _ (Fin.castLE S.air.mainNextWidth_le j),
        ζ * rootOfUnity S.logN,
        (openingsOf S (honestOpened S.params.logBlowup S.air S.logN (S.honestExt trace) chunks
          (Challenge.toSpec.symm ζ)) cur next).traceNext j) := by
  have hn : S.air.mainNextRow = true := by
    have hi := j.isLt
    unfold Air.mainNextWidth at hi; split at hi
    · assumption
    · omega
  obtain ⟨ps, hlde, -⟩ := matrix_lde S.params.logBlowup S.logN S.air.width trace S.valid.twoAdic
  obtain ⟨hzn, hzn'⟩ := S.outsideBase_next hζ
  have h := lde_opensLow hlde (j := Fin.castLE S.air.mainNextWidth_le j)
    (hlde.1 ▸ (Fin.castLE S.air.mainNextWidth_le j).isLt) hzn
  rw [hzn'] at h
  simp only [openingsOf, honestOpened, hn, ↓reduceIte, Option.getD_some]
  exact h

/-- The preprocessed trace's columns open low at `ζ`. -/
theorem preprocessedAt_opensLow {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y)
    (j : Fin S.air.preprocessedWidth) :
    OpensLow (S.logN + S.params.logBlowup) S.n (S.preprocessedWord j.val, ζ,
      (openingsOf S (honestOpened S.params.logBlowup S.air S.logN (S.honestExt trace) chunks
        (Challenge.toSpec.symm ζ)) cur next).preprocessedAt j) := by
  obtain ⟨pps, hplde, hpval⟩ := ldeRef_isLde S.logN S.params.logBlowup gen
    S.air.preprocessedWidth S.air.preprocessed S.valid.twoAdic gen_ne_zero
  have hj : j.val < pps.length := hplde.1 ▸ j.isLt
  have hpw : S.air.preprocessedWidth ≠ 0 := by have := j.isLt; omega
  obtain ⟨hdeg, -, hopen⟩ := lde_opened hplde hj (outsideBase_symm hζ)
  have heq := lde_eq_preprocessedPoly S pps hplde hpval j j.isLt
  rw [heq] at hdeg hopen
  rw [RingEquiv.apply_symm_apply] at hopen
  refine ⟨hζ, _, hdeg, fun _ ↦ rfl, ?_⟩
  simp only [openingsOf, honestOpened, hpw, ↓reduceIte, Option.getD_some]
  exact hopen

/-- The preprocessed trace's columns of the next row open low at `ζ ω_n`. -/
theorem preprocessedNext_opensLow {ζ : 𝕂} (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y)
    (j : Fin S.air.preprocessedNextWidth) :
    OpensLow (S.logN + S.params.logBlowup) S.n (S.preprocessedWord j.val,
      ζ * rootOfUnity S.logN,
      (openingsOf S (honestOpened S.params.logBlowup S.air S.logN (S.honestExt trace) chunks
        (Challenge.toSpec.symm ζ)) cur next).preprocessedNext j) := by
  have hn : S.air.opensPreprocessedNext = true := by
    have hi := j.isLt
    unfold Air.preprocessedNextWidth at hi; split at hi
    · assumption
    · omega
  have hj : j.val < S.air.preprocessedWidth := by
    have hi := j.isLt
    unfold Air.preprocessedNextWidth at hi; split at hi
    · omega
    · omega
  obtain ⟨pps, hplde, hpval⟩ := ldeRef_isLde S.logN S.params.logBlowup gen
    S.air.preprocessedWidth S.air.preprocessed S.valid.twoAdic gen_ne_zero
  have hj' : j.val < pps.length := hplde.1 ▸ hj
  obtain ⟨hzn, hzn'⟩ := S.outsideBase_next hζ
  have hz := Ext.outsideBase_iff.mp hzn
  obtain ⟨hdeg, -, hopen⟩ := lde_opened hplde hj' hzn
  have heq := lde_eq_preprocessedPoly S pps hplde hpval j hj
  rw [heq] at hdeg hopen
  rw [hzn'] at hz hopen
  refine ⟨hz, _, hdeg, fun _ ↦ rfl, ?_⟩
  simp only [openingsOf, honestOpened, hn, ↓reduceIte, Option.getD_some]
  exact hopen

end Generic

variable (S : Setup EF) (trace : Array F) (publicValues : List F)

/-- The honest quotient's values on the quotient domain after `α`: the constraints folded by `α`,
divided by `Z_H`. -/
noncomputable def honestQuotient (α : 𝕂) : Array EF :=
  quotientOfLde S.air publicValues S.logN (S.air.logQuotientChunks S.logN) (S.honestExt trace)
    (prepLde S.params.logBlowup S.air S.logN) (Challenge.toSpec.symm α)

/-- The honest quotient's chunk `c` after `α`: its values on the chunk's coset of the quotient
domain, extended onto `L`. -/
noncomputable def honestChunk (α : 𝕂) (c : ℕ) : Stark.Mat F :=
  ldeRef S.logN S.params.logBlowup
    (gen * (gen * powF (twoAdicGen (S.logN + S.air.logQuotientChunks S.logN)) c)⁻¹)
    (Challenge.d EF) (chunkValues (S.honestQuotient trace publicValues α)
      (2 ^ S.air.logQuotientChunks S.logN) c (2 ^ S.logN))

/-- The honest opened values after `α` and `ζ` (`honestOpened`). -/
noncomputable def honestOpenedValues (α ζ : 𝕂) : OpenedValues EF :=
  honestOpened S.params.logBlowup S.air S.logN (S.honestExt trace)
    ((List.range (2 ^ S.air.logQuotientChunks S.logN)).map (S.honestChunk trace publicValues α))
    (Challenge.toSpec.symm ζ)

/-- The honest prover of a trace: the trace's extension onto `L`, the quotient's chunks extended
onto `L`, and the values of their polynomials at `ζ` and `ζ ω_n`. -/
noncomputable def honestProver : Prover S where
  trace j x := rowValue (S.honestExt trace) _ j x
  quotient α c e x := rowValue (S.honestChunk trace publicValues α c) _ e x
  openings α ζ := openingsOf S (S.honestOpenedValues trace publicValues α ζ)
  perm _ _ _ := 0

variable {S trace publicValues}

/-- The shapes of a satisfied trace in a valid configuration. -/
theorem fits_of_satisfied (config : ValidConfig S.params S.air S.logN)
    (hsat : S.air.Satisfied S.logN trace publicValues) : Fits S.params S.air S.logN trace :=
  ⟨hsat.size, S.valid.colsInWidth, S.valid.twoAdic, config.chunksFit, S.valid.periodicFits⟩

/-- **The honest quotient makes the check at `ζ` hold**, for a trace satisfying the AIR and `ζ`
off the base field. -/
theorem constraintsHoldAt_honest (config : ValidConfig S.params S.air S.logN)
    (hsat : S.air.Satisfied S.logN trace publicValues) (α ζ : 𝕂)
    (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    ConstraintsHoldAt S publicValues α ζ ((S.honestProver trace publicValues).openings α ζ) := by
  have h := constraintsHoldAt_of_check S publicValues
    (S.honestOpenedValues trace publicValues α ζ) (Challenge.toSpec.symm ζ)
    (Challenge.toSpec.symm α) (by
      simp only [honestOpenedValues, honestOpened, List.size_toArray, List.length_map,
        List.length_range])
    (checkConstraints_honest S.params S.air S.logN trace publicValues _ _
      (fits_of_satisfied config hsat) hsat.vanish config.degreeFits (outsideBase_symm hζ))
  rwa [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h

/-- **The honest DEEP word has low degree**, for a trace satisfying the AIR and `ζ` off the base
field: every opened word is a codeword opened to its value. -/
theorem deepWord_honest_mem_code (config : ValidConfig S.params S.air S.logN) (α ζ a : 𝕂)
    (hζ : ∀ y : F, ζ ≠ algebraMap F 𝕂 y) :
    deepWord (S.honestProver trace publicValues) α ζ a ∈ S.code := by
  refine deepWord_mem_code _ α ζ a fun w hw ↦ ?_
  simp only [openedWords, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange,
    true_and] at hw
  rcases hw with ((((((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨c, e, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨c, -⟩) |
    ⟨c, -⟩)
  · exact S.traceAt_opensLow trace _ _ _ hζ j
  · exact S.traceNext_opensLow trace _ _ _ hζ j
  · obtain ⟨cps, hcl, hclen⟩ := chunk_isLde (EF := EF) S.params S.logN
      (S.air.logQuotientChunks S.logN) (S.honestQuotient trace publicValues α) S.valid.twoAdic
      config.chunksFit c
    have h := lde_opensLow hcl (j := e) (by omega) (outsideBase_symm hζ)
    rw [RingEquiv.apply_symm_apply] at h
    have hc : c.val < 2 ^ S.air.logQuotientChunks S.logN := c.isLt
    simp only [honestProver, openingsOf, honestOpenedValues, honestOpened, List.map_map,
      Function.comp_def, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hc, Option.map_some, Option.getD_some]
    rw [Array.getD_eq_getD_getElem?] at h
    exact h
  · exact S.preprocessedAt_opensLow trace _ _ _ hζ j
  · exact S.preprocessedNext_opensLow trace _ _ _ hζ j
  · exact c.elim0
  · exact c.elim0

/-- **Completeness.** For a valid configuration and a trace satisfying the AIR, the honest
prover's strategy is accepted on every execution whose out-of-domain point `ζ` lies off the base
field, so off the trace domain and `L`. -/
theorem completeness (config : ValidConfig S.params S.air S.logN)
    (hsat : S.air.Satisfied S.logN trace publicValues) :
    ∀ result ∈ support (executeStrategies unifSpec S.protocol.tree S.protocol.roles
      S.protocol.oracles noAccess noImpl (S.honestProver trace publicValues).strategy
      (S.verifier publicValues)),
      (∀ y : F, S.zetaOf result.1 ≠ algebraMap F 𝕂 y) → result.2.2 = true :=
  fun result hres hζ ↦ Prover.strategy_accepts _ publicValues result hres
    (constraintsHoldAt_honest config hsat _ _ hζ) (deepWord_honest_mem_code config _ _ _ hζ)

end Setup

end CompStark.Iop
