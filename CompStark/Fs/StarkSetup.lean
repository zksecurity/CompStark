/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.Observations
public import CompStark.Fs.StarkDeep
public import CompStark.Complete.Lde
public import CompStark.Complete.Merkle

/-! # The setup on fixed answers

The setup's computation of the verifying key is natural in its primitives
(`preprocessedKeyWith_map`), so simulating its oracles by `impl` runs it on the answers of `impl`
(`simulateQ_preprocessedKeyWith`). A cache under whose cap the honest openings bind holds the
preprocessed trace's extension: the columns read off it are the preprocessed words
(`committedColumn_setup`), since honest openings verify (`Merkle.verifyMulti_prune_mixed`,
`Merkle.verifyBatch_of_verifyMulti`).
-/

@[expose] public section

namespace CompStark.Stark

variable {F : Type} {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n)

theorem merkleNodeWith_map (H : Primitives F m) (leaf : Nat → m (Digest F)) :
    ∀ j t, φ (merkleNodeWith H leaf j t) = merkleNodeWith (H.map φ) (fun r ↦ φ (leaf r)) j t
  | 0, _ => rfl
  | j + 1, t => by
    simp only [merkleNodeWith, MonadHom.mmap_bind, merkleNodeWith_map H leaf j]
    rfl

theorem merkleCapWith_map [LawfulMonad m] [LawfulMonad n] (H : Primitives F m)
    (leaf : Nat → m (Digest F)) (levels h : Nat) :
    φ (merkleCapWith H leaf levels h) =
      merkleCapWith (H.map φ) (fun r ↦ φ (leaf r)) levels h := by
  unfold merkleCapWith
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_mapM, merkleNodeWith_map]

/-- **The setup is natural in its primitives.** -/
theorem preprocessedKeyWith_map [LawfulMonad m] [LawfulMonad n] [BaseField F]
    (H : Primitives F m) (P : Fri.Params) (A : Air F) (logN : Nat) :
    φ (preprocessedKeyWith H P A logN) = preprocessedKeyWith (H.map φ) P A logN := by
  unfold preprocessedKeyWith
  split
  · simp only [MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, merkleCapWith_map]
    rfl

end CompStark.Stark

namespace CompStark.RandomOracle
open CompStark.Stark OracleSpec OracleComp

variable {F : Type} [BaseField F] {K : Nat}

/-- Simulating the oracles of the setup by `impl` runs the setup on the answers of `impl`. -/
theorem simulateQ_preprocessedKeyWith {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl (spec F K) n) (P : Fri.Params) (A : Air F) (logN : Nat) :
    simulateQ impl (preprocessedKeyWith (ideal F K) P A logN) =
      preprocessedKeyWith (withAnswers K impl) P A logN := by
  have h := preprocessedKeyWith_map (simulateQ' impl) (ideal F K) P A logN
  rw [withAnswers_map] at h
  simpa only [simulateQ'_apply, simulateQ_spec_query] using h

end CompStark.RandomOracle

namespace CompStark.Fs
open CompStark.Stark CompStark.Fri CompStark.RandomOracle CompStark.Iop OracleSpec OracleComp
open Polynomial

variable {F : Type} {K : Nat}

/-- A cap on pure primitives is its nodes. -/
theorem merkleCapWith_id (H : Primitives F Id) (leaf : Nat → Id (Digest F)) (levels h : Nat) :
    merkleCapWith H leaf levels h = ((List.range (2 ^ min h levels)).map
      (merkleNodeWith H leaf (levels - min h levels))).toArray := by
  unfold merkleCapWith
  exact congrArg List.toArray List.idRun_mapM

variable [BaseField F] {EF : Type} [Challenge F EF]

/-- The preprocessed trace's polynomials are those of its extension. -/
theorem lde_eq_preprocessedPoly {lookups : List (Lookup F)} (S : Iop.Setup EF lookups)
    (ps : List F[X])
    (hlde : CompStark.Mat.IsLde S.params.logBlowup (S.logN + S.params.logBlowup)
      (preprocessedLde S.params S.air S.logN) ps)
    (hval : ∀ j < S.air.preprocessedWidth, ∀ i < 2 ^ S.logN,
      (ps.getD j 0).eval ((gen * gen⁻¹) * twoAdicGen S.logN ^ i) =
        S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0)
    (j : Nat) (hj : j < S.air.preprocessedWidth) : ps.getD j 0 = S.preprocessedPoly j := by
  have hlen : ps.length = S.air.preprocessedWidth := hlde.1.symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (fun a ha b hb hab ↦
    (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
      (by have := S.valid.twoAdic; omega)).pow_inj
      (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab) ?_ fun i hi ↦ ?_
  · have hmem : ps.getD j 0 ∈ ps := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have := hlde.2.2.2.2.2.1 _ hmem
    rw [Finset.card_range]
    simpa only [Nat.add_sub_cancel] using this
  · have := hval j hj i (Finset.mem_range.mp hi)
    rwa [mul_inv_cancel₀ (BaseField.gen_ne_zero), one_mul] at this

/-- **The preprocessed trace under a binding cap.** If honest openings against the verifying
key's cap bind the rows of `cache`, the columns read off `cache` under the cap are the
preprocessed trace's words. -/
theorem committedColumn_setup (S : Iop.Setup EF) (cache : MixedMerkleTree.Cache (List F) (Digest F))
    (g : (q : Query F) → Answer K q) (k : PreprocessedKey F)
    (hk : preprocessedKeyWith (idealOf g) S.params S.air S.logN = some k)
    (hbind : CapBinding cache (idealOf g) k.commit) :
    ∀ j < S.air.preprocessedWidth, committedColumn S cache k.commit j = S.preprocessedWord j := by
  intro j hj
  have hpw : S.air.preprocessedWidth ≠ 0 := by omega
  set ext := preprocessedLde S.params S.air S.logN with hext
  set hash : List F → Digest F := fun row ↦ g (.leaf row)
  set compress : Digest F → Digest F → Digest F := fun a b ↦ g (.node a b)
  obtain ⟨-, hheight, -⟩ :=
    shape_ldeRef S.logN S.params.logBlowup gen S.air.preprocessedWidth S.air.preprocessed
  set c := min S.params.capHeight S.logSize
  have hext : ∀ m ∈ [ext.toMatrix], m.height = 2 ^ S.logSize := fun m hm ↦ by
    rw [List.mem_singleton.mp hm]; exact hheight
  have hroot : k.commit = ((List.range (2 ^ c)).map
      (Merkle.injNode hash compress [ext.toMatrix] S.logSize (S.logSize - c))).toArray := by
    unfold preprocessedKeyWith at hk
    rw [ite_eq_right_of_eq_false _ _ (eq_false hpw)] at hk
    obtain rfl := Option.some_injective _ hk
    show merkleCapWith (idealOf g) _ _ _ = _
    rw [merkleCapWith_id]
    refine congrArg List.toArray (List.map_congr_left fun t _ ↦ ?_)
    rw [merkleNodeWith_pure (idealOf g) hash compress (fun _ ↦ rfl) (fun _ _ ↦ rfl),
      Merkle.injNode_uniform hash compress _ _ hext _ (Nat.sub_le _ _)]
    congr 1
    funext r
    simp only [Merkle.leafHashes, rowOf_toList, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  obtain ⟨ps, hlde, hval⟩ := ldeRef_isLde S.logN S.params.logBlowup gen S.air.preprocessedWidth
    S.air.preprocessed S.valid.twoAdic BaseField.gen_ne_zero
  have hP := lde_eq_preprocessedPoly S ps hlde hval j hj
  funext z
  set i := reverseBits z.val S.logSize
  have hi : i < 2 ^ S.logSize := reverseBits_lt _ _
  -- the honest opening at `i`, as a multi-opening against the cap
  have hv := Merkle.verifyMulti_prune_mixed hash compress [ext.toMatrix] S.logSize
    S.params.capHeight (fun m hm ↦ ⟨_, le_rfl, hext m hm⟩) ⟨_, List.mem_singleton_self _, hheight⟩
    (fun m hm ↦ by rw [hext m hm]; exact Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
    [i] (fun i' hi' ↦ by rw [List.mem_singleton.mp hi']; exact hi)
    [(List.range S.logSize).map fun l ↦
      Merkle.injNode hash compress [ext.toMatrix] S.logSize l ((i >>> l) ^^^ 1)]
    (fun q hq l hl ↦ by
      obtain rfl : q = 0 := by simp only [List.length_singleton] at hq; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_map, List.getElem?_range hl, Option.map_some]
      rfl)
  have hcl : k.commit.toList = (List.range (2 ^ c)).map
      (Merkle.injNode hash compress [ext.toMatrix] S.logSize (S.logSize - c)) := by
    rw [hroot, List.toList_toArray]
  rw [← hcl] at hv
  obtain ⟨path, hpath⟩ := Merkle.verifyBatch_of_verifyMulti hash compress k.commit.toList
    S.params.capHeight 1 S.logSize Nat.one_pos _ (by
      simp only [List.map_cons, List.map_nil, List.replicate_one]
      exact congrArg (fun x ↦ [x]) hheight) _ _ _ hv 0 (by simp only [List.length_singleton]; omega)
  have hex := extractCapRow_of_verifyCapH cache (idealOf g) k.commit hbind S.params.capHeight 1
    S.logSize i _ path Nat.one_pos hpath
  have hlog : ext.toMatrix.height.log2 = S.logSize := by
    rw [show ext.toMatrix.height = 2 ^ S.logSize from hheight, Nat.log2_two_pow]
  simp only [List.getD_cons_zero, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, hlog, Nat.sub_self, Nat.shiftRight_zero] at hex
  have hzlt : z.val < 2 ^ S.logSize := z.isLt
  have hjw : j < ext.toMatrix.width := hj
  rw [committedColumn, leafRow, hex, Option.getD_some, Merkle.Matrix.row,
    List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hjw),
    List.getElem_map, List.getElem_range]
  have hcell : ext.values.getD (i * ext.width + j) 0 = _ :=
    hlde.2.2.2.2.2.2 i hi j (by rw [← hlde.1]; exact hj)
  show ext.values.getD (i * ext.width + j) 0 = _
  rw [hcell, reverseBits_reverseBits hzlt, hP]
  rfl

end CompStark.Fs
