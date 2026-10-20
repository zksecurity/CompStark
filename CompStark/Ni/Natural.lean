/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Verifier
public import PolyFun.Control.Monad.Hom.Loops

/-! # The verifier is natural in its primitives

A monad morphism `φ : m →ᵐ n` maps primitives in `m` to primitives in `n` (`Primitives.map`),
and maps the verifier on the former to the verifier on the latter (`verifyWith_map`). The proof
pushes `φ` through each definition of the verifier once, for every proof; it never runs the
verifier.
-/

@[expose] public section
namespace CompStark

/-- The primitives `H` with their results mapped by `φ`. -/
def Primitives.map {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n) (H : Primitives m) :
    Primitives n where
  State := H.State
  init := H.init
  observe := H.observe
  sample s := φ (H.sample s)
  hash xs := φ (H.hash xs)
  compress a b := φ (H.compress a b)

@[simp] theorem Primitives.map_init {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n)
    (H : Primitives m) : (H.map φ).init = H.init := rfl

namespace Merkle

variable {F : Type} {d : Nat} {m n : Type → Type} [Monad m] [Monad n] (φ : m →ᵐ n)

theorem climbM_map (hash : List F → m (Vector F d))
    (compress : Vector F d → Vector F d → m (Vector F d)) (values : List (List F)) :
    ∀ path groups index padded root, φ (climbM hash compress values path groups index padded root) =
      climbM (fun xs ↦ φ (hash xs)) (fun a b ↦ φ (compress a b)) values path groups index padded
        root
  | [], _, _, _, _ => by simp only [climbM, MonadHom.mmap_pure]
  | sib :: sibs, groups, index, padded, root => by
    simp only [climbM]
    split <;>
    · simp only [MonadHom.mmap_bind]
      refine bind_congr fun r ↦ ?_
      rcases groups with _ | ⟨⟨h, is⟩, rest⟩
      · exact climbM_map hash compress values sibs [] _ _ r
      · dsimp only
        split
        · simp only [MonadHom.mmap_bind]
          refine bind_congr fun x ↦ bind_congr fun y ↦ ?_
          exact climbM_map hash compress values sibs rest _ _ y
        · exact climbM_map hash compress values sibs _ _ _ r

theorem verifyBatchM_map [DecidableEq F] (hash : List F → m (Vector F d))
    (compress : Vector F d → Vector F d → m (Vector F d)) (commit : Vector F d)
    (heights : List Nat) (index : Nat) (values : List (List F)) (path : List (Vector F d)) :
    φ (verifyBatchM hash compress commit heights index values path) =
      verifyBatchM (fun xs ↦ φ (hash xs)) (fun a b ↦ φ (compress a b)) commit heights index values
        path := by
  unfold verifyBatchM
  split
  · simp only [MonadHom.mmap_pure]
  · simp only [MonadHom.mmap_ite, MonadHom.mmap_bind, MonadHom.mmap_pure, climbM_map]

end Merkle

namespace Fri
open CompStark.Stark

local notation "F" => KoalaBear.Fast.Field

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : m →ᵐ n)
  {EF : Type} [Challenge EF]
  (H : Primitives m)

/-- `φ` on the verifier's monad. -/
abbrev mapM : M H →ᵐ M (H.map φ) := StateT.mapHom (ExceptT.mapHom φ)

omit [LawfulMonad m] [LawfulMonad n] in
theorem mapM_modify (f : H.State → H.State) :
    mapM φ H (modify f : M H Unit) = (modify f : M (H.map φ) Unit) := by
  apply StateT.ext
  intro s
  apply ExceptT.ext
  exact φ.mmap_pure (Except.ok ((), f s))

omit [LawfulMonad m] [LawfulMonad n] in
theorem mapM_observe (x : F) : mapM φ H (observe H x) = observe (H.map φ) x :=
  mapM_modify φ H _

omit [LawfulMonad m] [LawfulMonad n] in
theorem mapM_observeList (xs : List F) :
    mapM φ H (observeList H xs) = observeList (H.map φ) xs :=
  mapM_modify φ H _

omit [LawfulMonad m] [LawfulMonad n] in
theorem mapM_observeExts (xs : List EF) :
    mapM φ H (observeExts H xs) = observeExts (H.map φ) xs :=
  mapM_modify φ H _

theorem mapM_sample : mapM φ H (sample H) = sample (H.map φ) := by
  apply StateT.ext
  intro s
  apply ExceptT.ext
  exact φ.mmap_map (H.sample s) Except.ok

theorem mapM_throw {α : Type} (e : String) :
    mapM φ H (throw e : M H α) = (throw e : M (H.map φ) α) := by
  apply StateT.ext
  intro s
  apply ExceptT.ext
  change φ ((throw e : ExceptT String m α) >>= fun a ↦ pure (a, s)).run =
    ((throw e : ExceptT String n α) >>= fun a ↦ pure (a, s)).run
  simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind, MonadHom.mmap_pure]

theorem mapM_sampleList : ∀ k, mapM φ H (sampleList H k) = sampleList (H.map φ) k
  | 0 => by simp only [sampleList, MonadHom.mmap_pure]
  | k + 1 => by
    simp only [sampleList, MonadHom.mmap_bind, MonadHom.mmap_pure, mapM_sample, mapM_sampleList k]

theorem mapM_sampleExt : mapM φ H (sampleExt H : M H EF) = sampleExt (H.map φ) := by
  simp only [sampleExt, MonadHom.mmap_bind, MonadHom.mmap_pure, mapM_sampleList]

theorem mapM_sampleBits (bits : Nat) :
    mapM φ H (sampleBits H bits) = sampleBits (H.map φ) bits := by
  simp only [sampleBits, MonadHom.mmap_bind, MonadHom.mmap_pure, mapM_sample]

theorem mapM_checkWitness (bits : Nat) (w : F) :
    mapM φ H (checkWitness H bits w) = checkWitness (H.map φ) bits w := by
  simp only [checkWitness, MonadHom.mmap_ite, MonadHom.mmap_bind, MonadHom.mmap_pure,
    mapM_sampleBits, mapM_observe]

theorem mapM_ensure (b : Bool) (msg : String) :
    mapM φ H (ensure (H := H) b msg) = ensure (H := H.map φ) b msg := by
  simp only [ensure, MonadHom.mmap_ite, MonadHom.mmap_pure, mapM_throw]

theorem mapM_checkOpening (commit : Digest) (heights : List Nat) (index : Nat)
    (values : List (List F)) (path : List Digest) :
    mapM φ H (checkOpening H commit heights index values path) =
      checkOpening (H.map φ) commit heights index values path := by
  apply StateT.ext
  intro s
  apply ExceptT.ext
  change φ ((ExceptT.lift (Merkle.verifyBatchM H.hash H.compress commit heights index values
    path) >>= fun a ↦ pure (a, s) : ExceptT String m _).run) =
    (ExceptT.lift (Merkle.verifyBatchM (H.map φ).hash (H.map φ).compress commit heights index
      values path) >>= fun a ↦ pure (a, s) : ExceptT String n _).run
  simp only [ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ExceptT.run_pure,
    MonadHom.mmap_bind, MonadHom.mmap_pure, Merkle.verifyBatchM_map]
  rfl

theorem mapM_openInput (P : Params) (logMax index : Nat) (alpha : EF)
    (inputs : List BatchOpening) (rounds : List (Round EF)) :
    mapM φ H (openInput H P logMax index alpha inputs rounds) =
      openInput (H.map φ) P logMax index alpha inputs rounds := by
  simp only [openInput, MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_forIn,
    mapM_ensure, mapM_checkOpening]
  congr! with a
  split <;> simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, mapM_ensure]

theorem mapM_verifyQuery (P : Params) (logMax index : Nat) (betas : List EF)
    (commits : List Digest) (steps : List (CommitStep EF)) (ro : List (Nat × EF)) :
    mapM φ H (verifyQuery H P logMax index betas commits steps ro) =
      verifyQuery (H.map φ) P logMax index betas commits steps ro := by
  rcases ro with _ | ⟨r, rest⟩ <;>
  · simp only [verifyQuery, MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_forIn,
      mapM_ensure, mapM_checkOpening, mapM_throw]
    congr! with a
    split <;> simp only [MonadHom.mmap_ite, MonadHom.mmap_pure]

theorem mapM_verifyFri (P : Params) (proof : FriProof EF) (rounds : List (Round EF)) :
    mapM φ H (verifyFri H P proof rounds) = verifyFri (H.map φ) P proof rounds := by
  simp only [verifyFri, ← Array.forIn_toList, MonadHom.mmap_bind, MonadHom.mmap_pure,
    MonadHom.mmap_forIn,
    mapM_ensure, mapM_sampleExt, mapM_sampleBits, mapM_checkWitness,
    mapM_observe, mapM_observeList, mapM_observeExts, mapM_openInput, mapM_verifyQuery]

theorem mapM_verifyPcs (P : Params) (rounds : List (Round EF)) (proof : FriProof EF) :
    mapM φ H (verifyPcs H P rounds proof) = verifyPcs (H.map φ) P rounds proof := by
  simp only [verifyPcs, MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_forIn,
    mapM_observeExts, mapM_verifyFri]

end Fri

namespace Stark
open CompStark.Fri

local notation "F" => KoalaBear.Fast.Field

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : m →ᵐ n)
  {EF : Type} [Challenge EF]

omit [LawfulMonad m] [LawfulMonad n] in
theorem exceptT_mapHom_throw {α : Type} (e : String) :
    ExceptT.mapHom φ (throw e : ExceptT String m α) = throw e :=
  ExceptT.ext (φ.mmap_pure (Except.error e))

omit [LawfulMonad m] [LawfulMonad n] in
theorem exceptT_mapHom_run {α : Type} (H : Primitives m) (x : M H α) (s : H.State) :
    ExceptT.mapHom φ (x.run s) = (Fri.mapM φ H x).run s := rfl

/-- **The verifier is natural in its primitives.** -/
theorem verifyWith_map (H : Primitives m) (P : Params) (A : Air) (proof : Proof EF)
    (pis : List F) :
    φ (verifyWith H P A proof pis) = verifyWith (H.map φ) P A proof pis := by
  change (ExceptT.mapHom φ _).run = _
  simp only [verifyWith, MonadHom.mmap_bind, MonadHom.mmap_pure, MonadHom.mmap_ite,
    exceptT_mapHom_throw, exceptT_mapHom_run, mapM_observe, mapM_observeList, mapM_sampleExt,
    mapM_verifyPcs, Primitives.map_init]
  rfl

end Stark
end CompStark
