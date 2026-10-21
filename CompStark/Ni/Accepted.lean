/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.BcsChallenges

/-! # Two facts about accepted runs

* `verifyWith_log_head`: the verifier's first oracle call is the duplex call of `α`'s round, so
  it queries no hash before the call that binds the trace commitment.
* `commitWitness_idealOf`: every fold round's grinding check passes, so on an answer table the
  first sample of the round's answer has `commitPowBits` vanishing low bits.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Fri CompStark.RandomOracle OracleSpec OracleComp

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K : Nat}
    (answer : (q : Query F) → Answer K q)

/-! ### The first call -/

/-- **The first call.** If the verifier on logged answers accepts, its log starts with the duplex
call of the first round. -/
theorem verifyWith_log_head (hK : Challenge.d EF ≤ K) (P : Fri.Params) (A : Air F)
    (proof : Proof F EF)
    (pis : List F) (hok : (verifyWith (idealLogged answer) P A proof pis).run.1 = .ok ()) :
    ∃ rest, (verifyWith (idealLogged answer) P A proof pis).run.2 =
      ⟨keyAt answer (inputs P pis proof) 0, answer (keyAt answer (inputs P pis proof) 0)⟩ ::
        rest := by
  unfold verifyWith at hok ⊢
  dsimp only at hok ⊢
  split at hok
  · rename_i hshape
    simp only [hshape, ↓reduceIte] at ⊢
    split at hok
    · rename_i harities
      simp only [harities, ↓reduceIte] at ⊢
      rw [run_stateT_bind _ _ _ (fun a ↦ by split <;> rfl)] at hok ⊢
      rcases hrun : out answer _ { cap := initCap, input := [], samples := [] } with ⟨_ | a, w⟩
      · rw [hrun] at hok
        cases hok
      rw [hrun] at hok
      dsimp only
      have hrun1 := congrArg Prod.fst hrun
      have hrun2 := congrArg Prod.snd hrun
      dsimp only at hrun1 hrun2
      rw [← hrun2]
      clear hrun hrun2 hok
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observe] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observe, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observeList_nil] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observeList_nil, List.nil_append]
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [out_observeList_nil] at h₁
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, out_observeList_nil, List.nil_append]
      have hin₀ : [] ++ [(proof.degreeBits : F)] ++ [(proof.degreeBits : F)] ++ [0] ++
          proof.traceCommit.toList ++ pis = (inputs P pis proof).getD 0 [] := by
        simp only [inputs, List.nil_append, List.cons_append, List.append_assoc,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
      dsimp only at hrun1 ⊢
      rw [hin₀, show initCap = capAt answer (inputs P pis proof) 0 from rfl] at hrun1 ⊢
      have hv₀ := out_sampleExt_nil (EF := EF) answer hK (capAt answer (inputs P pis proof) 0)
        ((inputs P pis proof).getD 0 [])
      obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
      rw [hv₀] at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
      rw [hlog, hv₀]
      exact ⟨_, rfl⟩
    · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
      cases hok
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok

/-! ### The fold rounds' grinding -/

section Commit
variable (H : Primitives F Id) (P : Params)

/-- An accepting commit loop passes every grinding check, from the state `commitReplay` reaches
before each round. -/
theorem commitLoop_wit :
    ∀ (cws : List (Digest F × F)) (betas : Array EF) (s : H.State) (r : Array EF × H.State),
      forIn (m := M H) cws betas (commitBody H P) s = .ok r →
        ∀ i (hi : i < cws.length), (chkWit H P.commitPowBits cws[i].2
          (obsList H (commitReplay (EF := EF) H P (cws.take i) s).2 cws[i].1.toList)).1 = true
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | cw :: cws, betas, s, r, h, i, hi => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    unfold commitBody at h1
    rw [bind_ok_of H (observeList_eq H _ s), bind_ok_of H (checkWitness_eq H _ _ _)] at h1
    obtain ⟨hwit, h1⟩ := ensure_bind_eq_ok H h1
    rw [bind_ok_of H (sampleExt_eq H _)] at h1
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h1)
    subst hs1 hs2
    cases i with
    | zero => exact hwit
    | succ i =>
      exact commitLoop_wit cws _ _ r h2 i (by simp only [List.length_cons] at hi; omega)

end Commit

variable (P : Params) (proof : Proof F EF) (pis : List F)

/-- **The fold rounds' grinding.** If FRI accepts on the ideal primitives of an answer table,
then with grinding every fold round's answer has a first sample with `commitPowBits` vanishing
low bits. -/
theorem commitWitness_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K)
    (hopen : openedValues proof.opened ≠ [])
    (rounds : List (Round F EF)) (st : Sponge F)
    (hfri : verifyFri (idealOf answer) P proof.fri rounds (stateFri (idealOf answer) proof pis) =
      .ok ((), st))
    (i : Nat) (hi : i < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length)
    (hbits : P.commitPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputs P pis proof) (3 + i))).2.toList.getD
      0 0) % 2 ^ P.commitPowBits = 0 := by
  set H := idealOf answer
  have hcws : ∀ j (hj : j < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length),
      (inputs P pis proof).getD (3 + j) [] =
        (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].1.toList ++
          witnessInput P.commitPowBits
            (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)[j].2 := by
    intro j hj
    rw [show 3 + j = 2 + 1 + j by omega]
    exact inputs_getD_fold P pis proof j hj
  set cws := proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList
  set blocks := inputs P pis proof
  rw [verifyFri_eq, bind_ok_of H (sampleExt_eq H _)] at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨betas, st1, hloop, -⟩ := bind_eq_ok H hfri
  have hwit := commitLoop_wit H P cws #[] _ _ hloop i hi
  obtain ⟨-, hs⟩ := batch_idealOf answer P proof pis (by omega) hopen
  erw [hs] at hwit
  have htake : ∀ j (hj : j < (cws.take i).length), blocks.getD (3 + j) [] =
      (cws.take i)[j].1.toList ++ witnessInput P.commitPowBits (cws.take i)[j].2 := by
    intro j hj
    rw [List.length_take] at hj
    rw [List.getElem_take]
    exact hcws j (by omega)
  obtain ⟨-, -, l, hl⟩ :=
    commitReplay_idealOf (EF := EF) answer P (by omega) blocks (cws.take i) 3 _ htake
  rw [hl, List.length_take, Nat.min_eq_left hi.le] at hwit
  have hblock : blocks.getD (3 + i) [] = cws[i].1.toList ++ [cws[i].2] := by
    rw [hcws i hi]
    simp only [witnessInput, hbits, ↓reduceIte]
  rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)] at hwit
  simp only [chkWit, hbits, ↓reduceIte, smpBits, beq_iff_eq] at hwit
  change CompPoly.CanonicalNat.toNat (H.sample ⟨capAt answer blocks (3 + i),
    [] ++ cws[i].1.toList ++ [cws[i].2], []⟩).1 % 2 ^ P.commitPowBits = 0 at hwit
  rw [sample_idealOf_nil, List.nil_append, ← hblock] at hwit
  rw [← List.headD_eq_getD]
  exact hwit

end CompStark.Ni
