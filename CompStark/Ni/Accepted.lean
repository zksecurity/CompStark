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
  first sample of the round's answer has `commitPowBits` vanishing low bits; and likewise for the
  out-of-domain and batching rounds (`oodWitness_idealOf`, `batchWitness_idealOf`).
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
      ⟨keyAt answer (inputs P A pis proof) 0, answer (keyAt answer (inputs P A pis proof) 0)⟩ ::
        rest := by
  unfold verifyWith at hok ⊢
  dsimp only at hok ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hdeg
  simp only [hdeg, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hpis
  simp only [hpis, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hshape
  simp only [hshape, ↓reduceIte] at ⊢
  split at hok
  swap
  · simp only [ExceptT.run_bind, ExceptT.run_throw, pure_bind] at hok
    cases hok
  rename_i hoodw
  simp only [hoodw, ↓reduceIte] at ⊢
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
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [out_observeList_nil] at h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, out_observeList_nil, List.nil_append]
  have hin₀ : DomainSeparator.starkSeed F EF proof.degreeBits A.width A.numPublicValues
      (2 ^ A.logQuotientChunks) P.oodPowBits ++ proof.traceCommit.toList ++ pis =
      (inputs P A pis proof).getD 0 [] := by
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
  simp only [List.nil_append] at hrun1 ⊢
  rw [hin₀, show initCap = capAt answer (inputs P A pis proof) 0 from rfl] at hrun1 ⊢
  have hv₀ := out_sampleExt_nil (EF := EF) answer hK (capAt answer (inputs P A pis proof) 0)
    ((inputs P A pis proof).getD 0 [])
  obtain ⟨_, s₁, h₁, hrun1, hlog⟩ := out_bind_ok answer hrun1
  rw [hv₀] at h₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h₁)
  rw [hlog, hv₀]
  exact ⟨_, rfl⟩

/-! ### The fold rounds' grinding -/

section Commit
variable (H : Primitives F Id) (P : Params)

/-- An accepting commit loop passes every grinding check, from the state `commitReplay` reaches
before each round. -/
theorem commitLoop_wit (body : Digest F × F → Array EF → M H (ForInStep (Array EF)))
    (hbody : ∀ cw betas, body cw betas = commitBody H P cw betas) :
    ∀ (cws : List (Digest F × F)) (betas : Array EF) (s : H.State) (r : Array EF × H.State),
      forIn (m := M H) cws betas body s = .ok r →
        ∀ i (hi : i < cws.length), (chkWit H P.commitPowBits cws[i].2
          (obsList H (commitReplay (EF := EF) H P (cws.take i) s).2 cws[i].1.toList)).1 = true
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | cw :: cws, betas, s, r, h, i, hi => by
    obtain ⟨step, st', h1, h2⟩ := forIn_cons_eq_ok H _ _ _ _ _ _ h
    rw [hbody] at h1
    unfold commitBody at h1
    rw [bind_ok_of H (observeList_eq H _ s), bind_ok_of H (checkWitness_eq H _ _ _)] at h1
    obtain ⟨hwit, h1⟩ := ensure_bind_eq_ok H h1
    rw [bind_ok_of H (sampleExt_eq H _)] at h1
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (pure_eq_ok H h1)
    subst hs1 hs2
    cases i with
    | zero => exact hwit
    | succ i =>
      exact commitLoop_wit body hbody cws _ _ r h2 i (by simp only [List.length_cons] at hi; omega)

end Commit

variable (P : Params) (A : Air F) (proof : Proof F EF) (pis : List F)

/-- **The fold rounds' grinding.** If FRI accepts after the batching challenge on the ideal
primitives of an answer table, then with grinding every fold round's answer has a first sample
with `commitPowBits` vanishing low bits. -/
theorem commitWitness_idealOf (hK : P.numQueries + Challenge.d EF + 1 ≤ K)
    (rounds : List (Round F EF))
    (hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [friLogMax P proof])
    (st : Sponge F)
    (hfri : verifyFri (idealOf answer) P proof.fri rounds (batchOf (idealOf answer) P A proof pis)
      (stateFri (idealOf answer) P A proof pis) = .ok ((), st))
    (i : Nat) (hi : i < (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList).length)
    (hbits : P.commitPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputs P A pis proof)
      (3 + i))).2.toList.getD 0 0) % 2 ^ P.commitPowBits = 0 := by
  set H := idealOf answer
  set cws := proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList
  set blocks := inputs P A pis proof
  unfold verifyFri at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  simp only [hheights, List.headD_cons] at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  rw [bind_ok_of H (observeList_eq H _ _)] at hfri
  obtain ⟨-, hfri⟩ := ensure_bind_eq_ok H hfri
  obtain ⟨betas, st1, hloop, -⟩ := bind_eq_ok H hfri
  have hwit := commitLoop_wit H P _ (fun _ _ ↦ rfl) cws #[] _ _ hloop i hi
  have hstart : obsList H (stateFri H P A proof pis) (friSeedOf P proof) =
      ⟨capAt answer blocks 3, friSeedOf P proof, []⟩ := by
    obtain ⟨-, l₀, hl₀⟩ := batch_idealOf answer P A proof pis (by omega)
    rw [hl₀, obsList_idealOf_ne answer _ _ (friSeed_ne_nil _ _ _ _ _ _ _ _)]
    rfl
  erw [hstart] at hwit
  have htake : ∀ j (hj : j < (cws.take i).length), blocks.getD (3 + j) [] =
      seedAt (friSeedOf P proof) j ++ (cws.take i)[j].1.toList ++
        witnessInput P.commitPowBits (cws.take i)[j].2 := by
    intro j hj
    rw [List.length_take] at hj
    rw [List.getElem_take]
    exact inputs_getD_fold P A pis proof j (Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _))
  obtain ⟨-, -, l, hl⟩ :=
    commitReplay_idealOf (EF := EF) answer P (by omega) blocks (cws.take i) 3 _ [] htake
  rw [hl, List.length_take, Nat.min_eq_left hi.le] at hwit
  have hblock : blocks.getD (3 + i) [] = seedAt (friSeedOf P proof) i ++ cws[i].1.toList ++
      [cws[i].2] := by
    rw [inputs_getD_fold P A pis proof i hi]
    simp only [witnessInput, hbits, ↓reduceIte]
    rfl
  rw [obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)] at hwit
  simp only [chkWit, hbits, ↓reduceIte, smpBits, beq_iff_eq] at hwit
  change CompPoly.CanonicalNat.toNat (H.sample ⟨capAt answer blocks (3 + i),
    seedAt (friSeedOf P proof) i ++ cws[i].1.toList ++ [cws[i].2], []⟩).1 %
      2 ^ P.commitPowBits = 0 at hwit
  rw [sample_idealOf_nil, ← hblock] at hwit
  rw [← List.headD_eq_getD]
  exact hwit

/-! ### The out-of-domain and batching rounds' grinding -/

/-- A round's grinding check passes after observing `input` on a fresh duplex state: with
grinding, the first sample of the round's answer has `bits` vanishing low bits. -/
theorem grindWitness_idealOf (blocks : List (List F)) (r : Nat) (input : List F) (bits : Nat)
    (w : F) (hr : blocks.getD r [] = input ++ witnessInput bits w) (hbits : bits ≠ 0)
    (h : (chkWit (idealOf answer) bits w ⟨capAt answer blocks r, input, []⟩).1 = true) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer blocks r)).2.toList.getD 0 0) %
      2 ^ bits = 0 := by
  simp only [witnessInput, hbits, ↓reduceIte] at hr
  simp only [chkWit, hbits, ↓reduceIte, smpBits, beq_iff_eq] at h
  change CompPoly.CanonicalNat.toNat ((idealOf answer).sample
    ⟨capAt answer blocks r, input ++ [w], []⟩).1 % 2 ^ bits = 0 at h
  rw [sample_idealOf_nil, ← hr] at h
  rw [← List.headD_eq_getD]
  exact h

/-- **The out-of-domain round's grinding.** If the out-of-domain grinding check passes on the
ideal primitives of an answer table, then with grinding the first sample of round `1`'s answer
has `oodPowBits` vanishing low bits. -/
theorem oodWitness_idealOf (hK : Challenge.d EF ≤ K)
    (hood : (oodCheck (EF := EF) (idealOf answer) P A proof pis).1 = true)
    (hbits : P.oodPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputs P A pis proof) 1)).2.toList.getD
      0 0) % 2 ^ P.oodPowBits = 0 := by
  have hst : obsList (idealOf answer) (smpExt (EF := EF) (idealOf answer)
      (stateAlpha (idealOf answer) P A proof pis)).2 proof.quotientCommit.toList =
      ⟨capAt answer (inputs P A pis proof) 1, proof.quotientCommit.toList, []⟩ := by
    rw [(alpha_idealOf answer P A proof pis hK).2,
      obsList_idealOf_ne answer _ _ (digest_toList_ne_nil _)]
    rfl
  rw [oodCheck, hst] at hood
  exact grindWitness_idealOf answer _ 1 _ _ _ (by
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]) hbits hood

/-- **The batching round's grinding.** If the batching grinding check passes on the ideal
primitives of an answer table, then with grinding the first sample of round `2`'s answer has
`batchPowBits` vanishing low bits. -/
theorem batchWitness_idealOf (hK : Challenge.d EF + 1 ≤ K)
    (hbc : (batchCheck (idealOf answer) P A proof pis).1 = true)
    (hbits : P.batchPowBits ≠ 0) :
    CompPoly.CanonicalNat.toNat ((answer (keyAt answer (inputs P A pis proof) 2)).2.toList.getD
      0 0) % 2 ^ P.batchPowBits = 0 := by
  obtain ⟨-, l, hl⟩ := zeta_idealOf answer P A proof pis hK
  have hst : pcsState (idealOf answer) P (vRounds proof (zetaOf (idealOf answer) P A proof pis))
      (smpExt (EF := EF) (idealOf answer) (oodCheck (EF := EF) (idealOf answer) P A proof
        pis).2).2 =
      ⟨capAt answer (inputs P A pis proof) 2, DomainSeparator.pcsSeed F EF
        (pcsCounts proof.opened) P.batchPowBits ++ coeffs (openedValues proof.opened), []⟩ := by
    rw [hl, pcsState, obsOpened_eq, roundValues_vRounds', claimCounts_vRounds,
      obsList_idealOf_ne answer _ _ (pcsSeed_ne_nil _ _), obsList_idealOf answer _ rfl]
    rfl
  rw [batchCheck, hst] at hbc
  exact grindWitness_idealOf answer _ 2 _ _ _ (by
    simp only [inputs, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]) hbits hbc

end CompStark.Ni
