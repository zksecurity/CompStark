/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.ProverRun
public import CompStark.Compiled.GrandProductProver

/-! The grand-product prover's ideal run is the honest descent at the coins the duplex draws
(`grandProduct_idealRun`). -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Keccak CompStark.Multilinear CompStark.Multilinear.GrandProduct
open Interaction Interaction.Oracle Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

variable (μ : ℕ) (leaves : Fin 3 → ℕ → E)

/-- Honest rounds read their continuation only at the full prefix. -/
theorem honestRounds_congr (m ρ : ℕ) (lam : E) (point : List E) {tail : Protocol}
    (first second : List E → tail.tree.ExecutionPath) :
    (n : ℕ) → (χ : List E) → (rs : Fin n → E) → first (χ ++ List.ofFn rs) = second (χ ++ List.ofFn rs) →
      honestRounds μ leaves m ρ lam point tail first n χ rs =
        honestRounds μ leaves m ρ lam point tail second n χ rs
  | 0, χ, rs, h => by
      rw [List.ofFn_zero, List.append_nil] at h
      exact h
  | n + 1, χ, rs, h => by
      rw [honestRounds.eq_2, honestRounds.eq_2,
        honestRounds_congr m ρ lam point first second n (χ ++ [rs 0]) (Fin.tail rs) (by
          rw [List.append_assoc, List.singleton_append]
          rw [List.ofFn_succ] at h
          exact h)]

/-- Honest interpolation reads its continuation only at the full child point. -/
theorem honestInterpolation_congr {tail : Protocol} (first second : List E → tail.tree.ExecutionPath) :
    (n : ℕ) → (u : List E) → (us : Fin n → E) → first (u ++ List.ofFn us) = second (u ++ List.ofFn us) →
      honestInterpolation tail first n u us = honestInterpolation tail second n u us
  | 0, u, us, h => by
      rw [List.ofFn_zero, List.append_nil] at h
      exact h
  | n + 1, u, us, h => by
      rw [honestInterpolation.eq_2, honestInterpolation.eq_2,
        honestInterpolation_congr first second n (u ++ [us 0]) (Fin.tail us) (by
          rw [List.append_assoc, List.singleton_append]
          rw [List.ofFn_succ] at h
          exact h)]

/-- The rounds prover's ideal run draws its challenges and then runs the continuation's prover at
the full prefix; its path is the honest rounds into the continuation's path. -/
theorem grandRounds_idealRun (m ρ : ℕ) (lam : E) (point : List E) {tail : Protocol}
    (suffix : Presentation tail) (afterProver : List E → suffix.Prover) :
    (n : ℕ) → (χ : List E) → (state : Transcript.State) → ∃ rs : Fin n → E, ∃ reached,
      (grandRounds (2 ^ ρ) suffix n).idealRun
        (grandRoundsProver suffix (2 ^ ρ) (fun χ => honestMessage μ m ρ leaves lam point χ) afterProver n χ)
        state = (suffix.idealRun (afterProver (χ ++ List.ofFn rs)) reached).map fun result =>
          (honestRounds μ leaves m ρ lam point tail (fun _ => result.1) n χ rs, result.2)
  | 0, χ, state => by
      refine ⟨Fin.elim0, state, ?_⟩
      rw [List.ofFn_zero, List.append_nil]
      change suffix.idealRun (afterProver χ) state = _
      cases suffix.idealRun (afterProver χ) state <;> rfl
  | n + 1, χ, state => by
      let message : Message (2 ^ ρ) := fun i => (Vector.ofFn (honestMessage μ m ρ leaves lam point χ))[i]
      have honest : message = honestMessage μ m ρ leaves lam point χ := by
        funext i
        simp only [message, Fin.getElem_fin, Vector.getElem_ofFn]
      let drawn := scalarDraw.run (Transcript.replay state (fieldEvents message))
      obtain ⟨rs, reached, h⟩ := grandRounds_idealRun m ρ lam point suffix afterProver n
        (χ ++ [drawn.1]) drawn.2
      refine ⟨Fin.cons drawn.1 rs, reached, ?_⟩
      have unfolded : (grandRounds (2 ^ ρ) suffix (n + 1)).idealRun
          (grandRoundsProver suffix (2 ^ ρ) (fun χ => honestMessage μ m ρ leaves lam point χ) afterProver
            (n + 1) χ) state =
          Option.map (fun result => (⟨message, result.1⟩, result.2))
            (Option.map (fun result => (⟨some drawn.1, result.1⟩, result.2))
              ((grandRounds (2 ^ ρ) suffix n).idealRun
                (grandRoundsProver suffix (2 ^ ρ) (fun χ => honestMessage μ m ρ leaves lam point χ)
                  afterProver n (χ ++ [drawn.1])) drawn.2)) := rfl
      have prefixes : χ ++ List.ofFn (Fin.cons drawn.1 rs) = χ ++ [drawn.1] ++ List.ofFn rs := by
        rw [List.ofFn_succ, Fin.cons_zero, List.append_assoc, List.singleton_append]
        simp only [Fin.cons_succ]
      rw [unfolded, h, prefixes]
      cases suffix.idealRun (afterProver (χ ++ [drawn.1] ++ List.ofFn rs)) reached with
      | none => rfl
      | some result =>
          change some (_, result.2) = some (_, result.2)
          rw [honestRounds.eq_2, Fin.cons_zero, Fin.tail_cons, ← honest]

/-- The interpolation prover's ideal run draws the child point and then runs the continuation's
prover at it. -/
theorem interpolation_idealRun {tail : Protocol} (suffix : Presentation tail)
    (afterProver : List E → suffix.Prover) :
    (n : ℕ) → (u : List E) → (state : Transcript.State) → ∃ us : Fin n → E, ∃ reached,
      (interpolation suffix n).idealRun (interpolationProver suffix afterProver n u) state =
        (suffix.idealRun (afterProver (u ++ List.ofFn us)) reached).map fun result =>
          (honestInterpolation tail (fun _ => result.1) n u us, result.2)
  | 0, u, state => by
      refine ⟨Fin.elim0, state, ?_⟩
      rw [List.ofFn_zero, List.append_nil]
      change suffix.idealRun (afterProver u) state = _
      cases suffix.idealRun (afterProver u) state <;> rfl
  | n + 1, u, state => by
      let drawn := scalarDraw.run state
      obtain ⟨us, reached, h⟩ := interpolation_idealRun suffix afterProver n (u ++ [drawn.1]) drawn.2
      refine ⟨Fin.cons drawn.1 us, reached, ?_⟩
      have unfolded : (interpolation suffix (n + 1)).idealRun (interpolationProver suffix afterProver (n + 1) u)
          state = Option.map (fun result => (⟨drawn.1, result.1⟩, result.2))
            ((interpolation suffix n).idealRun (interpolationProver suffix afterProver n (u ++ [drawn.1]))
              drawn.2) := rfl
      have prefixes : u ++ List.ofFn (Fin.cons drawn.1 us) = u ++ [drawn.1] ++ List.ofFn us := by
        rw [List.ofFn_succ, Fin.cons_zero, List.append_assoc, List.singleton_append]
        simp only [Fin.cons_succ]
      rw [unfolded, h, prefixes]
      cases suffix.idealRun (afterProver (u ++ [drawn.1] ++ List.ofFn us)) reached with
      | none => rfl
      | some result =>
          change some (_, result.2) = some (_, result.2)
          rw [honestInterpolation.eq_2, Fin.cons_zero, Fin.tail_cons]

set_option maxHeartbeats 1600000 in
/-- The grand-product prover's ideal run is the honest descent at the drawn coins, into the
terminal prover's path. -/
theorem grandProduct_idealRun {tail : Protocol} (suffix : Presentation tail)
    (tailProver : Claim → suffix.Prover) (tailPath : Claim → tail.tree.ExecutionPath)
    (terminal : ∀ c state, ∃ final, suffix.idealRun (tailProver c) state = some (tailPath c, final)) :
    (steps : List ℕ) → (m : ℕ) → (c : Claim) → (state : Transcript.State) → ∃ coins final,
      (grandProduct suffix steps m).idealRun (grandProductProver μ leaves suffix tailProver steps m c) state =
        some (honestPath μ leaves tail tailPath steps m c coins, final)
  | [], _, c, state => by
      obtain ⟨final, h⟩ := terminal c state
      exact ⟨PUnit.unit, final, h⟩
  | ρ :: rest, m, c, state => by
      let lam := (scalarDraw.run state).1
      let childAfter : List E → (childrenStep suffix rest m ρ).Prover := fun χ => fun _ =>
        let children := Vector.ofFn fun s => Vector.ofFn (honestChildren μ leaves m ρ χ s)
        let values : Fin 3 → Fin (2 ^ ρ) → E := fun s i => children[s][i]
        ⟨values, interpolationProver (grandProduct suffix rest (m + ρ))
          (fun u => grandProductProver μ leaves suffix tailProver rest (m + ρ)
            (let point := u ++ χ
             let claimed := Vector.ofFn fun s => interpolated ρ values u s 0
             ⟨point, fun s => claimed[s]⟩)) ρ []⟩
      have unfolded : (grandProduct suffix (ρ :: rest) m).idealRun
          (grandProductProver μ leaves suffix tailProver (ρ :: rest) m c) state =
          ((grandRounds (2 ^ ρ) (childrenStep suffix rest m ρ) m).idealRun
            (grandRoundsProver (childrenStep suffix rest m ρ) (2 ^ ρ)
              (fun χ => honestMessage μ m ρ leaves lam c.point χ) childAfter m [])
            (scalarDraw.run state).2).map fun result => (⟨lam, result.1⟩, result.2) := rfl
      obtain ⟨rs, reached, rounds⟩ := grandRounds_idealRun μ leaves m ρ lam c.point
        (childrenStep suffix rest m ρ) childAfter m [] (scalarDraw.run state).2
      let χ := [] ++ List.ofFn rs
      let children := Vector.ofFn fun s => Vector.ofFn (honestChildren μ leaves m ρ χ s)
      let values : Fin 3 → Fin (2 ^ ρ) → E := fun s i => children[s][i]
      have honestValues : values = honestChildren μ leaves m ρ χ := by
        funext s i
        simp only [values, children, Fin.getElem_fin, Vector.getElem_ofFn]
      let claim : List E → Claim := fun u =>
        let point := u ++ χ
        let claimed := Vector.ofFn fun s => interpolated ρ values u s 0
        ⟨point, fun s => claimed[s]⟩
      have child : (childrenStep suffix rest m ρ).idealRun (childAfter χ) reached =
          ((interpolation (grandProduct suffix rest (m + ρ)) ρ).idealRun
            (interpolationProver (grandProduct suffix rest (m + ρ))
              (fun u => grandProductProver μ leaves suffix tailProver rest (m + ρ) (claim u)) ρ [])
            (Transcript.replay reached (fieldEvents fun i : Fin (3 * 2 ^ ρ) =>
              values ⟨i.val / 2 ^ ρ, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr i.isLt⟩
                ⟨i.val % 2 ^ ρ, Nat.mod_lt _ (Nat.two_pow_pos _)⟩))).map
            fun result => (⟨values, result.1⟩, result.2) := rfl
      obtain ⟨us, reached', interpolated⟩ := interpolation_idealRun (grandProduct suffix rest (m + ρ))
        (fun u => grandProductProver μ leaves suffix tailProver rest (m + ρ) (claim u)) ρ [] _
      let u := [] ++ List.ofFn us
      obtain ⟨coins, final, next⟩ := grandProduct_idealRun suffix tailProver tailPath terminal rest (m + ρ)
        (claim u) reached'
      refine ⟨(lam, rs, us, coins), final, ?_⟩
      rw [unfolded, rounds, child, interpolated, next]
      change some ((⟨lam, honestRounds μ leaves m ρ lam c.point
        (.public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ => interpolationProtocol (protocol tail rest (m + ρ)) ρ)
        (fun _ => ⟨values, honestInterpolation (protocol tail rest (m + ρ)) (fun _ => honestPath μ leaves tail tailPath rest (m + ρ) (claim u) coins)
          ρ [] us⟩) m [] rs⟩ : (protocol tail (ρ :: rest) m).tree.ExecutionPath), final) = _
      have claimed : claim u = ⟨u ++ χ, fun s => GrandProduct.interpolated ρ
          (honestChildren μ leaves m ρ χ) u s 0⟩ := by
        show (⟨u ++ χ, fun s => (Vector.ofFn fun s => GrandProduct.interpolated ρ values u s 0)[s]⟩ : Claim) = _
        congr 1
        funext s
        rw [Fin.getElem_fin, Vector.getElem_ofFn, honestValues]
      rw [honestRounds_congr μ leaves m ρ lam c.point
          (tail := .public .sender (Fin 3 → Fin (2 ^ ρ) → E) fun _ =>
            interpolationProtocol (protocol tail rest (m + ρ)) ρ) _ (fun χ' => ⟨honestChildren μ leaves m ρ χ',
          honestInterpolation (protocol tail rest (m + ρ))
            (fun u' => honestPath μ leaves tail tailPath rest (m + ρ)
              ⟨u' ++ χ', fun s => GrandProduct.interpolated ρ (honestChildren μ leaves m ρ χ') u' s 0⟩ coins)
            ρ [] us⟩) m [] rs (by
          beta_reduce
          rw [honestValues, honestInterpolation_congr _ (fun u' => honestPath μ leaves tail tailPath rest (m + ρ)
            ⟨u' ++ χ, fun s => GrandProduct.interpolated ρ (honestChildren μ leaves m ρ χ) u' s 0⟩ coins)
            ρ [] us (by beta_reduce; rw [claimed])])]
      rw [honestPath.eq_2]

end CompStark.Compiled
