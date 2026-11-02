/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.FriSchedule

/-! # FRI's rounds on fixed words

FRI's run on fixed committed words (`Rounds.run`): fold `j` folds word `words j`, read on its
domain, at `βs j`, injecting the rounds' input, and the final word is a polynomial on the final
domain. An accepted batch proof's queries are accepted by the run on the words extracted under its
commitments (`Fs/FriInjected.lean`).
-/

@[expose] public section

namespace CompStark.Sound.FriRounds

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri FriInject
open OracleComp
open scoped BigOperators ProbabilityTheory NNReal

variable {K : Type} [Field K]

namespace Rounds

/-- FRI's run on fixed words: fold `j` folds `words j`, read on its domain, at `βs j`, and the
final word is `fp` on the final domain. -/
def run (d : ℕ) (hd : 0 < d) : (words : ℕ → (m : ℕ) → Fin (2 ^ m) → K) → (fp : K[X]) →
    (βs : ℕ → K) → {n : ℕ} → (ω : SmoothCosetFftDomain n K) → (r : Rounds K n) →
      InjectTrace ω (r.degree d)
  | _, fp, _, _, ω, .final => .terminal fun x ↦ fp.eval (ω x)
  | words, fp, βs, n, ω, .fold k hk none rest =>
      .fold hk (degree_pos hd rest) (words 0 n) (βs 0)
        (run d hd (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
  | words, fp, βs, n, ω, .fold k hk (some g) rest =>
      .inject hk (degree_pos hd rest) (words 0 n) (βs 0) g
        (run d hd (fun j ↦ words (j + 1)) fp (fun j ↦ βs (j + 1)) (ω.subdomain k) rest)
termination_by structural _ _ _ _ _ r => r

variable [DecidableEq K]

end Rounds

namespace Rounds

variable (d : ℕ) (hd : 0 < d)

end Rounds

end CompStark.Sound.FriRounds
