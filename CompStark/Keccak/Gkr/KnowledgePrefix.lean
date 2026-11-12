/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeSchedule

/-! # Accepting-completion adapters for authored GKR prefixes -/

@[expose] public section
namespace CompStark.Keccak.Gkr

/-- Authorship of one wire vector advances the aligned semantic suffix by one cut. -/
theorem cuts_drop_append {E : Type} {p : Nat} (history : List (List E)) (message : List E)
    (step : WireStep) (c : Cut) (rest : List (WireStep × Cut))
    (aligned : (cuts p).drop history.length = ((step, c) :: rest).map Prod.snd) :
    (cuts p).drop (history ++ [message]).length = rest.map Prod.snd := by
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    List.drop_add_one_eq_tail_drop, aligned, List.map_cons, List.tail_cons]

/-- The aligned semantic suffix identifies the current cut in the full schedule. -/
theorem cuts_getElem_of_drop {p n : Nat} (step : WireStep) (c : Cut)
    (rest : List (WireStep × Cut)) (aligned : (cuts p).drop n = ((step, c) :: rest).map Prod.snd) :
    (cuts p)[n]? = some c := by
  have h := congrArg List.head? aligned
  simpa only [List.head?_drop, List.map_cons, List.head?_cons] using h

/-- Prefix knowledge supplies one accepting completion with the aligned residual or PCS relation. -/
theorem nextPrefixClaim_completion {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (nodes : List (WireStep × Cut)) (history : List (List E))
    (aligned : (cuts p).drop history.length = nodes.map Prod.snd)
    (good : nextPrefixClaim x output (nodes.map Prod.fst) history q) :
    ∃ t : Transcript E p, history <+: transcriptMessages t ∧ Accepts x output t ∧
      optionalCutHolds x output q t (nodes.head?.map Prod.snd) := by
  cases nodes with
  | nil =>
    obtain ⟨t, he, checks, terminal⟩ := good
    exact ⟨t, he ▸ List.prefix_refl _, checks, terminal⟩
  | cons node rest =>
    obtain ⟨c, hc, t, hpref, checks, residual⟩ := good
    have hcut := cuts_getElem_of_drop node.1 node.2 rest aligned
    have he : c = node.2 := Option.some.inj (hc.symm.trans hcut)
    subst c
    exact ⟨t, hpref, checks, residual⟩

/-- Appending a prover message preserves the previous prefix claim at its semantic boundary. -/
theorem prefix_message_preserving {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (q : Witness p)
    (n : Nat) (c : Cut) (rest : List (WireStep × Cut))
    (history : List (List E)) (message : Fin n → E)
    (aligned : (cuts p).drop history.length = ((.message n, c) :: rest).map Prod.snd)
    (boundary : MessageBoundary p c (rest.head?.map Prod.snd))
    (good : nextPrefixClaim x output (rest.map Prod.fst) (history ++ [List.ofFn message]) q) :
    prefixClaim x output history q := by
  obtain ⟨t, hpref, checks, residual⟩ := nextPrefixClaim_completion x output q rest
    (history ++ [List.ofFn message]) (cuts_drop_append history _ _ c rest aligned) good
  refine ⟨c, cuts_getElem_of_drop _ c rest aligned, t, ?_, checks, ?_⟩
  · exact (List.prefix_append history _).trans hpref
  · exact messageBoundary_preserving x output q t checks boundary residual

/-- An identified semantic cut removes the existential cut index from prefix knowledge. -/
theorem prefixClaim_at {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (output : Fin (2^(p+4)) → Fin 25 → E) (history : List (List E))
    (q : Witness p) (c : Cut) (hc : (cuts p)[history.length]? = some c) :
    prefixClaim x output history q ↔ ∃ t : Transcript E p,
      history <+: transcriptMessages t ∧ Accepts x output t ∧ cutHolds x output q t c := by
  constructor
  · rintro ⟨c', hc', t, ht, checks, good⟩
    have he : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst c'
    exact ⟨t, ht, checks, good⟩
  · rintro ⟨t, ht, checks, good⟩
    exact ⟨c, hc, t, ht, checks, good⟩

end CompStark.Keccak.Gkr
