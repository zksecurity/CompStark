/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.WitnessTrace

/-! Specification equality and completeness for the native prover with its actual witness builder. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak CompStark.Keccak.Gkr CompStark.BinaryFields BF64

/-- Native witness construction followed by native proving equals the specification at its retained challenges. -/
theorem prove_buildWitness_eq_specificationTranscript (writer : Writer) (committed : Array UInt64)
    (batch output : Array W) (h : Nat) (hb : batch.size=h+8) (hc : committed.size/(2^(h+8))=64)
    (hbound : 1600*(2^(h+8)/64)≤USize.size) (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField))
    (relation : InputRelation (ofK g) out (committedWitness (h+4) committed)) :
    let t := (prove writer (buildWitness (h+8) committed) committed batch output).toProtocol (h+4) (prove_layers_size ..)
    t=specificationTranscript (ofK g) out (committedWitness (h+4) committed) (Challenges.ofTranscript t) :=
  prove_eq_specificationTranscript writer (buildWitness (h+8) committed) committed batch output
    (buildWitness_nLog ..) hb hc (buildWitness_preChiRefines committed relation.1)
    (by rwa [buildWitness_nLog]) out ho

/-- Native witness construction and the complete native prover inherit deterministic verifier and PCS completeness. -/
theorem prove_buildWitness_complete (writer : Writer) (committed : Array UInt64)
    (batch output : Array W) (h : Nat) (hb : batch.size=h+8) (hc : committed.size/(2^(h+8))=64)
    (hbound : 1600*(2^(h+8)/64)≤USize.size) (out : Fin (2^(h+8)) → Fin 25 → E)
    (ho : ∀ l : Fin 25,output[l.val]!.toField=mle (fun b => out b l) (fun i : Fin (h+8) => batch[i.val]!.toField))
    (relation : InputRelation (ofK g) out (committedWitness (h+4) committed)) :
    let t := (prove writer (buildWitness (h+8) committed) committed batch output).toProtocol (h+4) (prove_layers_size ..)
    Accepts (ofK g) out t ∧ TerminalRelation (ofK g) (committedWitness (h+4) committed) t :=
  prove_complete writer (buildWitness (h+8) committed) committed batch output
    (buildWitness_nLog ..) hb hc (buildWitness_preChiRefines committed relation.1)
    (by rwa [buildWitness_nLog]) out ho relation

end CompStark.Keccak.GkrProver
