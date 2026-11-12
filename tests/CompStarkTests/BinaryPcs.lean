/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Decoder
public import CompStark.Pcs.Radius
public import CompStark.Pcs.Extraction
meta import CompStark.Pcs.Decoder
meta import CompStark.Pcs.Radius
meta import CompStark.Pcs.Extraction

/-! Executable regressions for numeric cube indexing, discrete radii and basis conversion. -/

@[expose] public section
namespace CompStarkTests.BinaryPcs
open CompStark.BinaryFields CompStark.Pcs CompPoly

#guard (List.finRange 256).all fun i => (cubeEquiv 8).symm (mask 8 i) = i
#guard ((cubeEquiv 0).symm (fun i => Fin.elim0 i)).val = 0
#guard agreementCutoff 8192 16384 3 = 15447
#guard agreementCutoff 512 8192 3 = 2728
#guard agreementCutoff 32 4096 3 = 476
#guard !(decide (johnsonAgreement 8192 16384 3 15446)) &&
  decide (johnsonAgreement 8192 16384 3 15447)
#guard !(decide (johnsonAgreement 512 8192 3 2727)) &&
  decide (johnsonAgreement 512 8192 3 2728)
#guard !(decide (johnsonAgreement 32 4096 3 475)) &&
  decide (johnsonAgreement 32 4096 3 476)

/-- A linear polynomial whose normalized novel coefficients are one and one. -/
def linearMessage : Whir.Table K 2 := polynomialMessage (RingHom.id K) 2 (by decide)
  (CPolynomial.C 1 + CPolynomial.X)

#guard (List.finRange 4).map (fun i => linearMessage (mask 2 i)) = [1, 1, 0, 0]

/-- Constant scalar word on the eight-point base-field domain. -/
def constantWordK : Whir.Word K 0 8 := fun _ _ => 1

/-- Constant scalar word on the same domain embedded into the cubic extension. -/
def constantWordE : Whir.Word E 0 8 := fun _ _ => 1

#guard ((gsListDecoder (algebraMap K E) 2 1 0 (by decide) extensionGsContext 7).decode
  (Whir.fullWord constantWordE)).map (fun f => (List.finRange 4).map (fun i => f (mask 2 i))) = [[1, 0, 0, 0]]

/-- Four distinguishable scalar rows exercise ordered parallel row collection. -/
def distinctConstantRows : Whir.Word K 2 8 := fun _ row =>
  K.ofBits (((cubeEquiv 2).symm row).val + 1)

/-- Small executable GS extraction, including the initial claim-dependent selection. -/
def initialExtractionSmoke (claimed : E) : List K :=
  let decoder := gsListDecoder (RingHom.id K) 2 1 0 (by decide) baseGsContext 7
  let claim : Whir.Claim E 2 :=
    ⟨fun u => if u 0 || u 1 then 0 else 1, claimed⟩
  let selected := initialExtractorCached decoder (algebraMap K E) (Whir.fullWord constantWordK) [claim]
  (List.finRange 4).map fun i => selected (mask 2 i)

/-- A dense extension polynomial exercising all three limbs during carrier conversion. -/
def denseConversionPolynomial : CPolynomial E := CPolynomial.ofArray
  ((Array.range 8).map fun i => E.ofLimbs (K.ofBits (2 ^ (i + 48) + i))
    (K.ofBits (i + 7)) (K.ofBits (2 ^ (i + 32))))

#guard extensionGsContext.convert (fun i => ofK (basis i)) 3 (by decide) denseConversionPolynomial =
  AdditiveNTT.monomialToNovelArray (fun i : Fin 64 => ofK (basis i)) 3 (by decide)
    denseConversionPolynomial
#guard extensionGsContext.convert (fun i => ofK (basis i)) 3 (by decide) 0 = Array.replicate 8 0

/-- A dense novel message retains high bits in each cubic-field limb. -/
def denseConversionMessage : Whir.Table E 3 :=
  polynomialMessage (algebraMap K E) 3 (by decide) denseConversionPolynomial

#guard (extensionGsContext.encodeRows (algebraMap K E) 3 1 0 (by decide) denseConversionMessage)[0] =
  encodeArray (algebraMap K E) 3 1 (by decide) denseConversionMessage

/-- Two distinct preimages of the zero restriction test validity preference and fallback. -/
def liftCandidate (value : Nat) : Whir.Table E 1 :=
  fun u => if u 0 then ofK (K.ofBits value) else 0

/-- Observe an ordered backward selection with an explicitly checked retained claim. -/
def foldLiftSmoke (claimed : Nat) (successor : Nat) : List E :=
  let claim : Whir.Claim E 1 := ⟨fun u => if u 0 then 1 else 0, ofK (K.ofBits claimed)⟩
  let selected := foldLiftCached (vars := 0) [liftCandidate 1, liftCandidate 2]
    0 claim (fun _ => ofK (K.ofBits successor))
  (List.finRange 2).map fun i => selected (mask 1 i)

#guard foldLiftSmoke 2 0 = [0, ofK (K.ofBits 2)]
#guard foldLiftSmoke 3 0 = [0, 1]
#guard foldLiftSmoke 2 1 = [0, 0]

/-- Compiled base-field decoding exercises the packed encoder and both initial-claim outcomes. -/
def checkPacked : IO Unit := do
  unless (((gsListDecoder (RingHom.id K) 2 1 0 (by decide) baseGsContext 7).decode
      (Whir.fullWord constantWordK)).map (fun f => (List.finRange 4).map (fun i => f (mask 2 i))) = [[1, 0, 0, 0]]) do
    throw (IO.userError "PCS packed encoder: constant base word")
  unless (((gsListDecoder (RingHom.id K) 2 1 2 (by decide) baseGsContext 7).decode
      (Whir.fullWord distinctConstantRows)).map (fun f => (List.finRange 16).map (fun i => f (mask 4 i))) =
        [(List.finRange 16).map fun i => if i.val < 4 then K.ofBits (i.val + 1) else 0]) do
    throw (IO.userError "PCS packed encoder: ordered base rows")
  unless (initialExtractionSmoke 1 = [1, 0, 0, 0]) do
    throw (IO.userError "PCS packed encoder: true initial claim")
  unless (initialExtractionSmoke 0 = [0, 0, 0, 0]) do
    throw (IO.userError "PCS packed encoder: false initial claim")

end CompStarkTests.BinaryPcs
