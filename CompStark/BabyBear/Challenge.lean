/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BabyBear.Field
public import CompStark.Mont32.Challenge
public import CompPoly.Fields.BabyBear.FastExt4

/-! # The challenge field of the BabyBear STARK

CompPoly's fast quartic extension `BabyBear.Fast.Ext4`, `BabyBear[X] / (X^4 - 11)`, Plonky3's
`BinomialExtensionField<BabyBear, 4>`, is a challenge field by the quartic extensions of fast
Montgomery fields (`Mont32.instChallengeExt4`) and CompPoly's `Binomial4` instance for BabyBear.
-/
