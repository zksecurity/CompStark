/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.Stark.ProgGen
import CompStark.KoalaBear.Group
import CompStarkFixtures.Keccak

/-! Chunks 15 to 18 of the Keccak AIR's quotient kernel (`CompStarkFixtures/KeccakKernel.lean`). -/

#gen_group_chunks CompStark.Fixtures.KeccakKernel CompStark.KoalaBear.Group
  (CompStark.Stark.Prog.compile
    (CompStark.Fixtures.Keccak.air (F := KoalaBear.Fast.Field)).constraints) 2000 15 19
