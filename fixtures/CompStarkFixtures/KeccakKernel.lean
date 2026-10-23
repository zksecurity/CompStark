/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStarkFixtures.KeccakKernel.Chunks0
import CompStarkFixtures.KeccakKernel.Chunks1
import CompStarkFixtures.KeccakKernel.Chunks2
import CompStarkFixtures.KeccakKernel.Chunks3

/-! # The Keccak AIR's quotient kernel

The program of Plonky3's Keccak AIR's constraints (`Prog.compile`) as straight-line code on groups
of rows (`#gen_group_chunks`), in chunks of 2000 instructions generated in four modules that build
in parallel, each chunk checked equal to the program's code on the group machine by `rfl`:
`CompStark.Fixtures.KeccakKernel.kernel`, for the fast backend's `kernels`.
-/

#gen_group_kernel CompStark.Fixtures.KeccakKernel _root_.KoalaBear.fieldSize
