/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgGen
public import CompStark.KoalaBear.Fast

/-! # Group kernels over KoalaBear

The kernels of programs on groups of rows (`CompStark/Stark/ProgGroup.lean`) over KoalaBear,
compiled with KoalaBear's constants as immediates, for the straight-line code of
`#gen_group_chunks`. This module belongs to the CPU-targeted native library.
-/

@[expose] public section
namespace CompStark.KoalaBear.Group

group_kernels _root_.KoalaBear.fieldSize

end CompStark.KoalaBear.Group
