/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Refines

/-! Certified scalar Keccak for transcript replay and Merkle authentication. -/

@[expose] public section
namespace CompStark.Keccak

/-- The scalar permutation agrees with VCVio on every input array. -/
@[csimp] theorem permutation_native :
    VCVio.Algorithms.Keccak.f1600 = CompStark.Keccak.f1600 :=
  (funext CompStark.Keccak.f1600_eq).symm

/-- Total Keccak-256 using scalar absorption and the reference digest framing. -/
def hashNative (bytes : ByteArray) : ByteArray :=
  if hu : bytes.size < USize.size then CompStark.Keccak.keccak256 bytes hu
  else VCVio.Algorithms.Keccak.squeeze (CompStark.Keccak.absorb bytes) 32

/-- The scalar hash preserves every digest byte, including padding-only final blocks. -/
@[csimp] theorem hash_native : VCVio.Algorithms.Keccak.keccak256 = hashNative := by
  funext bytes
  unfold hashNative
  split
  · exact (CompStark.Keccak.keccak256_eq bytes _).symm
  · simp only [CompStark.Keccak.absorb_eq]
    rfl

end CompStark.Keccak
