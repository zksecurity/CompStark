/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStarkFixtures.KeccakMerkle
import Lean.Data.Json.Parser
import Lean.Util.CollectAxioms

/-! # Rust-conformant streaming Merkle trees and observed duplex writer -/

namespace CompStarkTests.KeccakMerkle
open CompStark.Keccak CompStark.Fixtures.KeccakMerkle
open Lean

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def nums (json : Json) : Except String (Array Nat) := do
  (← json.getArr?).mapM Json.getNat?

private def bytes (json : Json) : Except String ByteArray := do
  return ByteArray.mk ((← nums json).map Nat.toUInt8)

private def lanes (json : Json) : Except String (Array UInt64) := do
  return (← nums json).map Nat.toUInt64

/-- Exact roots and canonical openings on the unchanged Rust builder's inputs. -/
def trees (fixtures : Array Json) : IO Unit := do
  for fixture in fixtures do
    let depth ← IO.ofExcept ((← IO.ofExcept (fixture.getObjVal? "depth")).getNat?)
    let width ← IO.ofExcept ((← IO.ofExcept (fixture.getObjVal? "width")).getNat?)
    if hw : width ≤ 64 then
      let input := rows (2 ^ depth) width hw
      let queries := (← IO.ofExcept (nums (← IO.ofExcept (fixture.getObjVal? "queries")))).toList
      let expectedRoot ← IO.ofExcept (bytes (← IO.ofExcept (fixture.getObjVal? "root")))
      let expectedSiblings ← IO.ofExcept ((← IO.ofExcept
        ((← IO.ofExcept (fixture.getObjVal? "siblings")).getArr?)).mapM bytes)
      let expectedRows ← IO.ofExcept ((← IO.ofExcept
        ((← IO.ofExcept (fixture.getObjVal? "leaf_data")).getArr?)).mapM bytes)
      let tree ← IO.ofExcept (Merkle.commit input)
      check "Merkle root differs from Rust" (tree.2.root.val == expectedRoot)
      let opening ← IO.ofExcept (tree.2.open queries)
      check "canonical pruned siblings differ from Rust"
        (opening.siblingHashes.map Subtype.val == expectedSiblings.toList)
      check "leaf images differ from Rust" (opening.leafData.map (·.bytes) == expectedRows.toList)
      check "opening row order" (opening.leafData.map (·.bytes) ==
        (Merkle.positions queries).map (fun q ↦ (row width hw q).bytes))
      check "honest sparse opening rejected" (Merkle.verify tree.1 tree.2.root queries opening)
      let builder := (input.toList.foldl (fun b r ↦ b.absorb #[r]) ({} : Merkle.Builder))
      let streamed ← IO.ofExcept builder.finish
      check "streaming root" (streamed.2.root.val == expectedRoot)
      if depth > 0 then
        check "truncated proof accepted" (!Merkle.verify tree.1 tree.2.root queries
          { opening with leafData := opening.leafData.tail })
      let extra : Merkle.Digest := ⟨ByteArray.mk (Array.replicate 32 0), by rfl⟩
      check "spurious sibling accepted" (!Merkle.verify tree.1 tree.2.root queries
        { opening with siblingHashes := opening.siblingHashes ++ [extra] })
      check "empty query accepted" ((tree.2.open []).toOption.isNone)
      check "out-of-domain query accepted" ((tree.2.open [2 ^ tree.1]).toOption.isNone)
    else throw (IO.userError "invalid reference width")
  check "empty commitment accepted" ((Merkle.commit #[]).toOption.isNone)
  check "incomplete commitment accepted" ((Merkle.commit (rows 3 8 (by decide))).toOption.isNone)

/-- Capture every actual permutation, including seed and full-buffer flushes. -/
def observe (events : Array (Array UInt64 × Array UInt64)) (input output : Array UInt64) :=
  events.push (input, output)

/-- Exact overwrite/clear semantics against Rust's production FiatShamirState. -/
def duplex (fixtures : Array Json) : IO (Duplex.State rate Unit) := do
  let mut writer : Duplex.Writer rate (Array UInt64) (Array (Array UInt64 × Array UInt64)) :=
    ⟨(Duplex.sample rate observe (seed #[]) 0 (by decide)).2, #[]⟩
  let mut messages := 0
  for count in [0, 1, 4, 5, 8, 9] do
    for k in [0:count] do
      writer := writer.write rate observe id (framed (count * 100 + k + 1).toUInt64)
      messages := messages + 1
    writer := (writer.sample rate observe 3 (by decide)).2
  check "writer dropped transmitted messages" (writer.stream.size == messages)
  check "observer permutation count" (writer.state.observed.size == fixtures.size)
  for event in writer.state.observed.zip fixtures do
    let input ← IO.ofExcept (lanes (← IO.ofExcept (event.2.getObjVal? "input")))
    let output ← IO.ofExcept (lanes (← IO.ofExcept (event.2.getObjVal? "output")))
    check "duplex permutation input differs from Rust" (event.1.1 == input)
    check "duplex permutation output differs from Rust" (event.1.2 == output)
  return ⟨writer.state.lanes, writer.state.width, writer.state.pending,
    writer.state.pending_le, ()⟩

/-- Smallest nonce and the next challenge agree with Rust at each work level. -/
def grinding (state : Duplex.State rate Unit) (fixtures : Array Json) : IO Unit := do
  for fixture in fixtures do
    let bits ← IO.ofExcept ((← IO.ofExcept (fixture.getObjVal? "bits")).getNat?)
    let expected ← IO.ofExcept ((← IO.ofExcept (fixture.getObjVal? "nonce")).getNat?)
    let challenge ← IO.ofExcept (lanes (← IO.ofExcept (fixture.getObjVal? "challenge")))
    let frame n := #[n.toUInt64, 0, 0, 4]
    let accept (out : Array UInt64) := out[0]! &&& ((1 <<< bits.toUInt64) - 1) == 0
    let some (nonce, next) := Duplex.grind rate (fun _ _ _ ↦ ()) state frame accept (expected + 1)
      | throw (IO.userError "grinding found no nonce")
    check "grinding nonce differs from Rust" (nonce == expected)
    check "grinding next challenge differs from Rust"
      ((Duplex.sample rate (fun _ _ _ ↦ ()) next 3 (by decide)).1 == challenge)
    check "grinding exhausted bound accepted" ((Duplex.grind rate (fun _ _ _ ↦ ())
      state frame accept expected).isNone)

/-- Fixed checked-in vectors are generated by the read-only Rust harness. -/
def run : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "tests/data/keccak_merkle.json"))
  trees (← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "trees")).getArr?))
  let state ← duplex (← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "duplex")).getArr?))

  grinding state (← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "grinding")).getArr?))

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``Merkle.hashRow_eq, ``Merkle.compress_eq,
      ``Merkle.Tree.leaf, ``Merkle.Tree.join, ``Merkle.Tree.nodes_eq, ``Merkle.Tree.root_eq,
      ``Merkle.carry_rows, ``Merkle.Builder.absorb_rows, ``Merkle.commit_rows,
      ``Merkle.Tree.open_eq, ``Merkle.Tree.batch_complete,
      ``Duplex.absorb_eq, ``Duplex.sample_eq, ``Duplex.Writer.write_eq,
      ``Duplex.findNonce_min, ``Duplex.grind_eq] do
    for dependency in (← Lean.collectAxioms declaration) do
      unless allowed.contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"

#print axioms Merkle.Tree.nodes_eq
#print axioms Merkle.Tree.root_eq
#print axioms Merkle.carry_rows
#print axioms Merkle.Builder.absorb_rows
#print axioms Merkle.commit_rows
#print axioms Merkle.Tree.open_eq
#print axioms Merkle.Tree.batch_complete
#print axioms Duplex.absorb_eq
#print axioms Duplex.sample_eq
#print axioms Duplex.Writer.write_eq
#print axioms Duplex.findNonce_min
#print axioms Duplex.grind_eq

end CompStarkTests.KeccakMerkle
