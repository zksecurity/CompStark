/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Lookup.LogUp
public import CompStark.Stark.Quotient

/-! # Quotient values of the LogUp constraints

An AIR's LogUp constraints (`logUpConstraints`) folded by `α` on the quotient domain and divided
by the trace domain's vanishing polynomial, from the main, preprocessed and permutation traces
there, the permutation trace in base coordinates. The batch prover adds them, after the AIR's own
constraints in Horner's order, to the quotient (`lookupQuotientValues`).
-/

@[expose] public section
namespace CompStark.Lookup
open CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- The selectors and `1 / Z_H` on the quotient domain `g · ⟨ω_q⟩` of size
`2 ^ (degreeBits + logChunks)` in natural order: the first-row, last-row and transition
selectors of the trace domain of size `2 ^ degreeBits`, and `1 / Z_H`, which has period
`2 ^ logChunks` there. -/
def quotientSelectors (degreeBits logChunks : Nat) : Array F × Array F × Array F × Array F :=
  let qlog := degreeBits + logChunks
  let n := 2 ^ qlog
  let xs := cosetPoints gen qlog
  let gInv := (twoAdicGen degreeBits)⁻¹
  let period := 2 ^ logChunks
  let zhs := Array.ofFn (n := period) fun k ↦ powF (xs.getD k 0) (2 ^ degreeBits) - 1
  let invFirst := batchInv (xs.map (· - 1))
  let invLast := batchInv (xs.map (· - gInv))
  (Array.ofFn (n := n) fun i ↦ zhs.getD (i.val % period) 0 * invFirst.getD i 0,
    Array.ofFn (n := n) fun i ↦ zhs.getD (i.val % period) 0 * invLast.getD i 0,
    xs.map (· - gInv), batchInv zhs)

/-- The extension constraints `ext`, folded by `α`, on every row of the quotient domain
`g · ⟨ω_q⟩` of size `2 ^ (degreeBits + logChunks)`, divided by the trace domain's vanishing
polynomial. `tq`, `pq` and `rq` are the trace, the preprocessed trace and the permutation trace in
base coordinates on the quotient domain in natural order, `per` the periodic columns there
(`periodicRow`); `chs` are the challenges and `terminal` the terminal. The next row is
`2 ^ logChunks` rows on. -/
def lookupQuotientValues (ext : List (ExtExpr F)) (pis : List F)
    (degreeBits logChunks : Nat) (tq pq rq : Mat F) (per : List (Array F)) (chs : List EF)
    (terminal alpha : EF) : Array EF :=
  let n := 2 ^ (degreeBits + logChunks)
  let period := 2 ^ logChunks
  let (fs, ls, ts, invZh) := quotientSelectors (F := F) degreeBits logChunks
  let d := Challenge.d EF
  let get (m : Mat F) (r c : Nat) : F := m.values.getD (r * m.width + c) 0
  let permAt (r c : Nat) : EF :=
    Challenge.ofCoeffs ((List.range d).map fun e ↦ get rq r (c * d + e))
  Array.ofFn (n := n) fun r ↦
    let r := r.val
    let r' := (r + period) % n
    let env : Expr.Env F EF :=
      { cur := fun c ↦ Ext.ofBase (get tq r c)
        next := fun c ↦ Ext.ofBase (get tq r' c)
        prepCur := fun c ↦ Ext.ofBase (get pq r c)
        prepNext := fun c ↦ Ext.ofBase (get pq r' c)
        periodic := fun j ↦ Ext.ofBase (periodicRow (per.getD j #[]) r)
        pub := fun j ↦ Ext.ofBase (pis.getD j 0)
        const := Ext.ofBase
        isFirstRow := Ext.ofBase (fs.getD r 0)
        isLastRow := Ext.ofBase (ls.getD r 0)
        isTransition := Ext.ofBase (ts.getD r 0) }
    let aux : ExtExpr.Env EF := ⟨permAt r, permAt r', (chs.getD · 0), terminal⟩
    Challenge.smul (invZh.getD (r % period) 0)
      (ext.foldl (fun acc c ↦ acc * alpha + c.eval env aux) 0)

end CompStark.Lookup
