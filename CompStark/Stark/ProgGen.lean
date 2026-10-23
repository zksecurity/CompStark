/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.ProgGroup
public meta import Lean.Elab.Command

/-! # Straight-line code for a program

`group_kernels p` defines, in the current namespace, the group kernels (`CompStark/Stark/ProgGroup`)
over the field `FastField p` as compiled functions, the field's constants immediate.

`#gen_group_chunks K ns prog size i n` cuts the code of the program `prog`, evaluated during
elaboration, into chunks of `size` instructions and, for the `i`-th of `n` equal parts of them
(chunks `i c / n` to `(i + 1) c / n - 1` of `c`), defines their code `K.code_k` and their
straight-line code `K.chunk_k`, a call of the kernel of `ns` per instruction, with `K.chunk_k_eq : K.chunk_k env s = K.code_k.foldl (fun s i ↦ i.exec M s) s` for
the group machine `M` checked by the kernel's `rfl`, without unfolding field arithmetic: both sides
reduce to the same calls. `#gen_group_kernel K p` assembles the chunks into
`K.kernel : GroupKernel p` (`runChunks_eq`). Chunks of a program can be generated in separate
modules, built in parallel.
-/

open Lean Elab Command Meta

namespace CompStark.Stark.Prog

set_option hygiene false in
/-- The group kernels over `FastField p` in the current namespace. -/
macro "group_kernels " p:term : command => `(
    @[noinline] def addSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.addSS $p nm s d a b
    @[noinline] def addSE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.addSE $p nm s e d a b
    @[noinline] def addES (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.addES $p nm s e d a b
    @[noinline] def addEE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.addEE $p nm s e d a b
    @[noinline] def addSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.addSW $p nm s d a c
    @[noinline] def addEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.addEW $p nm s e d a c
    @[noinline] def addWS (nm : Nat) (s : ByteArray) (d b : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.addWS $p nm s d b c
    @[noinline] def addWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d b : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.addWE $p nm s e d b c
    @[noinline] def subSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.subSS $p nm s d a b
    @[noinline] def subSE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.subSE $p nm s e d a b
    @[noinline] def subES (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.subES $p nm s e d a b
    @[noinline] def subEE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.subEE $p nm s e d a b
    @[noinline] def subSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.subSW $p nm s d a c
    @[noinline] def subEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.subEW $p nm s e d a c
    @[noinline] def subWS (nm : Nat) (s : ByteArray) (d b : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.subWS $p nm s d b c
    @[noinline] def subWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d b : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.subWE $p nm s e d b c
    @[noinline] def mulSS (nm : Nat) (s : ByteArray) (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.mulSS $p nm s d a b
    @[noinline] def mulSE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.mulSE $p nm s e d a b
    @[noinline] def mulES (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.mulES $p nm s e d a b
    @[noinline] def mulEE (nm : Nat) (s : ByteArray) (e : @& ByteArray)
        (d a b : USize) : ByteArray :=
      CompStark.Stark.Prog.mulEE $p nm s e d a b
    @[noinline] def mulSW (nm : Nat) (s : ByteArray) (d a : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.mulSW $p nm s d a c
    @[noinline] def mulEW (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.mulEW $p nm s e d a c
    @[noinline] def mulWS (nm : Nat) (s : ByteArray) (d b : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.mulWS $p nm s d b c
    @[noinline] def mulWE (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d b : USize)
        (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.mulWE $p nm s e d b c
    @[noinline] def fill (nm : Nat) (s : ByteArray) (d : USize) (c : UInt32) : ByteArray :=
      CompStark.Stark.Prog.fill nm s d c
    @[noinline] def copy (nm : Nat) (s : ByteArray) (e : @& ByteArray) (d a : USize) : ByteArray :=
      CompStark.Stark.Prog.copy nm s e d a
    @[noinline] def gather (nm : Nat) (s : ByteArray) (d : USize) (m : @& ByteArray) (w c : Nat)
        (next : @& Array Nat) (r0 : Nat) : ByteArray :=
      CompStark.Stark.Prog.gather nm s d m w c next r0
    @[noinline] def accS (nm : Nat) (rb : USize) (s : ByteArray) (a : USize)
        (wts : @& Array UInt32) (w : Nat) :
        ByteArray :=
      CompStark.Stark.Prog.accS $p nm rb s a wts w
    @[noinline] def accE (nm : Nat) (rb : USize) (s : ByteArray) (e : @& ByteArray) (a : USize)
        (wts : @& Array UInt32)
        (w : Nat) : ByteArray :=
      CompStark.Stark.Prog.accE $p nm rb s e a wts w
    @[noinline] def accW (nm : Nat) (rb : USize) (s : ByteArray) (c : UInt32)
        (wts : @& Array UInt32) (w : Nat) :
        ByteArray :=
      CompStark.Stark.Prog.accW $p nm rb s c wts w
  )

/-! ### The generator -/

/-- A literal. -/
meta def natE (n : Nat) : Lean.Expr := mkRawNatLit n

/-- The generator's view of a program: its field `F` (`FastField P` with instance `inst`) and the
code, the field's elements as their words. -/
structure GenProg where
  F : Lean.Expr
  P : Lean.Expr
  inst : Lean.Expr
  code : Array (Instr UInt32)

/-- Evaluate a program term. Elements of `FastField P` are represented as their words. -/
meta def evalProg (stx : Syntax) : TermElabM GenProg := do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← whnfR (← inferType e)
  let F := ty.appArg!
  let F' ← whnfR F
  unless F'.isAppOfArity ``Montgomery.Native32.FastField 2 do
    throwError "expected a program over `FastField p`, got {F}"
  let prog ← unsafe evalExpr (Prog UInt32) ty e
  return ⟨F, F'.appFn!.appArg!, F'.appArg!, prog.code⟩

/-- A field element `w` as a term of `FastField P`. -/
meta def fieldE (g : GenProg) (w : UInt32) : MetaM Lean.Expr := do
  let wE := toExpr w
  let pred ← withLocalDeclD `x (mkConst ``UInt32) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``LT.lt #[← mkAppM ``UInt32.toNat #[x], g.P])
  let pf ← mkDecideProof (← mkAppM ``LT.lt #[← mkAppM ``UInt32.toNat #[wE], g.P])
  return mkAppN (mkConst ``Subtype.mk [1]) #[mkConst ``UInt32, pred, wE, pf]

meta def opE : Op → Lean.Expr
  | .add => mkConst ``Op.add
  | .sub => mkConst ``Op.sub
  | .mul => mkConst ``Op.mul

meta def srcE : Src → Lean.Expr
  | .next c => mkApp (mkConst ``Src.next) (natE c)
  | .prepCur c => mkApp (mkConst ``Src.prepCur) (natE c)
  | .prepNext c => mkApp (mkConst ``Src.prepNext) (natE c)
  | .permCur c => mkApp (mkConst ``Src.permCur) (natE c)
  | .permNext c => mkApp (mkConst ``Src.permNext) (natE c)
  | .periodic i => mkApp (mkConst ``Src.periodic) (natE i)
  | .isFirstRow => mkConst ``Src.isFirstRow
  | .isLastRow => mkConst ``Src.isLastRow
  | .isTransition => mkConst ``Src.isTransition

meta def opdE (g : GenProg) : Opd UInt32 → MetaM Lean.Expr
  | .reg r => pure <| mkApp2 (mkConst ``Opd.reg) g.F (natE r)
  | .cur c => pure <| mkApp2 (mkConst ``Opd.cur) g.F (natE c)
  | .const x => return mkApp2 (mkConst ``Opd.const) g.F (← fieldE g x)

/-- An instruction as a term. -/
meta def instrE (g : GenProg) : Instr UInt32 → MetaM Lean.Expr
  | .load d s => pure <| mkApp3 (mkConst ``Instr.load) g.F (natE d) (srcE s)
  | .scalar d i => pure <| mkApp3 (mkConst ``Instr.scalar) g.F (natE d) (natE i)
  | .bin o d a b => return mkAppN (mkConst ``Instr.bin) #[g.F, opE o, natE d, ← opdE g a,
      ← opdE g b]
  | .acc a w => return mkApp3 (mkConst ``Instr.acc) g.F (← opdE g a) (natE w)

/-- The kernel call of an instruction on the state `s`, as the group machine reduces it. -/
meta def callE (ns : Name) (env s : Lean.Expr) (i : Instr UInt32) : MetaM Lean.Expr := do
  let nm ← mkAppM ``GroupEnv.nm #[env]
  let rb ← mkAppM ``GroupEnv.rb #[env]
  match i with
  | .load d src => do
    let L ← mkAppM ``GroupEnv.L #[env]
    let fld (n : Name) : MetaM Lean.Expr := mkAppM n #[L]
    let d := mkApp2 (mkConst ``regOff) env (natE d)
    let tcol (c : Nat) : MetaM Lean.Expr := pure (mkApp2 (mkConst ``tcolOff) env (natE c))
    let gather (m w : Name) (c : Nat) : MetaM Lean.Expr := do
      return mkAppN (mkConst (ns ++ `gather)) #[nm, s, d, ← fld m, ← fld w, natE c,
        ← fld ``Loads.next, ← fld ``Loads.r0]
    let sb ← mkAppM ``GroupEnv.sb #[env]
    match src with
    | .next c => gather ``Loads.main ``Loads.w c
    | .prepCur c => return mkAppN (mkConst (ns ++ `copy)) #[nm, s, ← fld ``Loads.prepT, d, ← tcol c]
    | .prepNext c => gather ``Loads.prep ``Loads.pw c
    | .permCur c => return mkAppN (mkConst (ns ++ `copy)) #[nm, s, ← fld ``Loads.permT, d, ← tcol c]
    | .permNext c => gather ``Loads.perm ``Loads.rw c
    | .periodic j =>
      return mkAppN (mkConst ``copyPer) #[nm, s, ← fld ``Loads.per, natE j, d, sb]
    | .isFirstRow => return mkAppN (mkConst (ns ++ `copy)) #[nm, s, ← fld ``Loads.first, d, sb]
    | .isLastRow => return mkAppN (mkConst (ns ++ `copy)) #[nm, s, ← fld ``Loads.last, d, sb]
    | .isTransition => return mkAppN (mkConst (ns ++ `copy)) #[nm, s, ← fld ``Loads.trans, d, sb]
  | .scalar d i =>
    return mkAppN (mkConst (ns ++ `fill))
      #[nm, s, mkApp2 (mkConst ``regOff) env (natE d), mkApp2 (mkConst ``scalAt) env (natE i)]
  | .bin o d a b => do
    let view ← mkAppM ``GroupEnv.view #[env]
    let col (c : Nat) : MetaM Lean.Expr := pure (mkApp2 (mkConst ``colOff) env (natE c))
    let reg (r : Nat) : Lean.Expr := mkApp2 (mkConst ``regOff) env (natE r)
    let d := reg d
    let k (kind : String) : Name := ns ++ Name.mkSimple ((match o with
      | .add => "add" | .sub => "sub" | .mul => "mul") ++ kind)
    match a, b with
    | .reg ra, .reg rb => return mkAppN (mkConst (k "SS")) #[nm, s, d, reg ra, reg rb]
    | .reg ra, .cur cb => return mkAppN (mkConst (k "SE")) #[nm, s, view, d, reg ra, ← col cb]
    | .cur ca, .reg rb => return mkAppN (mkConst (k "ES")) #[nm, s, view, d, ← col ca, reg rb]
    | .cur ca, .cur cb => return mkAppN (mkConst (k "EE")) #[nm, s, view, d, ← col ca, ← col cb]
    | .reg ra, .const y => return mkAppN (mkConst (k "SW")) #[nm, s, d, reg ra, toExpr y]
    | .cur ca, .const y => return mkAppN (mkConst (k "EW")) #[nm, s, view, d, ← col ca, toExpr y]
    | .const x, .reg rb => return mkAppN (mkConst (k "WS")) #[nm, s, d, reg rb, toExpr x]
    | .const x, .cur cb => return mkAppN (mkConst (k "WE")) #[nm, s, view, d, ← col cb, toExpr x]
    | .const _, .const _ => throwError "an operation on two constants"
  | .acc a w => do
    let wts ← mkAppM ``GroupEnv.wts #[env]
    match a with
    | .reg r =>
      return mkAppN (mkConst (ns ++ `accS)) #[nm, rb, s, mkApp2 (mkConst ``regOff) env
          (natE r), wts, natE w]
    | .cur c => do
      let off := mkApp2 (mkConst ``colOff) env (natE c)
      let view ← mkAppM ``GroupEnv.view #[env]
      return mkAppN (mkConst (ns ++ `accE)) #[nm, rb, s, view, off, wts, natE w]
    | .const c => return mkAppN (mkConst (ns ++ `accW)) #[nm, rb, s, toExpr c, wts, natE w]

/-- `#gen_group_chunks K ns prog size i n`: the `i`-th of `n` parts of the chunks of `size`
instructions of the program `prog`, as `K.code_k`, `K.chunk_k` (calls of the kernels of `ns`) and
`K.chunk_k_eq`. -/
elab "#gen_group_chunks " K:ident ns:ident prog:term:max size:num part:num parts:num : command =>
  withScope (fun sc ↦ { sc with opts := maxRecDepth.set sc.opts 100000 }) do
    let g ← liftTermElabM (evalProg prog)
    let N := size.getNat
    let K := K.getId
    let ns := ns.getId
    let instrT := mkApp (mkConst ``Instr) g.F
    let envT := mkConst ``GroupEnv
    let baT := mkConst ``ByteArray
    let chunks := (g.code.size + N - 1) / N
    let lo := part.getNat * chunks / parts.getNat
    let hi := (part.getNat + 1) * chunks / parts.getNat
    for k in [lo:hi] do
      let instrs := (g.code.extract (k * N) ((k + 1) * N)).toList
      let codeName := K ++ Name.mkSimple s!"code_{k}"
      let chunkName := K ++ Name.mkSimple s!"chunk_{k}"
      let codeE ← liftTermElabM do mkListLit instrT (← instrs.mapM fun i =>
          (instrE g i : MetaM Lean.Expr))
      let listT := mkApp (mkConst ``List [0]) instrT
      liftCoreM <| addAndCompile (.defnDecl (mkDefinitionValEx codeName [] listT codeE
          (.regular 0) .safe []))
      let (ty, val) ← liftTermElabM do
        withLocalDeclD `env envT fun env => withLocalDeclD `s baT fun s0 => do
          let mut body := s0
          for i in instrs do
            body ← callE ns env body i
          return (← mkForallFVars #[env, s0] baT, ← mkLambdaFVars #[env, s0] body)
      liftCoreM <| addAndCompile (.defnDecl
          (mkDefinitionValEx chunkName [] ty val .opaque .safe []))
      let thm ← liftTermElabM do
        withLocalDeclD `env envT fun env => withLocalDeclD `s baT fun s0 => do
          let M := mkApp3 (mkConst ``groupMachine) g.P g.inst env
          let step ← withLocalDeclD `s baT fun s => withLocalDeclD `i instrT fun i => do
            mkLambdaFVars #[s, i] (mkApp4 (mkConst ``Instr.exec) g.F baT M i |>.app s)
          let rhs ← mkAppM ``List.foldl #[step, s0, mkConst codeName]
          let lhs := mkApp2 (mkConst chunkName) env s0
          return (← mkForallFVars #[env, s0] (← mkEq lhs rhs),
            ← mkLambdaFVars #[env, s0] (← mkEqRefl lhs))
      let thmName := K ++ Name.mkSimple s!"chunk_{k}_eq"
      let tv : TheoremVal := { name := thmName, levelParams := [], type := thm.1, value := thm.2 }
      liftCoreM <| addDecl (.thmDecl tv)

/-- `#gen_group_kernel K p`: the chunks `K.chunk_0, K.chunk_1, …` as `K.kernel : GroupKernel p`. -/
elab "#gen_group_kernel " K:ident p:term:max : command => do
  let K := K.getId
  let env ← getEnv
  let n := (List.range 100000).find? (fun k ↦ !env.contains (K ++ Name.mkSimple s!"chunk_{k}"))
    |>.getD 0
  let ks := List.range n
  liftTermElabM do
    let pE ← Term.elabTerm p (some (mkConst ``Nat))
    let inst ← synthInstance (mkApp (mkConst ``Montgomery.Native32.Mont32Field) pE)
    let F := mkApp2 (mkConst ``Montgomery.Native32.FastField) pE inst
    let instrT := mkApp (mkConst ``Instr) F
    let codes ← mkListLit (mkApp (mkConst ``List [0]) instrT)
      (ks.map fun k => mkConst (K ++ Name.mkSimple s!"code_{k}"))
    let code ← mkAppM ``List.toArray #[← mkAppM ``List.flatten #[codes]]
    let bb ← mkArrow (mkConst ``ByteArray) (mkConst ``ByteArray)
    let run ← withLocalDeclD `env (mkConst ``GroupEnv) fun env => do
      let fs ← mkListLit bb
        (ks.map fun k => mkApp (mkConst (K ++ Name.mkSimple s!"chunk_{k}")) env)
      mkLambdaFVars #[env] (← mkAppM ``runChunks #[fs])
    let pf ← withLocalDeclD `env (mkConst ``GroupEnv) fun env => do
      let M := mkApp3 (mkConst ``groupMachine) pE inst env
      -- Forall₂ (chunk equations) codes fs, built from the last chunk
      let rel ← withLocalDeclD `c (mkApp (mkConst ``List [0]) instrT) fun c =>
        withLocalDeclD `f bb fun f => do
          let body ← withLocalDeclD `s (mkConst ``ByteArray) fun s => do
            let step ← withLocalDeclD `s' (mkConst ``ByteArray) fun s' =>
              withLocalDeclD `i instrT fun i => do
                mkLambdaFVars #[s', i] (mkApp (mkApp4 (mkConst ``Instr.exec) F
                    (mkConst ``ByteArray) M i) s')
            mkForallFVars #[s] (← mkEq (mkApp f s) (← mkAppM ``List.foldl #[step, s, c]))
          mkLambdaFVars #[c, f] body
      let mut acc := mkApp3 (mkConst ``List.Forall₂.nil [0, 0]) (mkApp (mkConst ``List [0]) instrT)
        bb rel
      let mut csE := mkApp (mkConst ``List.nil [0]) (mkApp (mkConst ``List [0]) instrT)
      let mut fsE := mkApp (mkConst ``List.nil [0]) bb
      for k in ks.reverse do
        let c := mkConst (K ++ Name.mkSimple s!"code_{k}")
        let f := mkApp (mkConst (K ++ Name.mkSimple s!"chunk_{k}")) env
        let h := mkApp (mkConst (K ++ Name.mkSimple s!"chunk_{k}_eq")) env
        acc := mkAppN (mkConst ``List.Forall₂.cons [0, 0])
          #[mkApp (mkConst ``List [0]) instrT, bb,
            rel, c, f, csE, fsE, h, acc]
        csE := mkApp3 (mkConst ``List.cons [0]) (mkApp (mkConst ``List [0]) instrT) c csE
        fsE := mkApp3 (mkConst ``List.cons [0]) bb f fsE
      mkLambdaFVars #[env] (mkApp5 (mkConst ``runChunks_eq) F
          (mkConst ``ByteArray) M csE fsE |>.app acc)
    let kernel ← mkAppM ``GroupKernel.mk #[code, run, pf]
    let ty ← inferType kernel
    let decl := Declaration.defnDecl (mkDefinitionValEx (K ++ `kernel) [] ty kernel
      ReducibilityHints.abbrev DefinitionSafety.safe [])
    addAndCompile decl

end CompStark.Stark.Prog
