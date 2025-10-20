import Tigris.interpreter.entrypoint
import Tigris.interpreter.leval
import Tigris.core.ftransform

namespace LApp

structure REPLState where
  PE    : PEnv
  E     : Env
  lower : IR.Incremental.LoweringState
  cc    : IR.Incremental.CCState
  funs  : Std.HashMap Name IR.LFun
  gvals : LInterpreter.GlobalEnv

private def asModule (st : REPLState) (mainBody : IR.LExpr) : IR.LModule :=
  let funs := st.funs.valuesArray
  let main : IR.LFun := ⟨"main", "arg", mainBody⟩
  {funs, main}

def initREPL : REPLState where
  PE    := initState
  E     := MLType.defaultE'
  lower := ⟨0, ∅, ∅, ∅⟩
  cc    := ⟨1000, ∅⟩
  funs  := ∅
  gvals := ∅

private def isNonRecFun (fe : FExpr) : Bool :=
  match IRf.HelperF.stripTy fe with
  | .Fun .. => true
  | _       => false

private def pickIdBind (binds : Array BindingF) : Array ((Name × FExpr) ⊕ Name) :=
  let (recs, nonrecs) := IRf.HelperF.splitLetGroup binds
  recs.foldl (fun a s => a.push $ .inr s.1)
  $ nonrecs.foldl (fun a s => a.push $ .inl s) #[]

open IR.Incremental in
def interpretI (st : REPLState) (code : String) : IO (REPLState × LInterpreter.Val) := do
  let (PE', topdecl) <- Parsing.parseREPL code st.PE |>.toIO .userError
  let res@(_, E', _) <- inferToplevelC topdecl st.E |> IO.ofExcept
  let (topdeclF, logger, ctors) <- inferToplevelF res |> IO.ofExcept
  IO.print logger

  let mut lower := IR.Incremental.withTyDecl st.lower ctors
  let mut {cc, funs, gvals,..} := st
  let mut mainBody? : Option IR.LExpr := none
  for d in topdeclF do
    match d with
    | .idBind binds =>
      let (lower', newL) := lowerIdBind lower binds
      let (cc', newCC) := stepFuns cc newL
      lower := lower'
      cc    := cc'
      for f in newCC do
        funs := funs.insert f.fid f
      for b in pickIdBind binds do
        match b with
        | .inl (name, fe) =>
          if isNonRecFun fe then
            mainBody? := some (.seq #[] (.ret name))
          else
            let (lower', le) := IR.Incremental.lower1 lower fe
            lower := lower'
            let (cc', le', lifted) := IR.Incremental.stepExpr cc le
            cc := cc'
            for lf in lifted do funs := funs.insert lf.fid lf
            let m := asModule {st with funs} le'
            println! IR.fmtModule m
            let v <- LInterpreter.evalModule m gvals |>.toIO (.userError ∘ toString)
            gvals := gvals.insert name v
            mainBody? := some le'
        | .inr fid =>
          mainBody? := some (.seq #[] (.ret fid))
    | .patBind (_, fe) =>
      let (lower', le) := IR.Incremental.lower1 lower fe
      let (cc', le, lifted) := IR.Incremental.stepExpr cc le
      lower     := lower'
      cc        := cc'
      mainBody? := some le
      for lf in lifted do funs := funs.insert lf.fid lf
  let mainBody :=
    match mainBody? with
    | some e => e
    | none =>
      -- default to () when nothing to run
      let u := "u"; .letVal u (.cst .unit) (.seq #[] (.ret u))
  let m := asModule {st with funs} mainBody
  let v <- LInterpreter.evalModule m gvals |>.toIO (.userError ∘ toString)
  return ({st with PE := PE', E := E', lower, cc, funs, gvals}, v)

def interpretL (s : String) (PE : PEnv) (E : Env) : IO (PEnv × Env × LInterpreter.Val) := do
  let (PE', topdecl) <- Parsing.parseREPL s PE |>.toIO .userError
  let res@(_, E', _) <- inferToplevelC topdecl E |> IO.ofExcept
  let (topdeclF, logger, ctors) <- inferToplevelF res |> IO.ofExcept
  IO.print logger
  let (_, cc) := IR.toLamModuleF topdeclF ctors
  let val <- LInterpreter.evalModule cc |>.toIO $ .userError ∘ toString
  return (PE', E', val)

