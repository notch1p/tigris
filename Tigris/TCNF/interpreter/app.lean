import Tigris.TCNF.interpreter.eval
import Tigris.TCNF.«entrypoint-incr»

namespace TCNF.Interpreter.App open Incremental Std
structure EvalState where
  PE       : PEnv      := initState
  E        : Env       := MLType.defaultE'
  is       : IState    := {}
  nfs      : NFState   := {}
  ins      : IncrState := {}
  optDecls : Lean.Data.Trie (Decl .postCC) := ∅
  ctors    : HashMap String Nat := ∅

abbrev EvalM := StateRefT EvalState LowerM
instance : MonadLift IO EvalM := ⟨liftM ∘ liftEIO⟩

def evaluate1 (s : String.Slice) : EvalM Unit := do
  let {PE, E, is, nfs, ins, ctors, optDecls} <- get
  let (PE, decls) <- Parsing.parseREPL s PE
  let te@(_, E@{tyDecl,..}, _) <- inferToplevelC decls E
                      |>.mapError toString |> EIO.ofExcept
  let (decls, L, ctors) <- inferToplevelF te ctors |>.mapError toString |> EIO.ofExcept
  modify fun s => {s with E, PE, ctors}
  IO.print L
  let ds := decls.size

  -- not very effcient since we can derive it when typechecking too lazy to refactor
  let newtypes := newtypeCtors tyDecl

  let rec lower i lifted is nfs (h : i <= ds) :=
    match h' : i with
    | 0 => return (lifted, is, nfs)
    | n + 1 => do
      let ((decls, is), nfs) <- lowerTop1 decls[ds - i] ctors tyDecl |>.run is |>.run nfs
      let ((_, is@{lifted := lifted',..}), nfs) <- ccDecls decls |>.run is |>.run nfs
      let ((lifted', is), nfs) <- optimize1 newtypes lifted' |>.run is |>.run nfs
      lower n (lifted ++ lifted') is nfs $ Nat.le_of_succ_le h

  let (lifted, ins, nfs) <- lower ds #[] ins nfs Nat.le.refl
  modify (fun s@{optDecls,..} =>
    {s with ins
            nfs
            optDecls := lifted.foldl (fun acc d => acc.insert d.name d) optDecls})

  let is <- lifted.foldlM (init := is)
    fun is@{globaldecls,topvals,..} d@{fvarId, arity, body, name,..} => do
      if arity > 0 then
        if let some ty := E.E[name]? then
          println! template name "<fun>" ty
        return {is with globaldecls := globaldecls.insert fvarId d}
      else
        let v <- evalCode body {is with globaldecls, topvals} |>.adapt toString
        if let some ty := E.E[name]? then
          println! template name v ty
        return {is with topvals := topvals.insert fvarId v}

  modify (fun s => {s with is})
