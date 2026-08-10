import Tigris.TCNF.interpreter.types
import Tigris.TCNF.entrypoint
namespace TCNF.Interpreter.old open Std TCNF open MLType (TypingError)

private def checkInterrupt : EIO TypingError Unit :=
  IO.checkCanceled >>= fun
  | true => throw .Interrupted
  | false => return ()
local macro "withInterrupt!" x:doSeq : term => ``(checkInterrupt *> do $x)

mutual
partial def evalLetValue : LetValue .postCC -> EvaluatorM Value
  | .lit k    => return asConst k
  | .pair p q => .pair <$> evalAtom p <*> evalAtom q
  | .proj i s => projPair s i =<< lookup s
  | .field _ i s => projConstr s i =<< lookup s
  | .ctor t as => .constr t <$> as.mapM evalAtom
  | .prim op args  => evalPrimBinop op =<< args.mapM evalAtom
  | .extern f args => evalExtern f =<< args.mapM evalAtom
  | .isCtor s t a =>
    lookup s <&> fun
                 | .constr t' as => .bool $ t' == t && as.size == a
                 | _ => .bool $ false
  | .mkClos c env => .clos c <$> env.mapM evalAtom
  | .app 0 as | .pap 0 as => impossibleF! "All branches failed to match against {format as}"
  | .app f as | .pap f as => do
    let as <- as.mapM evalAtom
    let f <- lookup f
    applyN f as.toSubarray

partial def applyN (f : Value) (as : Subarray Value) : EvaluatorM Value := withInterrupt!
  let s@{globaldecls,locals,..} <- read
  let (.clos f env) := f | impossibleF! "callee #{f} is not a code pointer"
  let some {params, body,..} := globaldecls[f]? | impossibleF! "undefined function #{f}"
  let arity := params.size - env.size
  let ass := as.size
  if arity == ass then
    let locals := Array.seq2fold2 (init := locals) (xs := env) (ys := as) (zs := params)
      fun acc a b => acc.insert b.fvarId a
    evalCode body {s with locals}
  else if arity > ass then return .clos f (env ++ as)
  else -- seq2fold2 f xs ys zs = foldl2 f (xs ++ ys) zs = foldl .. (xs ++ ys `zip` zs)
    let locals := Array.seq2fold2 (init := locals) (xs := env) (ys := as) (zs := params)
      fun acc a b => acc.insert b.fvarId a
    let f' <- evalCode body {s with locals}
    applyN f' as[arity:]
partial def jump (f : FVarId) (as : Array Value) : EvaluatorM Value := fun s => do
  let some (params, body, locals) := s.joins[f]? | impossible! "undefined join point #{f}"
  let mut locals := locals
  for a in as, fvarId in params do locals := locals.insert fvarId a
  evalCode body {s with locals}

partial def evalCode (c : Code .postCC) : EvaluatorM Value :=
  match c with
  | .let {fvarId, value,..} b => withInterrupt!
    let v <- evalLetValue value
    withReader
      (fun s@{locals,..} => {s with locals := locals.insert fvarId v})
      (evalCode b)
  | .cases d _ alts  => evalCases d alts
  | .jp {fvarId, params, body,..} k =>
    let ps := params.map Param.fvarId
    withReader
      (fun s@{joins, locals,..} => {s with joins := joins.insert fvarId (ps, body, locals)})
      (evalCode k)
  | .jmp jp args => jump jp =<< args.mapM evalAtom
  | .ret a => evalAtom a
  | .unreach _ => impossibleF! "unreachable code has been reached"

partial def evalCases (d : FVarId) (alts : Array $ Alt .postCC) : EvaluatorM Value := do
  match <- lookup d with
  | .unit =>
    goConst $ alts.find? fun | .default _         | .const .PUnit _ => true         | _ => false
  | .int i =>
    goConst $ alts.find? fun | .default _ => true | .const (.PInt i') _ => i == i'  | _ => false
  | .bool b =>
    goConst $ alts.find? fun | .default _ => true | .const (.PBool b') _ => b == b' | _ => false
  | .str s =>
    goConst $ alts.find? fun | .default _ => true | .const (.PStr s') _ => s == s'  | _ => false
  | .constr t as =>
    match alts.find? fun | .default _ => true | .ctor t' .. => t' == t | _ => false
    with
    | some (.default k) => evalCode k
    | some (.ctor _ ps k) =>
      let s@{locals,..} <- read
      let locals := Array.foldl2 (fun acc a {fvarId,..} => acc.insert fvarId a) locals as ps
      evalCode k {s with locals}
    | _ => impossibleF! "Can't match against {d} ==> {t}"
  | v => impossibleF! "Discriminant {v} is neither variant nor constant"
where
  goConst : Option (Alt .postCC) -> EvaluatorM Value
  | some $ .default k
  | some $ .const _ k => evalCode k
  | _ => impossibleF! "Can't match against {d}"
end

open Format (fill group pretty nestD)
def template {α} [ToFormat α] (name : String) (v : α) (ty : Scheme) : String :=
  let s := s!"{name} ="
  let ss := s.length
  if ss <= 20
  then pretty (fill $ (group $ s <> nestD (format v)) <+> "⊢" <> format ty)
              (width := 70) (indent := ss - 1) (column := ss - 1)
  else pretty (fill $ (group $ s ++ "\n" ++ format v) <+> "⊢" <> format ty)
              (width := 70) (indent := 2) (column := 2)
def check (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let {decls, main} <- lowerModuleCCOpt fdecls ctors E.tyDecl
  let mut globaldecls := ∅
  let mut topvals := ∅
  for d@{fvarId, arity, body, name,..} in decls.push main do
    if arity > 0 then
      if let some ty := E.E[name]? then
        liftEIO (println! template name "<fun>" ty)
      globaldecls := globaldecls.insert fvarId d
      topvals := topvals.insert fvarId (.clos fvarId #[])
    else
      let v <- evalCode body {globaldecls, topvals} |>.adapt toString
      if let some ty := E.E[name]? then
        liftEIO (println! template name v ty)
      topvals := topvals.insert fvarId v

def checkFile (s : System.FilePath) : IO Unit := do
  let s <- IO.FS.readFile s
  EIO.toIO .userError $ check s

def main (args : List String) := args.forA fun p => checkFile p
