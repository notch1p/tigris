import Tigris.TCNF.interpreter.types
import Tigris.TCNF.entrypoint
namespace TCNF.Interpreter open Std TCNF open MLType (TypingError)

private def checkInterrupt : EIO TypingError Unit :=
  IO.checkCanceled >>= fun
  | true => throw .Interrupted
  | false => return ()

def asConst : TConst -> Value
  | .PUnit   => .unit
  | .PInt i  => .int i
  | .PStr s  => .str s
  | .PBool b => .bool b

def lookup (x : FVarId) : EvaluatorM Value := do
  let {globaldecls, topvals, locals,..} <- read
  match locals[x]? <|> topvals[x]? with
  | some v => return v
  | none   =>
    let some {fvarId,..} := globaldecls[x]? | impossible! "unbound fvar #{x}"
    return .clos fvarId #[]

def evalAtom : Atom -> EvaluatorM Value
  | .lit k  => return asConst k
  | .erased => impossible! "unreachable code is reached"
  | .fvar x => lookup x

def projPair (s : FVarId) : Nat -> Value -> EvaluatorM Value
  | 0, .pair p _ => return p
  | 1, .pair _ q => return q
  | i, v => impossible! "invalid pair projection #{i} for #{s} ==> {v}"

def projConstr (s : FVarId) : Nat -> Value -> EvaluatorM Value
  | i, v@(.constr t as) =>
    if h : i < as.size then return as[i]
    else impossible! "invalid variant projection #{i} for #{s} ==> {v}"
  | i, v => impossible! "invalid variant projection #{i} for #{s} ==> {v}"

def evalPrimBinop (op : PrimOp) (args : Array Value) : EvaluatorM Value :=
  match op, h : args.size with
  | .add   , _ + 2 => applyBinOp! Add.add args expectInt  Value.int
  | .sub   , _ + 2 => applyBinOp! Sub.sub args expectInt  Value.int
  | .mul   , _ + 2 => applyBinOp! Mul.mul args expectInt  Value.int
  | .div   , _ + 2 => applyBinOp! Div.div args expectInt  Value.int
  | .eqInt , _ + 2 => applyBinOp! BEq.beq args expectInt  Value.bool
  | .eqBool, _ + 2 => applyBinOp! BEq.beq args expectBool Value.bool
  | .eqStr , _ + 2 => applyBinOp! BEq.beq args expectStr  Value.bool
  | op, _          => impossible! "cannot apply {repr op} to {args}"

mutual
partial def evalLetValue : LetValue .postCC -> EvaluatorM Value
  | .lit k    => return asConst k
  | .pair p q => .pair <$> evalAtom p <*> evalAtom q
  | .proj i s => projPair s i =<< lookup s
  | .field _ i s => projConstr s i =<< lookup s
  | .ctor t as => .constr t <$> as.mapM evalAtom
  | .prim op args => evalPrimBinop op =<< args.mapM evalAtom
  | .isCtor s t a =>
    lookup s <&> fun
                 | .constr t' as => .bool $ t' == t && as.size == a
                 | _ => .bool $ false
  | .mkClos c env => .clos c <$> env.mapM evalAtom
  | .extern .. => return .unit
  | .app 0 as | .pap 0 as => impossible! "All branches failed to match against {format as}"
  | .app f as | .pap f as => do
    let as <- as.mapM evalAtom
    let f <- lookup f
    applyN f as.toSubarray

partial def applyN (f : Value) (as : Subarray Value) : EvaluatorM Value := do
  let s@{globaldecls,locals,..} <- read
  let (.clos f env) := f | impossible! "callee #{f} is not a code pointer"
  let some {params, body,..} := globaldecls[f]? | impossible! "undefined function #{f}"
  let arity := params.size - env.size
  let ass := as.size
  if arity == ass then
    let locals := Array.seq2fold2 (init := locals) (xs := env) (ys := as) (zs := params)
      fun acc a b => acc.insert b.fvarId a
    evalCode body {s with locals}
  else if arity > ass then return .clos f (env ++ as)
  else
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
  | .let {fvarId, value,..} b => do
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
  | .unreach _ => impossible! "unreachable code has been reached"

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
    | _ => impossible! "Can't match against {d} ==> {t}"
  | v => impossible! "Discriminant {v} is neither variant nor constant"
where
  goConst : Option (Alt .postCC) -> EvaluatorM Value
  | some $ .default k
  | some $ .const _ k => evalCode k
  | _ => impossible! "Can't match against {d}"
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
  for d@{fvarId, arity, body, name, ty,..} in decls.push main do
    if arity > 0 then
      liftEIO (println! template name "<fun>" $ E.E[name]?.getD $ .Forall [] [] ty)
      globaldecls := globaldecls.insert fvarId d
    else
      let v <- evalCode body {globaldecls, topvals} |>.adapt toString
      liftEIO (println! template name v $ E.E[name]?.getD $ .Forall [] [] ty)
      topvals := topvals.insert fvarId v

def checkFile (s : System.FilePath) : IO Unit := do
  let s <- IO.FS.readFile s
  EIO.toIO .userError $ check s

def main (args : List String) :=
  args.forA fun p => checkFile p
