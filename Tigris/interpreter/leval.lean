import Tigris.core.lam
import Tigris.parsing.types
import Tigris.typing.ttypes

namespace LInterpreter open IR open MLType (TypingError)

private def checkInterrupt : EIO TypingError Unit :=
  IO.checkCanceled >>= fun
  | true => throw .Interrupted
  | false => return ()

inductive Val where
  | unit
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
  | pair (p q : Val)
  | ctor (tag : Name) (fields : Array Val)
  | code (pointer : Name)
deriving Repr, BEq, Inhabited

abbrev Env    := Std.HashMap Name Val
abbrev FunTab := Std.HashMap Name LFun

/-- any error tagged impossbible should be (but isn't) caught by a previous pass
   e.g. typechecker
-/
macro "impossible!" v:interpolatedStr(term) : term =>
  ``(throw $ TypingError.Impossible (s! $v))
open Std Format in
def Val.toFormat : Val -> Std.Format
  | .unit => "()" | .int i => format i
  | .bool b => format b | .str s => repr s
  | .pair a b => toFormat a ++ "," <> toFormat b
  | .ctor t fs => t ++ sbracket (joinSep' (fs.map toFormat) ",")
  | .code fid => s!"#<{fid}>"

instance : ToString Val := ⟨Std.Format.pretty ∘ Val.toFormat⟩
instance : Std.ToFormat Val := ⟨Val.toFormat⟩

def expectInt : Val -> Except TypingError Int
  | .int i => return i
  | v => impossible! "expected Int, found {v}"
def expectBool : Val -> Except TypingError Bool
  | .bool b => return b
  | v => impossible! "expected Bool, found {v}"
def asConst? : Val -> Option Const
  | .unit => some .unit
  | .int i => some (.int i)
  | .bool b => some (.bool b)
  | .str s => some (.str s)
  | _ => none

def getVar (ρ : Env) (ft : FunTab) (x : Name) : Except TypingError Val :=
  match ρ[x]? with
   | some v => .ok v
   | none => if x ∈ ft then .ok (.code x) else impossible! "unbound variable {x}"

def evalPrim (op : PrimOp) (args : Array Val) : Except TypingError Val :=
  match op, args.toList with
  | .add, [.int a, .int b] => return .int $ a + b
  | .sub, [.int a, .int b] => return .int $ a - b
  | .mul, [.int a, .int b] => return .int $ a * b
  | .div, [.int a, .int b] => return .int $ a / b
  | .eqInt , [.int a, .int b]
  | .eqBool, [.bool a, .bool b]
  | .eqStr , [.str a, .str b]
    => return (.bool (a == b))
  | _, _ => impossible! "invalid primitive application {repr op} on {args}"

def proj (idx : Nat) (s : Name) (v : Val)  : Except TypingError Val :=
  match v with
  | .pair a b =>
    match idx with
    | 0 => return a
    | 1 => return b
    | _ => impossible! "pair projection {idx} out of bounds on {s} = {v}"
  | .ctor _ fs =>
    if h : idx < fs.size then return fs[idx]
    else impossible! "ctor projection {idx} out of bounds on {s} = {v}"
  | _ => impossible! "projection on non-aggregate {s} = {v}"

instance : MonadLift (Except ε) (EIO ε) where
  monadLift
  | .ok res => return res
  | .error e => throw e

mutual
partial def evalRhs (ft : FunTab) (ρ : Env)
  : Rhs -> EIO TypingError Val := fun rhs => checkInterrupt *>
  match rhs with
  | .prim op xs => xs.mapM (liftM ∘ getVar ρ ft) >>= liftM ∘ evalPrim op
  | .proj s i => liftM ∘ proj i s =<< getVar ρ ft s
  | .mkPair a b => pure .pair <*> getVar ρ ft a <*> getVar ρ ft b
  | .mkConstr t fs => .ctor t <$> fs.mapM (liftM ∘ getVar ρ ft)
  | .isConstr s t ar =>
    getVar ρ ft s <&> fun
    | .ctor t' fs => .bool (t' == t && fs.size == ar)
    | _ => .bool false
  | .call f a =>
    getVar ρ ft f >>= fun
    | .code fid => evalFun ft fid =<< getVar ρ ft a
    | f' => impossible! "callee {f} = {f'} is not a code pointer"

partial def evalStmt (ft : FunTab) (ρ : Env) 
  : Stmt -> EIO TypingError Env := fun (.let1 x rhs) =>
  checkInterrupt *> ρ.insert x <$> evalRhs ft ρ rhs

partial def evalTail (ft : FunTab) (ρ : Env) 
  : Tail -> EIO TypingError Val := fun t => checkInterrupt *>
  match t with
  | .ret x => getVar ρ ft x
  | .app f a =>
    getVar ρ ft f >>= fun
    | .code fid => evalFun ft fid =<< getVar ρ ft a
    | f' => impossible! "callee {f} = {f'} is not a code pointer"
  | .cond c t e =>
    getVar ρ ft c >>= liftM ∘ expectBool >>= fun
    | true => evalExpr ft ρ t
    | false => evalExpr ft ρ e
  | .switchConst s cases d? => do
    match asConst? (<- getVar ρ ft s) with
    | none => impossible! "discrminant is not a constant"
    | some k =>
      match cases.findSome? fun (kc, b) => if kc == k then some b else none
      with
      | some branch => evalExpr ft ρ branch
      | none =>
        match d? with
        | some b => evalExpr ft ρ b
        | none => throw
                $ .NoMatchL (toString k)
                $ cases.map
                $ toString ∘ Prod.fst
  | .switchCtor s cases d? => do
    match <- getVar ρ ft s with
    | .ctor tag fs =>
      let ar := fs.size
      match cases.findSome? fun (t, arity, b) => 
        if t == tag && arity == ar then some b else none
      with
      | some b => evalExpr ft ρ b
      | none =>
        match d? with
        | some b => evalExpr ft ρ b
        | none => throw
                $ .NoMatchL s!"{tag}/{ar}"
                $ cases.map fun (n, ar, _) => s!"{n}/{ar}"
    | _ => impossible! "discriminant is not a constructor"

partial def evalExpr (ft : FunTab) (ρ : Env) 
  : LExpr -> EIO TypingError Val := fun e => checkInterrupt *>
  match e with
  | .seq binds t => binds.foldlM (evalStmt ft) ρ >>= fun ρ => evalTail ft ρ t
  | .letVal x v b =>
    let vx :=
      match v with
      | .var y => ρ.getD y (if y ∈ ft then .code y else .unit)
      | .cst .unit => .unit
      | .cst (.int i) => .int i
      | .cst (.bool b) => .bool b
      | .cst (.str s) => .str s
      | .constr t fs =>
        .ctor t $ fs.map fun n => ρ.getD n (if n ∈ ft then .code n else .unit)
      | .lam .. => panic! "unexpected lambda after closure conversion"
    evalExpr ft (ρ.insert x vx) b
  | .letRhs x rhs b =>
    ρ.insert x <$> evalRhs ft ρ rhs >>= (evalExpr ft · b)
  | .letRec funs b =>
    evalExpr (funs.foldl (fun a f => a.insert f.fid f) ft) ρ b

partial def evalFun (ft : FunTab) (fid : Name) (payload : Val) : EIO TypingError Val := do
  checkInterrupt
  let some {param, body,..} := ft.get? fid
    | impossible! "unknown code pointer {fid}"
  evalExpr ft {(param, payload)} body
end

def evalModule (m : LModule) : EIO TypingError Val := checkInterrupt *>
  let ft : FunTab := m.funs.foldl (fun a f => a.insert f.fid f) {(m.main.fid, m.main)}
  let payload := Val.pair .unit (.ctor "𝐄" #[])
  evalFun ft m.main.fid payload

end LInterpreter
