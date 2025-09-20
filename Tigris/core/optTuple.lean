import Tigris.core.lam

/-!
Fuse projections, e.g.
  - `let x = t[i]` where `t` is
    1. a pair `(_, *)` of `mkPair a b`
    2. a ctor application of `mkConstr tag fields`
-/
namespace IR

open Std

inductive TInfo where
  | alias  (y : Name)
  | pair   (a b : Name)
  | constr (tag : Name) (fields : Array Name)
deriving Inhabited, Repr

abbrev TEnv := Std.HashMap Name TInfo

@[inline] partial def tChase (env : TEnv) (x : Name) : Name :=
  match env.get? x with
  | some (.alias y) =>
    if y == x then x else tChase env y
  | _ => x

@[inline] def tGetPair (env : TEnv) (x : Name) : Option (Name × Name) :=
  match env.get? (tChase env x) with
  | some (.pair a b) => some (a, b)
  | _ => none

@[inline] def tGetConstr (env : TEnv) (x : Name) : Option (Name × Array Name) :=
  match env.get? (tChase env x) with
  | some (.constr tag fs) => some (tag, fs)
  | _ => none

def fuseProj (env : TEnv) (dest : Name) (src : Name) (idx : Nat) : (LExpr × TEnv) :=
  let s := tChase env src
  match tGetPair env s with
  | some (a, b) =>
    let v := if idx == 0 then a else b
    (.letVal dest (.var v) (.seq #[] (.ret dest)), env.insert dest (.alias v))
  | none =>
    match tGetConstr env s with
    | some (_, fs) =>
      if h : idx < fs.size then
        let v := fs[idx]
        (.letVal dest (.var v) (.seq #[] (.ret dest)), env.insert dest (.alias v))
      else
        (.letRhs dest (.proj s idx) (.seq #[] (.ret dest)), env.erase dest)
    | none =>
        (.letRhs dest (.proj s idx) (.seq #[] (.ret dest)), env.erase dest)

def fuseRhs (env : TEnv) (x : Name) : Rhs -> (LExpr × TEnv)
  | .mkPair a b =>
    ( .letRhs x (.mkPair a b) (.seq #[] (.ret x))
    , env.insert x (.pair (tChase env a) (tChase env b)))
  | .mkConstr tag fs =>
    ( .letRhs x (.mkConstr tag (fs.map (tChase env))) (.seq #[] (.ret x))
    , env.insert x (.constr tag (fs.map (tChase env))))
  | .proj s i =>
    fuseProj env x s i
  | .prim op args =>
    (.letRhs x (.prim op (args.map (tChase env))) (.seq #[] (.ret x)), env.erase x)
  | .isConstr s t ar =>
    (.letRhs x (.isConstr (tChase env s) t ar) (.seq #[] (.ret x)), env.erase x)
  | .call f a =>
    (.letRhs x (.call (tChase env f) (tChase env a)) (.seq #[] (.ret x)), env.erase x)

partial def plugLet' (x : Name) (rhsOut : LExpr) (bodyK : LExpr -> LExpr) : LExpr :=
  match rhsOut with
  | .letVal y v rest =>
    if y == x then .letVal y v (bodyK rest)
    else .letVal y v (plugLet' x rest bodyK)
  | .letRhs y r rest =>
    if y == x then .letRhs y r (bodyK rest)
    else .letRhs y r (plugLet' x rest bodyK)
  | .seq _ _ => bodyK rhsOut
  | .letRec fs b => .letRec fs (plugLet' x b bodyK)

/- Main fusion pass. Keeps only projection/constructor/pair fusion and alias propagation. -/
mutual
partial def fuseValue (env : TEnv) : Value -> (Value × TEnv)
  | .var x       => (.var (tChase env x), env)
  | .cst k       => (.cst k, env)
  | .constr t fs => (.constr t (fs.map (tChase env)), env)
  | .lam p b     =>
    -- Do not cross lambda; clear knowledge about p and shadow captures
    let b' := fuseExpr (env.erase p) b
    (.lam p b', env.erase p)

partial def fuseTail (env : TEnv) : Tail -> Tail
  | .ret x      => .ret (tChase env x)
  | .app f a    => .app (tChase env f) (tChase env a)
  | .cond c t e => .cond (tChase env c) (fuseExpr env t) (fuseExpr env e)
  | .switchConst s cases d? =>
    .switchConst (tChase env s) (cases.map fun (k, b) => (k, fuseExpr env b))
      (d?.map (fuseExpr env))
  | .switchCtor s cases d? =>
    .switchCtor (tChase env s) (cases.map fun (c, ar, b) => (c, ar, fuseExpr env b))
      (d?.map (fuseExpr env))

partial def fuseExpr (env : TEnv) : LExpr -> LExpr
  | .letVal x v b =>
    let (v', env') := fuseValue env v
    -- Track aliases from letVal x (var y)
    let env'' :=
      match v' with
      | .var y => env'.insert x (.alias (tChase env' y))
      | _      => env'.erase x
    .letVal x v' (fuseExpr env'' b)

  | .letRhs x rhs b =>
    -- Rewrite RHS with fusion-aware env
    let (rhsOut, envAfter) := fuseRhs env x rhs
    plugLet' x rhsOut (fun _ => fuseExpr envAfter b)

  | .letRec funs b =>
    -- Reset any layout info that binds these ids; also do not cross param
    let kill := fun (e : TEnv) (f : LFun) => e.erase f.fid |>.erase f.param
    let env' := funs.foldl kill env
    let funs' :=
      funs.map fun ⟨fid, p, body⟩ =>
        ⟨fid, p, fuseExpr (env'.erase p) body⟩
    .letRec funs' (fuseExpr env' b)

  | .seq binds tail =>
    let binds' :=
      binds.map fun
        | .let1 x (.mkPair a b) =>
          .let1 x (.mkPair (tChase env a) (tChase env b))
        | .let1 x (.mkConstr t fs) =>
          .let1 x (.mkConstr t (fs.map (tChase env)))
        | .let1 x (.proj s i) =>
          -- local fusion in binds too
          match tGetPair env (tChase env s) with
          | some _ => .let1 x (.prim PrimOp.eqInt #[]) -- placeholder;
          | none =>
            match tGetConstr env (tChase env s) with
            | some (_, fs) =>
              if i < fs.size then
                  .let1 x (.prim PrimOp.eqInt #[]) -- placeholder;
              else .let1 x (.proj (tChase env s) i)
            | none => .let1 x (.proj (tChase env s) i)
        | .let1 x r =>
          .let1 x $
            match r with
            | .prim op args     => .prim op (args.map (tChase env))
            | .proj s i         => .proj (tChase env s) i
            | .mkPair a b       => .mkPair (tChase env a) (tChase env b)
            | .mkConstr t fs    => .mkConstr t (fs.map (tChase env))
            | .isConstr s t ar  => .isConstr (tChase env s) t ar
            | .call f a         => .call (tChase env f) (tChase env a)
    -- Binds have no scope to introduce alias here easily without restructuring;
    -- we leave deep bind fusion to constantFold/copy-prop paths and focus on letRhs/letVal.
    .seq binds' (fuseTail env tail)
end

@[inline] def fuseTupleProj (e : LExpr) : LExpr :=
  fuseExpr (∅ : TEnv) e

end IR
