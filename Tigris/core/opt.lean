import Tigris.core.lam

/-! optimizations for LExpr IR. Have done

- Constant folding/propagation
- Copy propagation + DCE
- Tailcallify, turn
  - `let r := call f a in return r`
  - `let r := call f a in pe* seq [e] (ret r)`
    where
    - `pe := <pure-letVal/letRhs>`
    - `r ∉ fv e ∧ r ∉ fv pe`
  into `fᵀ a`
-/

namespace IR

open Std

inductive KVal where
  | alia   (y : Name)
  | cst     (k : Const)
  | pair    (a b : Name)
  | constr  (tag : Name) (fields : Array Name)
deriving Inhabited, Repr

abbrev KEnv := Std.TreeMap Name KVal

partial def chase (env : KEnv) (x : Name) : Name :=
  match env.get? x with
  | some (.alia y) =>
    if y == x then x else chase env y
  | _ => x

partial def getConst (env : KEnv) (x : Name) : Option Const :=
  match env.get? (chase env x) with
  | some (.cst k) => some k
  | _ => none

partial def getConstr (env : KEnv) (x : Name) : Option (Name × Array Name) :=
  match env.get? (chase env x) with
  | some (.constr t fs) => some (t, fs)
  | _ => none

partial def getPair (env : KEnv) (x : Name) : Option (Name × Name) :=
  match env.get? (chase env x) with
  | some (.pair a b) => some (a, b)
  | _ => none

def fvRhs : Rhs -> Std.HashSet Name
  | .prim _ args   => args.foldl (·.insert ·) ∅
  | .proj s _      => {s}
  | .mkPair a b    => ({a} : Std.HashSet Name).insert b
  | .mkConstr _ fs => fs.foldl (init := ∅) (·.insert ·)
  | .isConstr s .. => {s}
  | .call f a      => ({f} : Std.HashSet Name).insert a

@[inline] def isPureRhs : Rhs -> Bool
  | .call .. => false
  | _        => true

mutual
partial def fvValue : Value -> Std.HashSet Name
  | .var x       => {x}
  | .cst _       => ∅
  | .constr _ fs => fs.foldl (init := ∅) (·.insert ·)
  | .lam p b     => fvExpr b |>.erase p

partial def fvTail : Tail -> Std.HashSet Name
  | .ret x      => {x}
  | .app f a    => ({f} : Std.HashSet Name).insert a
  | .cond c t e => fvExpr t ∪ fvExpr e |>.insert c
  | .switchConst s cases d? =>
    let acc := cases.foldl (· ∪ fvExpr ·.2) {s}
    match d? with
    | some b => acc ∪ fvExpr b
    | none   => acc
  | .switchCtor s cases d? =>
    let acc := cases.foldl (· ∪ fvExpr ·.2.2) {s}
    match d? with
    | some b => acc ∪ fvExpr b
    | none   => acc

partial def fvExpr : LExpr -> Std.HashSet Name
  | .letVal x v b =>
    letI s := fvValue v
    letI sb := fvExpr b
    s ∪ sb.erase x
  | .letRhs x r b =>
    letI s := fvRhs r
    letI sb := fvExpr b
    s ∪ sb.erase x
  | .letRec funs b =>
    letI sb := fvExpr b
    (·.2) <|
      funs.foldl
        (init := ((∅ : Std.HashSet Name), sb))
        fun (defs, acc) ⟨fid, p, body⟩ =>
          let fb := (fvExpr body).erase fid |>.erase p
          (defs.insert fid, acc ∪ fb)
  | .seq binds tail =>
    letI sb := binds.foldl (init := ∅) fun acc (.let1 _ rhs) => acc ∪ (fvRhs rhs)
    sb ∪ (fvTail tail)
end

def applyBinds (bs : Array Stmt) (e : LExpr) : LExpr :=
  bs.foldr (init := e) fun (.let1 x rhs) acc => .letRhs x rhs acc

def evalPrim (op : PrimOp) (args : Array Const) : Option Const :=
  match op, args.toList with
  | .add, [Const.int a, Const.int b] => some (.int (a + b))
  | .sub, [Const.int a, Const.int b] => some (.int (a - b))
  | .mul, [Const.int a, Const.int b] => some (.int (a * b))
  | .div, [Const.int a, Const.int b] =>
    if b == 0 then none else some (.int (a / b))
  | .eqInt,  [Const.int a,  Const.int b]  => some (.bool (a == b))
  | .eqBool, [Const.bool a, Const.bool b] => some (.bool (a == b))
  | .eqStr,  [Const.str a,  Const.str b]  => some (.bool (a == b))
  | _, _ => none

mutual
partial def cfValue (env : KEnv) : Value -> Value
  | .var x => .var (chase env x)
  | .cst k => .cst k
  | .constr t fs => .constr t (fs.map (chase env))
  | .lam p b => .lam p (cfExpr (env.erase p) b)

partial def cfRhs (env : KEnv) (x : Name) : Rhs -> (LExpr × KEnv)
  | .prim op args =>
    let names := args.map (chase env)
    let consts := names.map (getConst env)
    if consts.all (·.isSome) then
      match evalPrim op (consts.map (·.getD Const.unit)) with
      | some k =>
        let env' := env.insert x (.cst k)
        (.letVal x (.cst k) (.seq #[] (.ret x)), env')
      | none =>
        (.letRhs x (.prim op names) (.seq #[] (.ret x)), env.erase x)
    else
      (.letRhs x (.prim op names) (.seq #[] (.ret x)), env.erase x)
  | .proj s i =>
    let s' := chase env s
    match getPair env s' with
    | some (a, b) =>
      let v := if i == 0 then a else b
      let env' := env.insert x (.alia v)
      (.letVal x (.var v) (.seq #[] (.ret x)), env')
    | none =>
      match getConstr env s' with
      | some (_, fs) =>
        if h : i < fs.size then
          let v := fs[i]
          let env' := env.insert x (.alia v)
          (.letVal x (.var v) (.seq #[] (.ret x)), env')
        else
          (.letRhs x (.proj s' i) (.seq #[] (.ret x)), env.erase x)
      | none =>
        (.letRhs x (.proj s' i) (.seq #[] (.ret x)), env.erase x)
  | .mkPair a b =>
    let a' := chase env a
    let b' := chase env b
    letI env' := env.insert x (.pair a' b')
    (.letRhs x (.mkPair a' b') (.seq #[] (.ret x)), env')
  | .mkConstr tag fs =>
    let fs' := fs.map (chase env)
    letI env' := env.insert x (.constr tag fs')
    (.letRhs x (.mkConstr tag fs') (.seq #[] (.ret x)), env')
  | .isConstr s tag ar =>
    letI s' := chase env s
    match getConstr env s' with
    | some (t, fs) =>
      let b := (t == tag) && (fs.size == ar)
      let env' := env.insert x (.cst (.bool b))
      (.letVal x (.cst (.bool b)) (.seq #[] (.ret x)), env')
    | none =>
      (.letRhs x (.isConstr s' tag ar) (.seq #[] (.ret x)), env.erase x)
  | .call f a =>
    letI f' := chase env f
    letI a' := chase env a
    (.letRhs x (.call f' a') (.seq #[] (.ret x)), env.erase x)

partial def plugLet (x : Name) (rhsOut : LExpr) (bodyK : LExpr -> LExpr) : LExpr :=
  match rhsOut with
  | .letVal y v rest =>
    if y == x then .letVal y v (bodyK rest)
    else .letVal y v (plugLet x rest bodyK)
  | .letRhs y r rest =>
    if y == x then .letRhs y r (bodyK rest)
    else .letRhs y r (plugLet x rest bodyK)
  | .seq _ _ => bodyK rhsOut
  | .letRec fs b => .letRec fs (plugLet x b bodyK)

partial def cfTail (env : KEnv) : Tail -> Tail
  | .ret x => .ret (chase env x)
  | .app f a => .app (chase env f) (chase env a)
  | .cond c t e =>
    letI c' := chase env c
    letI t' := cfExpr env t
    letI e' := cfExpr env e
    .cond c' t' e'
  | .switchConst s cases d? =>
    letI s' := chase env s
    letI cases' := cases.map fun (k, b) => (k, cfExpr env b)
    letI d' := d? |>.map (cfExpr env)
    .switchConst s' cases' d'
  | .switchCtor s cases d? =>
    letI s' := chase env s
    letI cases' := cases.map fun (c, ar, b) => (c, ar, cfExpr env b)
    letI d' := d? |>.map (cfExpr env)
    .switchCtor s' cases' d'

partial def cfExpr (env : KEnv) : LExpr -> LExpr
  | .letVal x v body =>
    let v' := cfValue env v
    letI env' :=
      match v' with
      | .var y => env.insert x (.alia (chase env y))
      | .cst k => env.insert x (.cst k)
      | .lam p _ => env.erase x |>.erase p -- shadowing
      | .constr _ _ => env.erase x
    let b' := cfExpr env' body
    .letVal x v' b'
  | .letRhs x rhs body =>
    let (rhsOut, envAfter) := cfRhs env x rhs
    plugLet x rhsOut fun _ => cfExpr envAfter body
  | .letRec funs body =>
    letI ids   := funs.map (·.fid)
    let env'  := env.eraseMany ids
    letI funs' := funs.map fun ⟨fid, p, b⟩ => ⟨fid, p, cfExpr (env'.erase p) b⟩
    .letRec funs' (cfExpr env' body)
  | .seq binds tail =>
    match cfTail env tail with
    | .cond c t e =>
      match getConst env c with
      | some (.bool true)  => applyBinds binds t
      | some (.bool false) => applyBinds binds e
      | _ => .seq binds (.cond c t e)
    | .switchConst s cases d? =>
      match getConst env s with
      | some k =>
        match cases.findSome? fun (k', b) => if k' == k then some b else none with
        | some b => applyBinds binds b
        | none   => match d? with
                    | some b => applyBinds binds b
                    | none   => .seq binds (.switchConst s cases d?)
      | none => .seq binds (.switchConst s cases d?)
    | .switchCtor s cases d? =>
      -- NEW: choose a constructor case if scrutinee is known
      match getConstr env s with
      | some (tag, fs) =>
        let c := cases.findSome? fun (c, ar, b) =>
          if c == tag && ar == fs.size then some b else none
        match c with
        | some b => applyBinds binds b
        | none   =>
          match d? with
          | some b => applyBinds binds b
          | none   => .seq binds (.switchCtor s cases d?)
      | none => .seq binds (.switchCtor s cases d?)
    | tail => .seq binds tail

end

@[inline] def constantFold (e : LExpr) : LExpr :=
  cfExpr ∅ e

/-- DCE -/
abbrev UMap := Std.HashMap Name Nat

@[inline] def bump (m : UMap) (x : Name) : UMap :=
  m.alter x fun
            | some x => some $ x + 1
            | none => some 1

@[inline] def bumpMany (m : UMap) (xs : Array Name) : UMap :=
  xs.foldl bump m

@[inline] def dec (m : UMap) (x : Name) : UMap :=
  m.alter x fun
            | t@(some 0) => t
            | some n => some $ n - 1
            | none   => some 0

@[inline] def decMany (m : UMap) (xs : Array Name) : UMap :=
  xs.foldl dec m

@[inline] def decByValue (m : UMap) : Value -> UMap
  | .var y        => dec m y
  | .cst _        => m
  | .constr _ fs  => decMany m fs
  | .lam _ _      => m

@[inline] def decByRhs (m : UMap) : Rhs -> UMap
  | .prim _ args     => decMany m args
  | .proj s _        => dec m s
  | .mkPair a b      => dec (dec m a) b
  | .mkConstr _ fs   => decMany m fs
  | .isConstr s ..   => dec m s
  | .call f a        => dec (dec m f) a

mutual
partial def countValue : Value -> UMap -> UMap
  | .var x, m       => bump m x
  | .cst _, m       => m
  | .constr _ fs, m => bumpMany m fs
  | .lam _ b, m     => countExpr b m

partial def countRhs : Rhs -> UMap -> UMap
  | .prim _ args, m    => bumpMany m args
  | .proj s _, m       => bump m s
  | .mkPair a b, m     => bump (bump m a) b
  | .mkConstr _ fs, m  => bumpMany m fs
  | .isConstr s .., m  => bump m s
  | .call f a, m       => bump (bump m f) a

partial def countTail : Tail -> UMap -> UMap
  | .ret x, m        => bump m x
  | .app f a, m      => bump (bump m f) a
  | .cond c t e, m   =>
    let m := countExpr t $ bump m c
    countExpr e m
  | .switchConst s cases d?, m =>
    let m := cases.foldl (init := bump m s) fun a (_, b) => countExpr b a
    match d? with | some b => countExpr b m | none => m
  | .switchCtor s cases d?, m =>
    let m := cases.foldl (init := bump m s) fun a (_, _, b) => countExpr b a
    match d? with | some b => countExpr b m | none => m
partial def countExpr : LExpr -> UMap -> UMap
  | .letVal _ v b, m  => countExpr b (countValue v m)
  | .letRhs _ r b, m  => countExpr b (countRhs r m)
  | .letRec fs b, m   =>
    let m := fs.foldl (init := m) fun acc ⟨_, _, body⟩ => countExpr body acc
    countExpr b m
  | .seq binds tail, m =>
    let m := binds.foldl (init := m) fun acc (.let1 _ rhs) => countRhs rhs acc
    countTail tail m
end

@[inline] def UMap.ofExpr (e : LExpr) : UMap :=
  countExpr e ∅

/-- copy-prop-dce -/
abbrev AEnv := Std.HashMap Name Name

@[inline] partial def aChase (env : AEnv) (x : Name) : Name :=
  match env.get? x with
  | some y => if y == x then x else aChase env y
  | none   => x

@[inline] def rwName (env : AEnv) (x : Name) : Name := aChase env x
@[inline] def rwArgs (env : AEnv) (xs : Array Name) : Array Name := xs.map (rwName env)

def rwRhs (env : AEnv) : Rhs -> Rhs
  | .prim op args     => .prim op (rwArgs env args)
  | .proj s i         => .proj (rwName env s) i
  | .mkPair a b       => .mkPair (rwName env a) (rwName env b)
  | .mkConstr t fs    => .mkConstr t (rwArgs env fs)
  | .isConstr s t ar  => .isConstr (rwName env s) t ar
  | .call f a         => .call (rwName env f) (rwName env a)

def ηLam? : Value -> Option Value
  | .lam p (.seq #[] (.app g a)) =>
      if a == p then some (.var g) else none
  | _ => none

mutual
partial def rwValue (env : AEnv) : Value -> Value
  | .var x       => .var (rwName env x)
  | .cst k       => .cst k
  | .constr t fs => .constr t (rwArgs env fs)
  | .lam p b     => .lam p (cpdce (env.erase p) ∅ b)

partial def cpdce (env : AEnv) (uses : UMap) : LExpr -> LExpr
  | .letVal x v body =>
    let v := ηLam? v |>.getD v
    let body' := cpdce (env.erase x) uses body
    let used := (fvExpr body').contains x
    match v with
    | .var y =>
      if used then
        .letVal x (.var (rwName env y)) body'
      else
        cpdce env (dec uses (rwName env y)) body'
    | _ =>
      let v' := rwValue env v
      if used then
        .letVal x v' body'
      else
        cpdce env (decByValue uses v') body'

  | .letRhs x rhs body =>
    let body' := cpdce (env.erase x) uses body
    let rhs' := rwRhs env rhs
    let used := (fvExpr body').contains x
    if !used && isPureRhs rhs' then
      cpdce env (decByRhs uses rhs') body'
    else .letRhs x rhs' body'

  | .letRec funs body =>
    let funs' := funs.map fun ⟨fid, p, b⟩ =>
      ⟨fid, p, cpdce (env.erase fid |>.erase p) uses b⟩
    let body' := cpdce env uses body
    let keep := funs'.any fun ⟨fid, _, _⟩ => (fvExpr body').contains fid
    if keep then .letRec funs' body'
    else body'

  | .seq binds tail =>
    let tail' :=
      match tail with
      | .ret x      => .ret (rwName env x)
      | .app f a    => .app (rwName env f) (rwName env a)
      | .cond c t e => .cond (rwName env c) (cpdce env uses t) (cpdce env uses e)
      | .switchConst s cases d? =>
        .switchConst
          (rwName env s)
          (cases.map (fun (k, b) => (k, cpdce env uses b)))
          (d? |>.map (cpdce env uses))
      | .switchCtor s cases d? =>
        .switchCtor
          (rwName env s)
          (cases.map (fun (c, ar, b) => (c, ar, cpdce env uses b)))
          (d? |>.map (cpdce env uses))
    let (_ , binds') :=
      binds.foldl (init := (uses, (#[] : Array Stmt))) fun (u, acc) (.let1 y rhs) =>
        let rhs' := rwRhs env rhs
        if isPureRhs rhs' && u.getD y 0 == 0 then
          (decByRhs u rhs', acc)
        else
          (u, acc.push (.let1 y rhs'))
    .seq binds' tail'
end

@[inline] def copyPropDCE (e : LExpr) : LExpr :=
  cpdce (∅ : AEnv) (.ofExpr e) e

def bindsArePureNoUse (x : Name) (binds : Array Stmt) : Bool :=
  binds.all fun (.let1 _ rhs) => isPureRhs rhs && !(fvRhs rhs).contains x

def peelAfterCall (x : Name) : LExpr -> Option (Array Stmt)
  | .seq binds (Tail.ret y) =>
    if y == x && bindsArePureNoUse x binds then some binds else none
  | .letRhs _ rhs rest =>
    if isPureRhs rhs && !(fvRhs rhs).contains x then
      peelAfterCall x rest
    else none
  | .letVal _ v rest =>
    if !(fvValue v).contains x then
      peelAfterCall x rest
    else none
  | _ => none

/-- Tailcall opt, eligible for
    - let r := call f a in seq [] (ret r)
    - let r := call f a in
      (pure letVal/letRhs not using r)*
      seq [pure-binds not using r] (ret r)
-/
partial def tailcallify : LExpr -> LExpr := fun e =>
  match e with
  | .letVal x (.lam p b) body =>
    .letVal x (.lam p (tailcallify b)) (tailcallify body)
  | .letVal x v body => .letVal x v (tailcallify body)

  | .letRhs x (.call f a) body =>
    let body' := tailcallify body
    match peelAfterCall x body' with
    | some _ =>
      .seq #[] (.app f a)
    | none   =>
      .letRhs x (.call f a) body'

  | .letRhs x rhs body =>
    .letRhs x rhs (tailcallify body)

  | .letRec funs body =>
    letI funs' := funs.map fun ⟨fid, p, b⟩ => ⟨fid, p, tailcallify b⟩
    .letRec funs' (tailcallify body)

  | .seq binds tail =>
    .seq binds $
      match tail with
      | .cond c t e => .cond c (tailcallify t) (tailcallify e)
      | .switchConst s c d =>
        .switchConst s (c.map (·.map id tailcallify)) (tailcallify <$> d)
      | .switchCtor s c d =>
        .switchCtor s (c.map fun (n, a, e) => (n, a, tailcallify e)) (tailcallify <$> d)
      | t => t

/--
  1. constant folding
  2. copy-prop-DCE (needed for tailcallify)
  3. tailcall
  4. copy-prop-DCE again
-/
def optimizeLam (e : LExpr) : LExpr :=
--  letI e0 := fuseTupleProj e
  letI e1 := constantFold e
  letI e2 := copyPropDCE e1
  letI e3 := tailcallify e2
  letI e4 := copyPropDCE e3
  e4
