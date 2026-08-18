import Tigris.oldcore2.lift
import Tigris.typing.fexpr
import Tigris.oldcore2.matchAppF
import PP

namespace IRf open IR MLType open FExpr open SysF.Helper (pvs) open Helper

private abbrev Env := IR.Env

variable {σ}

namespace HelperF

/--
- `t × u`        has `.pair`
- `t -> u`       has `.ctor "𝐂" 2`    `(cons '𝐂 #(code env))`
- ADT/Imm Values has `.unknown`
Type schemes / quantified types are peeled to their monotype body. -/
partial def shapeOfMLType : MLType -> Shape
  | .TSch (.Forall _ _ t) => shapeOfMLType t
  | _ ×'' _   => .pair
  | _ ->' _   => .ctor "𝐂" 2
  | _          => .unknown
@[inline] def shapeOfFExpr : FExpr -> Shape := shapeOfMLType ∘ FExpr.getTy

def primOfName : String -> Option PrimOp
  | "add"     => some .add
  | "sub"     => some .sub
  | "mul"     => some .mul
  | "div"     => some .div
  | "__eqInt"   => some .eqInt
  | "__eqBool"  => some .eqBool
  | "__eqString"=> some .eqStr
  | _           => none
def matchBinaryPrim : FExpr -> Option (PrimOp × FExpr × FExpr)
  | .App (.App (.Var f _) x _) y _ => (·, x, y) <$> primOfName f
  | .App (.Var f _) (.Prod' x y _) _ => (·, x, y) <$> primOfName f
  | _ => none
def decomposeApp : FExpr -> (FExpr × Array FExpr)
  | .App f a _ =>
    let (h, as) := decomposeApp f
    (h, as.push a)
  | e => (e, #[])
def decomposeLamChain : (fe : FExpr) -> (h : fe = FExpr.Fun p pty b ty) -> String × Array String × FExpr
  | .Fun p _ b _, _ => (p, go b #[])
where go
  | .Fun q _ b _, acc => go b (acc.push q)
  | e, acc => (acc, e)

def isDictName : String -> Bool := fun x => x.startsWith "d_" || x.startsWith "rd_"
def isDictArg : FExpr -> Bool
  | .Var x _ => isDictName x
  | _ => false

def arrArity : MLType -> Nat
  | .TSch (.Forall _ _ t) => arrArity t
  | .TArr _ b => 1 + arrArity b
  | _         => 0
def getArrArity : FExpr -> Nat := arrArity ∘ FExpr.getTy

def matchCtorApp (ctorArity : Std.HashMap String Nat) (e : FExpr)
  : Option (String × Array FExpr × Nat) :=
  let (h, args) := decomposeApp e
  match h with
  | .Var cname _ =>
    match ctorArity[cname]? with
    | some ar => some (cname, args, ar)
    | none => none
  | _ => none

def splitLetGroup
  (xs : Array (Name × Scheme × FExpr))
  : (Array (Name × Name × Array Name × FExpr) × Array (Name × FExpr)) :=
  xs.foldl
    (init := (#[], #[]))
    fun (recs, nonrecs) (x, _, e) =>
      match e with
      | .Fix lam@(.Fun ..) _ => (recs.push (x, decomposeLamChain lam ‹_›), nonrecs)
      | _ => (recs, nonrecs.push (x, e))

def realizeSel (roots : Array Name) : Sel -> (Name -> M σ LExpr) -> M σ LExpr
  | .base i, k => k roots[i]!
  | .field s i, k => realizeSel roots s fun v => do
    let p <- fresh "p"
    let cont <- k p
    return .letRhs p (.proj v i) cont

def collectTopPatBinds (p : Pattern) (s : Sel) : Array (String × Sel) := go p s where
  go
  | .PVar x, sel      => #[(x, sel)]
  | .PWild, _         => #[]
  | .PConst _, _      => #[]
  | .PProd' p q, sel  => go p (.field sel 0) ++ go q (.field sel 1)
  | .PCtor _ as, sel  =>
    as.size.fold (init := #[]) fun i _ acc => acc ++ go as[i] (.field sel i)

partial def bindPatBinds
  (roots : Array Name)
  (bs : Subarray (String × Sel))
  (ρ : Env)
  (k : Env -> M σ LExpr) : M σ LExpr :=
  if h : bs.size = 0 then k ρ
  else
    let (x, sel) := bs[0]
    realizeSel roots sel fun v => do
      (.letVal x (.var v) ·) <$> bindPatBinds roots bs[1:] (ρ.insert x x) k

def predToApp : Pred -> MLType := fun {cls, args} => MLType.mkApp (TCon cls) args
def unwrapTSch : MLType -> MLType
  | TSch (.Forall _ _ps t) => /-ps.foldr (TArr ∘ predToApp)-/ t
  | t => t

partial def stripTy : FExpr -> FExpr
  | FExpr.TyApp f _ | FExpr.TyLam _ f => stripTy f
  | Let bs body ty =>
    Let (bs.map fun (id, sch, fe) => (id, sch, stripTy fe)) (stripTy body) (unwrapTSch ty)
  | Proj fe s id ty => Proj (stripTy fe) s id (unwrapTSch ty)
  | Fix e ty => Fix (stripTy e) (unwrapTSch ty)
  | Match ds bs res ex red => Match (ds.map stripTy) (bs.map fun (pat, e) => (pat, stripTy e)) (unwrapTSch res) ex red
  | Cond c t e ty => Cond (stripTy c) (stripTy t) (stripTy e) (unwrapTSch ty)
  | Prod' p q ty => Prod' (stripTy p) (stripTy q) (unwrapTSch ty)
  | App f a ty => App (stripTy f) (stripTy a) (unwrapTSch ty)
  | Fun p pty b ty => Fun p (unwrapTSch pty) (stripTy b) (unwrapTSch ty)
  | Var x ty => Var x (unwrapTSch ty)
  | t => t

partial def findReturnedVar : FExpr -> Option (String × MLType × (FExpr -> FExpr))
  | .Var v ty => some (v, ty, id)
  | .Match scrs branches resTy ex red =>
    if h : branches.size = 1 then
      let (pats, rhs) := branches[0]
      match findReturnedVar rhs with
      | some (v, vty, reb) =>
        some (v, vty, fun new =>
          .Match scrs #[(pats, reb new)] resTy ex red)
      | none => none
    else
      none
  | _ => none

def etaExpandParams (params : Array String) (core : FExpr) : (Array String × FExpr) :=
  match findReturnedVar core with
  | none => (params, core)
  | some (v, vTy, rebuild) =>
    let (argTys, _) := decomposeArr vTy
    if argTys.isEmpty then
      (params, core)
    else
      -- build applications f η0 η1 ... with proper types
      let rec mk (f : FExpr) (ty : MLType) (i : Nat) (accP : Array String)
        : (Array String × FExpr) :=
        match ty with
        | .TArr a b =>
          let pName := s!"η{i}"
          let f'    := .App f (.Var pName a) b
          mk f' b (i+1) (accP.push pName)
        | _ => (accP, f)
      let (newPs, applied) := mk (.Var v vTy) vTy 0 #[]
      let allParams := params ++ newPs
      (allParams, rebuild applied)

end HelperF

open HelperF

mutual
partial def lowerMany
  (es : Array FExpr) (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Array Name -> M σ LExpr) : M σ LExpr := go 0 #[] where
  go i acc : M σ LExpr :=
    if h : i < es.size then lowerF es[i] ρ ctors $ go i.succ ∘ acc.push
    else k acc

partial def lowerFunApp
  (head : FExpr) (args : Array FExpr)
  (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr :=
  let n := getArrArity head
  -- Intermediate (curried) call results are themselves functions
  -- (i.e. closures `(cons '𝐂 #(code env))`). Only the FINAL call's
  -- result shape comes from the outermost FExpr's type, set by the caller
  -- via the wrapper `k` (see callsite in lowerF .App branch).
  let curried : Shape := .ctor "𝐂" 2

  let applyUnary (vfName aName : Name) (cont : Name -> M σ LExpr) : M σ LExpr := do
    let u <- fresh "u"
    setShape u .unknown
    let pair <- fresh "pair"
    setShape pair .pair
    let r <- fresh "call"
    setShape r curried
    let body <- cont r
    pure
    $ .letVal u (.cst .unit)
    $ .letRhs pair (.mkPair aName u)
    $ .letRhs r (.call vfName pair) body

  let callWithMany (fv : Name) (ns : Array Name) : M σ LExpr := do
    if ns.isEmpty then k fv
    else if h : ns.size = 1 then
      applyUnary fv ns[0] k
    else
      buildPairs (name := ns.toList) fun tuple => do
        let r0 <- fresh "r"
        setShape r0 curried
        .letRhs r0 (.call fv tuple) <$> k r0

  let mkPartial (fv : Name) (supplied : Array Name) (missing : Nat) : M σ LExpr := do
    let lamV <- do
      if missing = 1 then
        let p   <- fresh "arg"
        setShape p .pair
        let aL  <- fresh "_pL#arg"
        let _aR <- fresh "_pR#arg"
        let res <- fresh "r"
        setShape res curried
        let allArgs := supplied.push aL
        let callCore <- buildPairs (name := allArgs.toList) fun tuple =>
          pure $ .letRhs res (.call fv tuple) (.seq #[] (.ret res))
        let body :=
          .letRhs aL  (.proj p 0) $
          .letRhs _aR (.proj p 1) $
          callCore
        pure (.lam p body)
      else
        let param <- fresh "rest"
        setShape param .pair
        let restNames : Array Name <- (missing - 1).foldM (init := #[]) fun _ _ acc =>
          acc.push <$> fresh
        let allArgs := supplied ++ restNames.push param
        let res <- fresh "r"
        setShape res curried
        let callCore <- buildPairs (name := allArgs.toList) fun tuple =>
          pure $ .letRhs res (.call fv tuple) (.seq #[] (.ret res))
        let lamBody := destructTuple param (restNames.push param) 0 callCore
        pure (.lam param lamBody)
    let out <- fresh "clos"
    setShape out (.ctor "𝐂" 2)
    let cont <- k out
    pure (.letVal out lamV cont)

  let applyRest (fv : Name) (rest : Array Name) : M σ LExpr := do
    if rest.isEmpty then k fv
    else if h : rest.size = 1 then applyUnary fv rest[0] k
    else
      buildPairs (name := rest.toList) fun tuple2 => do
        let r1 <- fresh "r"
        setShape r1 curried
        .letRhs r1 (.call fv tuple2) <$> k r1

  let applyAllWithTotal (total : Nat) (vf : Name) (ns : Array Name) : M σ LExpr := do
    if total = 0 then callWithMany vf ns
    else if ns.size < total then mkPartial vf ns (total - ns.size)
    else if ns.size = total then callWithMany vf ns
    else
      let now  := ns[:total]
      let rest := ns[total:]
      if h : now.size = 1 then applyUnary vf now[0] (applyRest · rest)
      else
        buildPairs (name := now.toList) fun tuple => do
          let r0 <- fresh "r"
          setShape r0 curried
          .letRhs r0 (.call vf tuple) <$> applyRest r0 rest

  let applyByType (vf : Name) (ns : Array Name) : M σ LExpr := do
    if n = 0 then callWithMany vf ns
    else if ns.size < n then mkPartial vf ns (n - ns.size)
    else if ns.size = n then callWithMany vf ns
    else
      let now := ns[:n]
      let rest := ns[n:]
      if h : now.size = 1 then applyUnary vf now[0] (applyRest · rest)
      else
        buildPairs (name := now.toList) fun tuple => do
          let r0 <- fresh "r"
          setShape r0 curried
          let after <- applyRest r0 rest
          pure (.letRhs r0 (.call vf tuple) after)

  let applyBroken (total : Nat) (vf0 : Name) : M σ LExpr := do
    let dp := Nat.min total args.size
    have := Nat.min_le_right total args.size
    let rec applyD (i : Nat) (vf : Name) : M σ LExpr := do
      if h : i < dp then
        have := Nat.lt_of_lt_of_le h this
        lowerF args[i] ρ ctors fun a => applyUnary vf a (applyD (i + 1))
      else
        let rest := args[dp:]
        if rest.isEmpty then k vf
        else
          lowerMany rest ρ ctors fun ns =>
            if h : ns.size = 1 then applyUnary vf ns[0] k
            else
              buildPairs (name := ns.toList) fun tuple => do
                let r1 <- fresh "r"
                setShape r1 curried
                .letRhs r1 (.call vf tuple) <$> k r1
    applyD 0 vf0

  lowerF head ρ ctors fun vf0 => do
    let ar? <- getArity vf0
    lowerMany args ρ ctors fun ns => do
      match ar? with
      | some total =>
        if total < n then
          applyBroken total vf0
        else
          applyAllWithTotal total vf0 ns
      | none =>
        applyByType vf0 ns

partial def lowerF
  (e : FExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr := do
  match matchBinaryPrim e with
  | some (op, x, y) =>
    lowerF x ρ ctors fun vx =>
      lowerF y ρ ctors fun vy => do
        let r <- fresh "p"
        setShape r .unknown -- primitive int/bool/string
        let cont <- k r
        return .letRhs r (.prim op #[vx, vy]) cont
  | none =>
    match matchCtorApp ctors e with
    | some (cname, args, ar) =>
      if ar == 0 && args.isEmpty then
        let r <- fresh "con"
        setShape r (.ctor cname 0)
        let cont <- k r
        return (.letRhs r (.mkConstr cname #[]) cont)
      else lowerCtorApp cname args ar ρ ctors k
    | none =>
      match h : e with
      | .TyLam _ t | .TyApp t _ => lowerF t ρ ctors k

      | .Var x _ =>
        match ctors[x]? with
        | some 0 =>
          let r <- fresh "con"
          setShape r (.ctor x 0)
          let cont <- k r
          return (.letRhs r (.mkConstr x #[]) cont)
        | _ => k (ρ.getD x x)

      | .CI i _ =>
        let v <- fresh "c"; setShape v .unknown
        let body <- k v; return .letVal v (.cst (.int i)) body
      | .CB i _ =>
        let v <- fresh "c"; setShape v .unknown
        let body <- k v; return .letVal v (.cst (.bool i)) body
      | .CS i _ =>
        let v <- fresh "c"; setShape v .unknown
        let body <- k v; return .letVal v (.cst (.str i)) body
      | .CUnit _ =>
        let v <- fresh "c"; setShape v .unknown
        let body <- k v; return .letVal v (.cst .unit) body

      | .Prod' l r _ =>
        lowerF l ρ ctors fun lv =>
          lowerF r ρ ctors fun rv => do
            let p <- fresh "p"
            setShape p .pair
            let body <- k p
            return .letRhs p (.mkPair lv rv) body

      | .Proj src _ idx ty =>
        lowerF src ρ ctors fun sv => do
          let p <- fresh "p"
          setShape p (shapeOfMLType ty)
          let body <- k p
          return .letRhs p (.proj sv idx) body

      | .Fun .. =>
        let (p0, rest, core) := decomposeLamChain e h
        let tupleParam <- fresh "args"
        setShape tupleParam .pair -- multi-arg pack is nested pair
        let baseParams := #[p0] ++ rest
        let (allParams, core) := etaExpandParams baseParams core
        recordParamShapes allParams (peelArgTys (FExpr.getTy e))
        let ρ := allParams.foldl (fun acc p => acc.insert p p) ρ
        let loweredCore <- lowerFCore core ρ ctors
        let body := destructArgsPrelude tupleParam allParams loweredCore
        let f <- fresh "lam"
        setArity f allParams.size
        -- after closure-conversion `f` is `(cons '𝐂 #(code env))`
        setShape f (.ctor "𝐂" 2)
        let kbody <- k f
        return .letVal f (.lam tupleParam body) kbody

      | .App .. =>
        let (head, args) := decomposeApp e
        let resSh := shapeOfFExpr e
        lowerFunApp head args ρ ctors fun r => do
          setShape r resSh
          k r
      | .Cond c t e _ =>
        lowerF c ρ ctors fun cv =>
          .seq #[] <$> ((.cond cv · ·) <$> lowerF t ρ ctors k <*> lowerF e ρ ctors k)
      | .Let bs body _ =>
        let (recs, nonrecs) := splitLetGroup bs
        lowerNonRecBinds nonrecs.toSubarray ρ ctors fun ρ => do
          if recs.isEmpty then lowerF body ρ ctors k
          else
            let ρ := recs.foldl (fun acc (fid, _, _, _) => acc.insert fid fid) ρ
            let funs <- recs.mapM fun (fid, selfN, params, core) => do
              let (params, core) := etaExpandParams params core
              lowerRecFun fid selfN params core ρ ctors
            let bodyExpr <- lowerF body ρ ctors k
            return .letRec funs bodyExpr
      | .Fix lam@(.Fun ..) fixTy => do
        let (selfN, params, core) := decomposeLamChain lam ‹_›
        let (params, core) := etaExpandParams params core
        let fname <- fresh "f"
        let funIR <- lowerRecFun fname selfN params core ρ ctors fixTy
        let r <- fresh "r"
        setShape r (.ctor "𝐂" 2)
        let cont <- k r
        return .letRec #[funIR] (.letVal r (.var fname) cont)
      | .Fix .. => unreachable!

      | .Match scrs rows _ ex _ =>
        lowerMany scrs ρ ctors fun svars =>
          lowerMatchDT svars rows ex.isNone ρ ctors k

@[inline] partial def lowerFCore (e : FExpr) (ρ : Env) (ctors : Std.HashMap String Nat) : M σ LExpr :=
  lowerF e ρ ctors $ pure ∘ .seq #[] ∘ .ret

partial def lowerCtorApp
  (cname : String) (args : Array FExpr) (arity : Nat)
  (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr :=
  if args.size = arity then
    lowerMany args ρ ctors fun names => do
      let r <- fresh "con"
      setShape r (.ctor cname arity)
      let cont <- k r
      pure (.letRhs r (.mkConstr cname names) cont)
  else if args.size < arity then
    lowerMany args ρ ctors fun supplied => do
      let missing := arity - args.size
      let rec buildLam (i : Nat) (captured : Array Name) : M σ Value := do
        let p <- fresh "arg"
        setShape p .unknown
        if i + 1 < missing then
          let inner <- buildLam (i+1) (captured.push p)
          let v <- fresh "lam"
          setShape v (.ctor "𝐂" 2)
          let body := .letVal v inner (.seq #[] (.ret v))
          pure (.lam p body)
        else
          let res <- fresh "r"
          setShape res (.ctor cname arity)
          let fields := supplied ++ captured.push p
          let body := .letRhs res (.mkConstr cname fields) (.seq #[] (.ret res))
          pure (.lam p body)
      let lamV <- buildLam 0 #[]
      let out <- fresh "clos"
      setShape out (.ctor "𝐂" 2)
      let cont <- k out
      pure (.letVal out lamV cont)
  else -- should get blocked by typechecker, unreachable
    lowerF
      (args.foldl (init := FExpr.Var cname (MLType.TVar $ .named "?"))
      (fun f a => FExpr.App f a (MLType.TVar $ .named "?")))
      ρ ctors k

/-- Collapse argument types from a (possibly polymorphic) function type. -/
partial def peelArgTys : MLType -> Array MLType
  | .TSch (.Forall _ _ t) => peelArgTys t
  | a ->' b => #[a] ++ peelArgTys b
  | _ => #[]
/--
Also records shapes for the `_pL#name` / `_pR#name` destructure-introduced
names that `destructArgsPrelude` emits.


- for `sz = 1`:
  - `_pL#p₀` → shape of `p₀`
  - `_pR#p₀` → `.unknown` (dummy sentinel unit)

- for `sz ≥ 2`:
  - `_pL#pᵢ === pᵢ` → shape of `pᵢ`                     i < sz - 1
  - `_pR#pᵢ === (p_{i+1}, …)` → `.pair`                 i < sz - 2
  - `_pR#p_{sz-2} === p_{sz-1}` → shape of `p_{sz-1}`

**Note**: Getting the last `_pR` wrong would mark a function-typed argument as a `.pair`,
causing codegen to use `(car x)` instead of `(svref (cdr x) 0)` to project
the closure's codeptr, returning the ctor tag `𝐂` instead of a function. -/
private partial def recordParamShapes (params : Array String) (paramTys : Array MLType) : M σ Unit := do
  let shapeOfParam (i : Nat) : Shape :=
    if h : i < paramTys.size then shapeOfMLType paramTys[i] else .unknown
  let sz := params.size
  for h : i in [:sz] do
    let sh := shapeOfParam i
    setShape params[i] sh
    setShape s!"_pL#{params[i]}" sh
  if h : sz = 1 then
    setShape s!"_pR#{params[0]}" .unknown
  else if hgt : sz > 1 then
    -- Intermediate `_pR#pᵢ` (i < sz - 2) are sub-pairs.
    for h : i in [:sz - 2] do
      have : sz - 2 < sz := by omega
      have := Membership.get_elem_helper h rfl
      setShape s!"_pR#{params[i]}" .pair
    -- Final `_pR#p_{sz-2}` aliases the last param's value.
    setShape s!"_pR#{params[sz - 2]}" (shapeOfParam (sz - 1))

partial def lowerRecFun
  (fid : Name) (selfN : String) (params : Array String) (core : FExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (fnTy : MLType := .TVar $ .named "?")
  : M σ LFun := do
  let ρ := ρ.insert selfN fid
  -- The function value itself is a closure after CC
  setShape fid (.ctor "𝐂" 2)
  setShape selfN (.ctor "𝐂" 2)
  recordParamShapes params (peelArgTys fnTy)
  if params.size = 0 then
    let p <- fresh "arg"
    setShape p .unknown
    let body <- lowerFCore core (ρ.insert p p) ctors
    setArity fid 0
    return {fid, param := p, body, paramShape := .unknown}
  else
    let tupleParam <- fresh "args"
    -- Both single-arg (packed with unit) and multi-arg (nested pair)
    -- present as a pair at function entry.
    setShape tupleParam .pair
    let ρ := params.foldl (fun acc p => acc.insert p p) ρ
    let loweredCore <- lowerFCore core ρ ctors
    let body := destructArgsPrelude tupleParam params loweredCore
    setArity fid params.size
    return {fid, param := tupleParam, body, paramShape := .pair}

partial def lowerNonRecFun
  (fid : Name) (params : Array String) (core : FExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (fnTy : MLType := .TVar $ .named "?")
  : M σ LFun := do
  setShape fid (.ctor "𝐂" 2)
  recordParamShapes params (peelArgTys fnTy)
  if params.size = 0 then
    let p <- fresh "arg"
    setShape p .unknown
    let body <- lowerFCore core (ρ.insert p p) ctors
    setArity fid 0
    return {fid, param := p, body, paramShape := .unknown}
  else
    let tupleParam <- fresh "args"
    setShape tupleParam .pair
    let ρ := params.foldl (fun acc p => acc.insert p p) ρ
    let loweredCore <- lowerFCore core ρ ctors
    let body := destructArgsPrelude tupleParam params loweredCore
    setArity fid params.size
    return {fid, param := tupleParam, body, paramShape := .pair}

partial def lowerNonRecBinds
  (defs : Subarray (String × FExpr)) (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Env -> M σ LExpr) : M σ LExpr :=
  if h : defs.size = 0 then k ρ
  else
    let (x, e) := defs[0]
    lowerF e ρ ctors fun v => copyArity v x *> copyShape v x *>
      .letVal x (.var v) <$> lowerNonRecBinds defs[1:] (ρ.insert x x) ctors k

partial def lowerDT
  (cols : Array Sel)
  (roots : Array Name)
  (dt : DTree)
  (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (exhaustive : Bool)
  (k : Name -> M σ LExpr)
  (onFail : LExpr) : M σ LExpr :=
  match dt with
  | .fail => return onFail
  | .leaf row => bindPatBinds roots row.binds.toSubarray ρ (lowerF row.rhs · ctors k)
  | .splitProd j next =>
    let s := cols[j]!
    let cols := cols.replaceAt j #[.field s 0, .field s 1]
    lowerDT cols roots next ρ ctors exhaustive k onFail
  | .testConst j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM fun (tc, sub) => do
        let br <- lowerDT (cols.eraseIdx! j) roots sub ρ ctors exhaustive k onFail
        pure (constOnly tc, br)
      let defIR <- match d? with
                   | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ ctors exhaustive k onFail
                   | none => pure (if exhaustive then none else some onFail)
      return .seq #[] $ .switchConst sv caseIRs defIR
  | .testCtor j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM fun (cname, ar, sub) =>
        let cols := cols.replaceAt j $ .ofFn $ Sel.field cols[j]! ∘ @Fin.toNat ar
        (cname, ar, ·) <$> lowerDT cols roots sub ρ ctors exhaustive k onFail
      let defIR <- match d? with
                   | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ ctors exhaustive k onFail
                   | none => pure (if exhaustive then none else some onFail)
      return .seq #[] $ .switchCtor sv caseIRs defIR

partial def lowerMatchDT
  (scrs : Array Name)
  (rows : Array (Array Pattern × FExpr))
  (exhaustive : Bool)
  (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr := do
  let cols := Array.ofFn $ Sel.base ∘ @Fin.toNat scrs.size
  let rstates := rows.map fun (pats, rhs) => {pats, rhs}
  let dt := buildTree cols rstates
  lowerDT cols scrs dt ρ ctors exhaustive k
  $ .seq #[]
  $ .matchFail
  $ scrs
end

mutual
partial def lowerModule (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) : M σ (LModule × LModule) := do
  let rec build (i : Nat) (ρ : Env) (last? : Option Name) (ctors : Std.HashMap String Nat) : M σ LExpr := do
    if h : i < decls.size then
      match decls[i] with
      | .idBind binds =>
        let binds := binds.filter $ not ∘ (·.startsWith "(") ∘ Prod.fst
        let (recs, nonrecs) := splitLetGroup binds
        lowerNonRecBinds nonrecs.toSubarray ρ ctors fun ρ => do
          if h : recs.size = 0 then
            build (i + 1) ρ (if h : nonrecs.size = 0 then last? else some $ nonrecs.back.1) ctors
          else
            let funIRs <- recs.mapM fun (fid, selfN, ps, core) =>
              let (ps, core) := etaExpandParams ps core
              lowerRecFun fid selfN ps core ρ ctors
            let ρ := recs.foldl (fun acc (fid, _, _, _) => acc.insert fid fid) ρ
            .letRec funIRs <$> build (i + 1) ρ (some recs.back.1) ctors
      | .patBind (pat, _, e) =>
        lowerF e ρ ctors fun scr => do
          let onOk ρ := build (i + 1) ρ last? ctors
          let onFail := pure $ .seq #[] $ .matchFail #["Toplevel"]
          lowerTopPatBind scr pat ρ onOk onFail
    else
      match ρ["main"]? <|> last? with
      | some v => return .seq #[] $ .ret v
      | none =>
        let u <- fresh "u"
        return .letVal u (.cst .unit) $ .seq #[] $ .ret u

  let fid := "main"
  let param := "arg"
  let body <- optimizeLam <$> build 0 ∅ none ctors
  -- main has a single dummy `arg` parameter (entry point); unknown shape
  setShape param .unknown
  let main : LFun := {fid, param, body, paramShape := .unknown}
  let shapes <- getShapeMap
  let mod : LModule := {funs := #[], main, shapes}
  let modCC := runST fun _ => (IR.closureConvert mod).run' (1000, ∅, mod.shapes)
  return (mod, modCC)

partial def lowerTopPatBind
  (scr : Name)
  (pat : Pattern)
  (ρ   : Env)
  (onOk : Env -> M σ LExpr)
  (onFail : M σ LExpr)
  : M σ LExpr :=
  let roots := #[scr]
  let binds := collectTopPatBinds pat (.base 0)

  let rec bindAll i ρ k :=
    if h : i < binds.size then
      let (x, sel) := binds[i]
      realizeSel roots sel fun v =>
        .letVal x (.var v) <$> bindAll (i + 1) (ρ.insert x x) k
    else k ρ
  let rec go
    | [] => bindAll 0 ρ onOk
    | (sel, p) :: rest =>
      match p with
      | .PWild | .PVar _ => go rest
      | .PConst tc =>
        realizeSel roots sel fun sv => do
          let (ck, op) := constOf tc
          let c <- fresh "c"
          let cmp <- fresh "cmp"
          let t <- go rest
          let e <- onFail
          return .letVal c (.cst ck)
               $ .letRhs cmp (.prim op #[sv, c])
               $ .seq #[] (.cond cmp t e)
      | .PProd' p q =>
        go $ (Sel.field sel 0, p) :: (Sel.field sel 1, q) :: rest
      | .PCtor cname args =>
        realizeSel roots sel fun sv => do
          let flag <- fresh "is"
          let ar := args.size
          let t <- go $ args.size.foldRev (init := rest) fun i _ acc =>
            (Sel.field sel i, args[i]) :: acc
          let e <- onFail
          return .letRhs flag (.isConstr sv cname ar)
               $ .seq #[] (.cond flag t e)
  go [(Sel.base 0, pat)]
end

end IRf

namespace IR
open IRf
@[inline] def toLamModuleF (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) : (LModule × LModule) :=
  let decls := decls.map fun
    | .idBind b => .idBind $ b.map fun (id, sch, fe) => (id, sch, HelperF.stripTy fe)
    | .patBind (pat, sch, fe) => .patBind (pat, sch, HelperF.stripTy fe)
  runST fun _ => lowerModule decls ctors |>.run' (0, ∅, ∅)

@[inline] def toLamF (ctors : Std.HashMap String Nat) (e : FExpr) : LExpr :=
  runST fun _ => lowerFCore e (ctors := ctors) ∅ |>.run' (0, ∅, ∅)

@[inline] def toLamFO (ctors : Std.HashMap String Nat) (e : FExpr) : LExpr :=
  optimizeLam (toLamF ctors e)

namespace Incremental
structure LoweringState where
  gensym : Nat
  env    : Env
  ctors  : Std.HashMap String Nat
  arity  : Std.HashMap String Nat
  shapes : ShapeMap
deriving Inhabited

@[inline] def withTyDecl (st : LoweringState) (ctors : Std.HashMap String Nat) : LoweringState :=
  {st with ctors := st.ctors ∪ ctors}

def lowerIdBind (st : LoweringState) (binds : Array BindingF) : LoweringState × Array LFun :=
  let binds := binds.map fun (id, sch, fe) => (id, sch, HelperF.stripTy fe)
  let (recs, nonrecs) := HelperF.splitLetGroup binds
  let env :=
    recs.foldl (fun ρ (fid, _, _, _) => ρ.insert fid fid)
    $ nonrecs.foldl (fun ρ (x, _) => ρ.insert x x) st.env
  let (funs, (gensym, arity, shapes)) :=
    runST fun _ => (do
      let recs <- recs.mapM fun (fid, selfN, ps, core) => do
        let (ps, core) := HelperF.etaExpandParams ps core
        lowerRecFun fid selfN ps core env st.ctors
      let nonrecs <- nonrecs.foldlM (init := #[]) fun (acc : Array LFun) (x, rhs) => do
        match h : rhs with
        | FExpr.Fun .. =>
          let (p0, rest, core) := HelperF.decomposeLamChain rhs h
          let base := #[p0] ++ rest
          let (allParams, core) := HelperF.etaExpandParams base core
          let f <- lowerNonRecFun x allParams core env st.ctors rhs.getTy
          pure (acc.push f)
        | _ => pure acc
      pure $ recs ++ nonrecs).run (st.gensym, st.arity, st.shapes)
  ({st with gensym, env, arity, shapes}, funs)

def lower1 (st : LoweringState) (e : FExpr) : LoweringState × LExpr :=
  let (le, (gensym, arity, shapes)) :=
    runST fun _ => lowerFCore e st.env st.ctors |>.run (st.gensym, st.arity, st.shapes)
  ({st with gensym, arity, shapes}, le)

end Incremental
end IR
