import Tigris.core.lift
import Tigris.typing.fexpr
import Tigris.core.matchAppF
import PP

namespace IRf open IR MLType open FExpr open SysF.Helper (pvs) open Helper

private abbrev Env := IR.Env

variable {σ}

namespace HelperF

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

def arrArity : MLType -> Nat
  | .TSch (.Forall _ _ t) => arrArity t
  | .TArr _ b => 1 + arrArity b
  | _         => 0
def getArrArity : FExpr -> Nat := arrArity ∘ FExpr.getTy

def isDictArg : FExpr -> Bool
  | .Var x _ => x.startsWith "d_" || x.startsWith "rd_"
  | _ => false
  
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

def predToApp : Pred -> MLType := fun {cls, args} => TApp cls args
def unwrapTSch : MLType -> MLType
  | TSch (.Forall _ _ps t) => /-ps.foldr (TArr ∘ predToApp)-/ t
  | t => t

partial def stripTy : FExpr -> FExpr
  | TyApp f _ | TyLam _ f => stripTy f
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
    let (argTys, _) := decomposeArr' vTy
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

/-- Dictionary-aware + partial-application aware application:
  1. Split args into dict prefix (vars named d_* or rd_*) and user args (the rest).
  2. Apply all dict args one-by-one (each as unary payload ⟨arg, ()⟩).
  3. Let n = getArrArity(head) (user-argument arity; types carry user args only here).
    - If userArgs.size = 0: return the function after dicts (a closure expecting n args).
    - If userArgs.size < n: produce an uncurried closure expecting the remaining (n - size) args.
    - If userArgs.size = n: make one uncurried call packing all user args.
    - If userArgs.size > n: call with the first n args, then apply the rest to the result.

  - Not exactly a clean solution because the name-based assumption about dict args falls apart
    if there's a name clash.
-/
partial def lowerFunApp
  (head : FExpr) (args : Array FExpr)
  (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr :=
  let n := getArrArity head
  let (dictArgs, userArgs) := args.partition isDictArg

  -- apply a single unary argument `aName` to callee `vfName`
  let applyUnary (vfName aName : Name) (cont : Name -> M σ LExpr) : M σ LExpr := do
    let u <- fresh "u"
    let pair <- fresh "pair"
    let r <- fresh "call"
    let body <- cont r
    pure
    $ .letVal u (.cst .unit)
    $ .letRhs pair (.mkPair aName u)
    $ .letRhs r (.call vfName pair) body

  -- apply a function value `fv` to a list of user-arg names in one shot
  let callWithMany (fv : Name) (ns : Array Name) : M σ LExpr := do
    if ns.isEmpty then k fv
    else if h : ns.size = 1 then
      applyUnary fv ns[0] k
    else
      buildPairs (name := ns.toList) fun tuple => do
        let r0 <- fresh "r"
        .letRhs r0 (.call fv tuple) <$> k r0

  -- generate an uncurried closure expecting `missing` user args, pre-supplying `supplied`
  let mkPartial (fv : Name) (supplied : Array Name) (missing : Nat) : M σ LExpr := do
    let lamV <- do
      if missing = 1 then
        let p <- fresh "arg"
        let res <- fresh "r"
        let allArgs := supplied.push p
        let body <- buildPairs (name := allArgs.toList) fun tuple =>
          pure $ .letRhs res (.call fv tuple) (.seq #[] (.ret res))
        pure (.lam p body)
      else
        let param <- fresh "rest"
        let restNames : Array Name <- (missing - 1).foldM (init := #[]) fun _ _ acc =>
          acc.push <$> fresh
        let allArgs := supplied ++ restNames.push param
        let res <- fresh "r"
        let callCore <- buildPairs (name := allArgs.toList) fun tuple =>
          pure $ .letRhs res (.call fv tuple) (.seq #[] (.ret res))
        let lamBody := destructTuple param restNames 0 callCore
        pure (.lam param lamBody)
    let out <- fresh "clos"
    let cont <- k out
    pure (.letVal out lamV cont)

  -- after dicts applied, handle user args with arity-aware staging
  let applyUsers (fv : Name) : M σ LExpr :=
    if userArgs.isEmpty then k fv
    else
      lowerMany userArgs ρ ctors fun ns => do
        if n = 0 then callWithMany fv ns
        else if ns.size < n then mkPartial fv ns (n - ns.size)
        else if ns.size = n then callWithMany fv ns
        else
          let now := ns.extract 0 n
          let rest := ns.extract n ns.size
          buildPairs (name := now.toList) fun tuple => do
            let r0 <- fresh "r"
            let after <-
              if rest.size = 0 then k r0
              else if rest.size = 1 then applyUnary r0 rest[0]! k
              else
                buildPairs (name := rest.toList) fun tuple2 => do
                  let r1 <- fresh "r"
                  .letRhs r1 (.call r0 tuple2) <$> k r1
            pure (.letRhs r0 (.call fv tuple) after)

  lowerF head ρ ctors fun vf0 =>
    let rec applyDicts (i : Nat) (vf : Name) : M σ LExpr := do
      if h : i < dictArgs.size then
        lowerF dictArgs[i] ρ ctors fun a =>
          applyUnary vf a (applyDicts (i + 1))
      else
        applyUsers vf
    applyDicts 0 vf0

partial def lowerF
  (e : FExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr := do
  match matchBinaryPrim e with
  | some (op, x, y) =>
    lowerF x ρ ctors fun vx =>
      lowerF y ρ ctors fun vy => do
        let r <- fresh "p"
        let cont <- k r
        return .letRhs r (.prim op #[vx, vy]) cont
  | none =>
    match matchCtorApp ctors e with
    | some (cname, args, ar) =>
      if ar == 0 && args.isEmpty then
        let r <- fresh "con"
        let cont <- k r
        return (.letRhs r (.mkConstr cname #[]) cont)
      else lowerCtorApp cname args ar ρ ctors k
    | none =>
      match h : e with
      | .TyLam _ t | .TyApp t _ => lowerF t ρ ctors k

      | .Var x _ =>
        match ctors[x]? with
        | some 0 => let r <- fresh "con"; let cont <- k r; return (.letRhs r (.mkConstr x #[]) cont)
        | _ => k (ρ.getD x x)
      
      | .CI i _ => let v <- fresh "c" let body <- k v return .letVal v (.cst (.int i)) body
      | .CB i _ => let v <- fresh "c" let body <- k v return .letVal v (.cst (.bool i)) body
      | .CS i _ => let v <- fresh "c" let body <- k v return .letVal v (.cst (.str i)) body
      | .CUnit _ => let v <- fresh "c" let body <- k v return .letVal v (.cst .unit) body

      | .Prod' l r _ =>
        lowerF l ρ ctors fun lv =>
          lowerF r ρ ctors fun rv => do
            let p <- fresh "p"
            let body <- k p
            return .letRhs p (.mkPair lv rv) body
      
      | .Proj src _ idx _ =>
        lowerF src ρ ctors fun sv => do
          let p <- fresh "p"
          let body <- k p
          return .letRhs p (.proj sv idx) body
      
      | .Fun .. =>
        let (p0, rest, core) := decomposeLamChain e h
        let tupleParam <- fresh "args"
        let baseParams := #[p0] ++ rest
        let (allParams, core) := etaExpandParams baseParams core
        let ρ := allParams.foldl (fun acc p => acc.insert p p) ρ
        let loweredCore <- lowerFCore core ρ ctors
        let body := destructArgsPrelude tupleParam allParams loweredCore
        let f <- fresh "lam"
        let kbody <- k f
        return .letVal f (.lam tupleParam body) kbody

      | .App .. =>
        let (h, args) := decomposeApp e
        lowerFunApp h args ρ ctors k
      | .Cond c t e _ =>
        lowerF c ρ ctors fun cv =>
          .seq #[] <$> ((.cond cv · ·) <$> lowerFCore t ρ ctors <*> lowerFCore e ρ ctors)
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
      | .Fix lam@(.Fun ..) _ => do
        let (selfN, params, core) := decomposeLamChain lam ‹_›
        let (params, core) := etaExpandParams params core
        let fname <- fresh "f"
        let funIR <- lowerRecFun fname selfN params core ρ ctors
        let r <- fresh "r"
        let cont <- k r
        return .letRec #[⟨fname, funIR.param, funIR.body⟩] (.letVal r (.var fname) cont)
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
      let cont <- k r
      pure (.letRhs r (.mkConstr cname names) cont)
  else if args.size < arity then
    lowerMany args ρ ctors fun supplied => do
      let missing := arity - args.size
      let rec buildLam (i : Nat) (captured : Array Name) : M σ Value := do
        let p <- fresh "arg"
        if i + 1 < missing then
          let inner <- buildLam (i+1) (captured.push p)
          let v <- fresh "lam"
          let body := .letVal v inner (.seq #[] (.ret v))
          pure (.lam p body)
        else
          let res <- fresh "r"
          let fields := supplied ++ captured.push p
          let body := .letRhs res (.mkConstr cname fields) (.seq #[] (.ret res))
          pure (.lam p body)
      let lamV <- buildLam 0 #[]
      let out <- fresh "clos"
      let cont <- k out
      pure (.letVal out lamV cont)
  else -- should get blocked by typechecker, unreachable
    lowerF
      (args.foldl (init := FExpr.Var cname (MLType.TVar ⟨"?"⟩))
      (fun f a => FExpr.App f a (MLType.TVar ⟨"?"⟩)))
      ρ ctors k

partial def lowerRecFun
  (fid : Name) (selfN : String) (params : Array String) (core : FExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  : M σ LFun := do
  let ρ := ρ.insert selfN fid
  if params.size = 0 then
    let p <- fresh "arg"
    let body <- lowerFCore core (ρ.insert p p) ctors
    return ⟨fid, p, body⟩
  else
    let tupleParam <- fresh "args"
    let ρ := params.foldl (fun acc p => acc.insert p p) ρ
    let loweredCore <- lowerFCore core ρ ctors
    let body := destructArgsPrelude tupleParam params loweredCore
    return ⟨fid, tupleParam, body⟩

partial def lowerNonRecBinds
  (defs : Subarray (String × FExpr)) (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Env -> M σ LExpr) : M σ LExpr :=
  if h : defs.size = 0 then k ρ
  else
    let (x, e) := defs[0]
    lowerF e ρ ctors fun v =>
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
  let u <- fresh "u"
  let kont <- k u
  let fallback : LExpr := .letVal u (.cst .unit) kont
  let cols := Array.ofFn $ Sel.base ∘ @Fin.toNat scrs.size
  let rstates := rows.map fun (pats, rhs) => {pats, rhs}
  let dt := buildTree cols rstates
  lowerDT cols scrs dt ρ ctors exhaustive (pure ∘ .seq #[] ∘ .ret) fallback
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
      | .patBind (pat, e) =>
        lowerF e ρ ctors fun scr => do
          let onOk ρ := build (i + 1) ρ last? ctors
          let onFail := do
            let u <- fresh "u"
            return .letVal u (.cst .unit) $ .seq #[] $ .ret u
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
  let main : LFun := {fid, param, body}
  let mod := ⟨#[], main⟩
  let modCC := runST fun _ => (IR.closureConvert mod).run' 1000
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
    | .patBind (pat, fe) => .patBind (pat, HelperF.stripTy fe)
  runST fun _ => lowerModule decls ctors |>.run' 0

@[inline] def toLamF (ctors : Std.HashMap String Nat) (e : FExpr) : LExpr :=
  runST fun _ => lowerFCore e (ctors := ctors) ∅ |>.run' 0

@[inline] def toLamFO (ctors : Std.HashMap String Nat) (e : FExpr) : LExpr :=
  optimizeLam (toLamF ctors e)
end IR
