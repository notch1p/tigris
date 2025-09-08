import Tigris.core.lam
import Tigris.core.opt
import Tigris.core.lift
import Tigris.interpreter.entrypoint
import Tigris.oldcore.matchApp
import PP
@[inline] def Array.replaceAt (xs : Array α) (i : Nat) (elems : Array α) : Array α :=
  xs[0:i] ++ elems ++ xs[i+1:]

namespace IR variable {σ}

@[inline] def fresh (h := "x") : M σ Name :=
  modifyGet fun n => (h ++ toString n, n + 1)
namespace Helper
def constOf : TConst -> Const × PrimOp
  | .PUnit     => (.unit  , .eqInt)
  | .PInt i    => (.int i , .eqInt)
  | .PBool b   => (.bool b, .eqBool)
  | .PStr s    => (.str s , .eqStr)
@[inline] def constOnly := Prod.fst ∘ constOf

def primOfName (s : String) (t₁ t₂ : MLType) : Option PrimOp :=
  match s, t₁, t₂ with
  | "add", _, _   => some .add
  | "sub", _, _   => some .sub
  | "mul", _, _   => some .mul
  | "div", _, _   => some .div
  | "eq" , .TCon "Int", .TCon "Int"
                  => some .eqInt
  | "eq" , .TCon "Bool", .TCon "Bool"
                  => some .eqBool
  | "eq" , .TCon "String", .TCon "String"
                  => some .eqStr
  | _, _, _       => none

def matchBinaryPrim : TExpr -> Option (PrimOp × TExpr × TExpr)
  | .App (.App (.Var f _) x t₁) y t₂ => (·, x, y) <$> primOfName f t₁ t₂
  | _ => none

def decomposeLamChain : TExpr -> Option (String × Array String × TExpr)
  | .Fun p _ b _ =>
    let rec collect (e : TExpr) (acc : Array String) : (Array String × TExpr) :=
      match e with
      | .Fun q _ b' _ => collect b' (acc.push q)
      | other     => (acc, other)
    let (ps, core) := collect b #[]
    some (p, ps, core)
  | _ => none

def decomposeApp : TExpr -> (TExpr × Array TExpr)
  | .App f a _ =>
    let (h, as) := decomposeApp f
    (h, as.push a)
  | e => (e, #[])

def matchCtorApp (ctorArity : Std.HashMap String Nat) (e : TExpr)
  : Option (String × Array TExpr × Nat) :=
  let (h, args) := decomposeApp e
  match h with
  | .Var cname _ =>
    match ctorArity.get? cname with
    | some ar => some (cname, args, ar)
    | none    => none
  | _ => none

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
    as.size.fold (init := #[]) fun i _ acc =>
      acc ++ go as[i] (.field sel i)

def splitLetGroup
  (xs : Array (Name × Scheme × TExpr))
  -- recs                                      nonrecs
  : (Array (Name × Name × Array Name × TExpr) × Array (Name × TExpr)) :=
  xs.foldl
    (init := (#[], #[]))
    fun (recs, nonrecs) (x, _, e) =>
      match e with
      | .Fix lam _ | .Fixcomb lam _ =>
        match Helper.decomposeLamChain lam with
        | some (selfN, params, core) => (recs.push (x, selfN, params, core), nonrecs)
        | none => (recs, nonrecs.push (x, e))
      | _ => (recs, nonrecs.push (x, e))

end Helper

open Function (uncurry) in
open Helper in
mutual
partial def lowerNonRecBinds
  (defs : Subarray (String × TExpr)) (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Env -> M σ LExpr) : M σ LExpr := do
  if h : defs.size = 0 then
    k ρ
  else
    let (x, e) := defs[0]
    lowerE e ρ ctors fun v =>
      (.letVal x (.var v) ·) <$> lowerNonRecBinds defs[1:] (ρ.insert x x) ctors k

partial def lowerCtorApp
  (cname : String) (args : Array TExpr) (arity : Nat)
  (ρ : Env) (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr := do
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
    lowerE
      (args.foldl (init := TExpr.Var cname (MLType.TVar ⟨"?"⟩))
      (fun f a => TExpr.App f a (MLType.TVar ⟨"?"⟩)))
      ρ ctors k

partial def lowerE
  (e : TExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat) (k : Name -> M σ LExpr) : M σ LExpr := do
  -- binary prim sugar first
  match matchBinaryPrim e with
  | some (op, x, y) =>
    lowerE x ρ ctors fun vx =>
      lowerE y ρ ctors fun vy => do
        let r <- fresh "p"
        let cont <- k r
        return .letRhs r (.prim op #[vx, vy]) cont
  | none =>
    -- constructor-headed application?
    match matchCtorApp ctors e with
    | some (cname, args, ar) =>
      if ar == 0 && args.isEmpty then
        -- nullary ctor as value
        let r <- fresh "con"
        let cont <- k r
        pure (.letRhs r (.mkConstr cname #[]) cont)
      else
        lowerCtorApp cname args ar ρ ctors k
    | none =>
      match e with
      | .Ascribe e _ => lowerE e ρ ctors k

      | .Var x _ =>
        -- treat nullary ctor mentioned as a variable as value
        match ctors.get? x with
        | some 0 =>
          let r <- fresh "con"
          let cont <- k r
          pure (.letRhs r (.mkConstr x #[]) cont)
        | _ => k (ρ.getD x x)

      | .CI i _ =>
        let v <- fresh "c"
        let body <- k v
        return .letVal v (.cst (.int i)) body
      | .CB b _ =>
        let v <- fresh "c"
        let body <- k v
        return .letVal v (.cst (.bool b)) body
      | .CS s _ =>
        let v <- fresh "c"
        let body <- k v
        return .letVal v (.cst (.str s)) body
      | .CUnit _ =>
        let v <- fresh "c"
        let body <- k v
        return .letVal v (.cst .unit) body

      | .Prod' l r _ =>
        lowerE l ρ ctors fun lv =>
          lowerE r ρ ctors fun rv => do
            let p <- fresh "p"
            let body <- k p
            return .letRhs p (.mkPair lv rv) body

      | .Fun a _ body _ =>
        let lb <- lower body (ρ.insert a a) ctors
        let f <- fresh "lam"
        let kbody <- k f
        return .letVal f (.lam a lb) kbody

      | .App f a _ =>
        lowerE f ρ ctors fun vf =>
          lowerE a ρ ctors fun va => do
            let r <- fresh "call"
            let body <- k r
            return .letRhs r (.call vf va) body

      | .Cond c t e' _ =>
        lowerE c ρ ctors fun cv => do
          .seq #[] <$>
            ((.cond cv · ·) <$> lower t ρ ctors <*> lower e' ρ ctors)

      | .Let bs body _ =>
        let (recFuns, nonrecs) := splitLetGroup bs
        lowerNonRecBinds nonrecs.toSubarray ρ ctors fun ρ' => do
          if recFuns.isEmpty then
            lower body ρ' ctors
          else
            -- build all recursive functions in one letRec
            let funs <- recFuns.mapM fun (fid, selfN, params, core) =>
              lowerRecFun fid selfN params core ρ' ctors
            let ρ'' := recFuns.foldl (init := ρ') fun acc (fid, _, _, _) => acc.insert fid fid
            let body' <- lower body ρ'' ctors
            return .letRec funs body'

      | .Fix lam _ | .Fixcomb lam _ =>
        match decomposeLamChain lam with
        | some (selfN, params, core) => do
          let fname <- fresh "f"
          let funIR <- lowerRecFun fname selfN params core ρ ctors
          let r <- fresh "r"
          let cont <- k r
          return .letRec #[⟨fname, funIR.param, funIR.body⟩]
                 (.letVal r (.var fname) cont)
        | none => lowerE lam ρ ctors k

      | .Match scrs rows _ ex _ =>
        lowerMany scrs ρ ctors fun svars =>
          lowerMatchDT svars rows ex.isNone ρ ctors k

@[inline] partial def lower (e : TExpr) (ρ : Env := ∅) (ctors : Std.HashMap String Nat := ∅) : M σ LExpr :=
  lowerE e ρ ctors $ pure ∘ .seq #[] ∘ .ret

partial def lowerMany
  (es : Array TExpr)
  (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (k : Array Name -> M σ LExpr) : M σ LExpr := go 0 #[] where
  go i acc : M σ LExpr :=
    if h : i < es.size then
      lowerE es[i] ρ ctors $ go i.succ ∘ acc.push
    else k acc

partial def lowerRecFun
  (fid : Name) (selfN : String) (params : Array String) (core : TExpr) (ρ : Env)
  (ctors : Std.HashMap String Nat)
  : M σ LFun := do
  let ρ₀ := ρ.insert selfN fid
  let (p₀, rest) <- show M σ (Name × Subarray Name) from
    if h : params.size = 0 then do
      (·, ∅) <$> fresh "arg"
    else return (params[0], params[1:])

  let rec build (i : Nat) (ρᵢ : Env) : M σ LExpr := do
    if h : i < rest.size then
      let p := rest[i]
      let inner <- build i.succ (ρᵢ.insert p p)
      let v <- fresh "lam"
      return .letVal v (.lam p inner) (.seq #[] (.ret v))
    else lower core ρᵢ ctors

  let ρ₁ := ρ₀.insert p₀ p₀
  let body <- build 0 ρ₁
  return ⟨fid, p₀, body⟩

partial def bindPatBinds
  (roots : Array Name)
  (bs : Array (String × Sel))
  (ρ : Env)
  (k : Env -> M σ LExpr) : M σ LExpr :=
  if bs.isEmpty then k ρ
  else
    let (x, sel) := bs[0]!
    realizeSel roots sel fun v => do
      (.letVal x (.var v) ·) <$> bindPatBinds roots bs[1:] (ρ.insert x x) k

partial def lowerDT
  (cols : Array Sel)
  (roots : Array Name)
  (dt : DTree)
  (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (exhaustive : Bool)
  (k : Name -> M σ LExpr)
  (onFail : LExpr) : M σ LExpr := do
  match dt with
  | .fail => return onFail
  | .leaf row =>
    bindPatBinds roots row.binds ρ (lowerE row.rhs · ctors k)
  | .splitProd j next =>
    let s := cols[j]!
    let cols' := cols.replaceAt j #[.field s 0, .field s 1]
    lowerDT cols' roots next ρ ctors exhaustive k onFail
  | .testConst j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM (fun (tc, sub) => do
        let br <- lowerDT (cols.eraseIdx! j) roots sub ρ ctors exhaustive k onFail
        pure (constOnly tc, br))
      let defIR? <- match d? with
                    | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ ctors exhaustive k onFail
                    | none   => pure (if exhaustive then none else some onFail)
      pure (.seq #[] (.switchConst sv caseIRs defIR?))
  | .testCtor j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM fun (cname, ar, sub) => do
        let cols' := cols.replaceAt j $ .ofFn $ Sel.field cols[j]! ∘ @Fin.toNat ar
        let br <- lowerDT cols' roots sub ρ ctors exhaustive k onFail
        pure (cname, ar, br)
      let defIR? <- match d? with
                    | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ ctors exhaustive k onFail
                    | none   => pure (if exhaustive then none else some onFail)
      pure (.seq #[] (.switchCtor sv caseIRs defIR?))

partial def lowerMatchDT
  (scrs : Array Name)
  (rows : Array (Array Pattern × TExpr))
  (exhaustive : Bool)
  (ρ : Env)
  (ctors : Std.HashMap String Nat)
  (k : Name -> M σ LExpr) : M σ LExpr := do
  let u <- fresh "u"
  let kont <- k u
  let fallback : LExpr := .letVal u (.cst .unit) kont
  let cols := Array.ofFn (Sel.base ∘ @Fin.toNat scrs.size)
  let rstates := rows.map fun (pats, rhs) => {pats, rhs}
  let dt := buildTree cols rstates
  lowerDT cols scrs dt ρ ctors exhaustive (fun x => pure (.seq #[] (.ret x))) fallback

end
open Helper in
mutual

partial def lowerTopPatBind
  (scr : Name)
  (pat : Pattern)
  (ρ   : Env)
  (onOk : Env -> M σ LExpr)
  (onFail : M σ LExpr)
  : M σ LExpr :=

  let roots := #[scr]
  let binds := collectTopPatBinds pat (.base 0)

  let rec bindAll (i : Nat) (ρ' : Env) (k : Env -> M σ LExpr) : M σ LExpr := do
    if h : i < binds.size then
      let (x, sel) := binds[i]
      realizeSel roots sel fun v =>
        .letVal x (.var v) <$> bindAll (i+1) (ρ'.insert x x) k
    else k ρ'

  let rec go (work : List (Sel × Pattern)) : M σ LExpr := do
    match work with
    | [] => bindAll 0 ρ onOk
    | (sel, p) :: rest =>
      match p with
      | .PWild | .PVar _ => go rest
      | .PConst tc =>
        realizeSel roots sel fun sv => do
          let (ck, op) := constOf tc
          let c <- fresh "c"
          let cmp <- fresh "cmp"
          let tBranch <- go rest
          let eBranch <- onFail
          return .letVal c (.cst ck) $
                 .letRhs cmp (.prim op #[sv, c]) $
                 .seq #[] (.cond cmp tBranch eBranch)
      | .PProd' p q =>
        go $ (Sel.field sel 0, p) :: (Sel.field sel 1, q) :: rest
      | .PCtor cname args =>
        realizeSel roots sel fun sv => do
          let flag <- fresh "is"
          let ar := args.size
          let tBranch <- go $
            args.size.foldRev (init := rest)
              fun i _ acc => (Sel.field sel i, args[i]) :: acc
          let eBranch <- onFail
          return .letRhs flag (.isConstr sv cname ar) $
                 .seq #[] (.cond flag tBranch eBranch)

  go [(Sel.base 0, pat)]

partial def lowerModule (decls : Array TopDeclT) : M σ (LModule × LModule) := do
  let rec build (i : Nat) (ρ : Env) (last? : Option Name) (ctors : Std.HashMap String Nat) : M σ LExpr := do
    if h : i < decls.size then
      match decls[i] with
      | .tyBind td =>
        -- extend ctor arities
        let ctors' := td.ctors.foldl (init := ctors) fun m (cname, _, ar) => m.insert cname ar
        build (i + 1) ρ last? ctors'

      | .idBind binds =>
        -- filter out operator-like names
        let binds := binds.filter $ not ∘ (·.startsWith "(") ∘ Prod.fst
        let (recFuns, nonrecs) := splitLetGroup binds
        lowerNonRecBinds nonrecs.toSubarray ρ ctors fun ρ' => do
          if h : recFuns.size = 0 then
            build (i + 1) ρ' (if h : nonrecs.size = 0 then last? else some nonrecs.back.1) ctors
          else
            -- Build all rec functions together
            let funIRs <- recFuns.mapM fun (fid, selfN, ps, core) =>
              lowerRecFun fid selfN ps core ρ' ctors
            let ρ'' := recFuns.foldl (init := ρ') fun acc (fid, _, _, _) => acc.insert fid fid
            let next <- build (i + 1) ρ'' (some recFuns.back.1) ctors
            return (.letRec funIRs next)

      | .patBind (pat, e) =>
        lowerE e ρ ctors fun scr => do
          let onOk (ρ' : Env) := build (i + 1) ρ' last? ctors
          let onFail := do
            let u <- fresh "u"
            pure (.letVal u (.cst .unit) (.seq #[] (.ret u)))
          lowerTopPatBind scr pat ρ onOk onFail
    else
      match ρ.get? "main" <|> last? with
      | some v => pure (.seq #[] (.ret v))
      | none   =>
        let u <- fresh "u"
        pure (.letVal u (.cst .unit) (.seq #[] (.ret u)))

  -- Create main function
  let fid := "main"
  let param := "arg"
  let body <- optimizeLam <$> build 0 ∅ none ∅
  let main : LFun := {fid, param, body}
  let mod := ⟨#[], main⟩
  return Prod.mk mod (runST fun _ => (IR.closureConvert mod).run' 1000)

end

def toLamModuleT decls := runST fun _ => IR.lowerModule decls |>.run' 0
def toLamT s e := runST fun _ => lower e (ctors := s) |>.run' 0
def toLamTO s e := optimizeLam (toLamT s e)
def dumpLamModuleT decls := toLamModuleT decls |>.map fmtModule fmtModule
def toLamModuleT1 s e :=
  letI e := optimizeLam $ runST fun _ => lower e (ctors := s) |>.run' 0
  runST fun _ => closureConvert ⟨#[], "main", "arg", e⟩ |>.run' 0
attribute [inline] toLamModuleT toLamT toLamTO dumpLamModuleT toLamModuleT1

