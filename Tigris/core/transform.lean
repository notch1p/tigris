import Tigris.core.lam
import Tigris.core.opt
import Tigris.core.lift
import Tigris.interpreter.entrypoint
import Tigris.oldcore.matchApp
import Tigris.typing.exhaust
import PP
open PrettyPrint.Text (mkBoldBlackWhite)
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

def primOfName (s : String) : Option PrimOp :=
  match s with
  | "add"   => some .add
  | "sub"   => some .sub
  | "mul"   => some .mul
  | "div"   => some .div
  | "eq"    => some .eqInt -- `eq` is polymorphic in the interpreter,
                           -- default to eqInt here for now.
--  | "eqInt" => some .eqInt
--  | "eqBool"=> some .eqBool
--  | "eqStr" => some .eqStr
  | _ => none

def matchBinaryPrim : Expr -> Option (PrimOp × Expr × Expr)
  | .App (.App (.Var f) x) y => (·, x, y) <$> primOfName f
  | _ => none

def decomposeLamChain : Expr -> Option (String × Array String × Expr)
  | .Fun p b =>
    let rec collect (e : Expr) (acc : Array String) : (Array String × Expr) :=
      match e with
      | .Fun q b' => collect b' (acc.push q)
      | other     => (acc, other)
    let (ps, core) := collect b #[]
    some (p, ps, core)
  | _ => none

def realizeSel (roots : Array Name) : Sel -> (Name -> M σ LExpr) -> M σ LExpr
  | .base i, k => k roots[i]!
  | .field s i, k => realizeSel roots s fun v => do
    let p <- fresh "p"
    let cont <- k p
    return .letRhs p (.proj v i) cont

abbrev TyLookup := String -> Option TyDecl

@[inline] def headFin (τ : MLType) : Option Exhaustive.FinDom :=
  Exhaustive.FinDom.headFinDom τ

@[inline] def allConsts (d : Exhaustive.FinDom) : List TConst :=
  Exhaustive.FinDom.constsOf d

def constCasesExhaustive (τ? : Option MLType) (present : Std.HashSet TConst) : Bool :=
  match τ? with
  | some τ =>
    match headFin τ with
    | some d =>
      allConsts d |>.all (fun k => present.contains k)
    | none => false
  | none => false

def ctorCasesExhaustive
  (lookup : TyLookup) (τ? : Option MLType) (present : Std.HashSet (String × Nat)) : Bool :=
  match τ? with
  | some τ =>
    match Exhaustive.headTyconArgs τ with
    | some (tycon, _) =>
      match lookup tycon with
      | some td => Exhaustive.completeData td present
      | none    => false
    | none => false
  | none => false

def refineTypesForCtor
  (lookup : TyLookup) (τ? : Option MLType) (cname : String) : Option (Array MLType) :=
  match τ? with
  | some τ =>
    match Exhaustive.headTyconArgs τ with
    | some (tycon, tyArgs) =>
      match lookup tycon with
      | some td =>
        match Exhaustive.ctorFieldTypes td cname tyArgs with
        | some fts => some fts.toArray
        | none     => none
      | none => none
    | none => none
  | none => none

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
  (xs : Array (Name × Expr))
  -- recs                                      nonrecs
  : (Array (Name × Name × Array Name × Expr) × Array (Name × Expr)) :=
  xs.foldl
    (init := (#[], #[]))
    fun (recs, nonrecs) (x, e) =>
      match e with
      | .Fix lam | .Fixcomb lam =>
        match Helper.decomposeLamChain lam with
        | some (selfN, params, core) => (recs.push (x, selfN, params, core), nonrecs)
        | none => (recs, nonrecs.push (x, e))
      | _ => (recs, nonrecs.push (x, e))

end Helper

open Function (uncurry) in
open Helper in
mutual
partial def lowerNonRecBinds
  (defs : Subarray (String × Expr)) (ρ : Env) (k : Env -> M σ LExpr) : M σ LExpr := do
  if h : defs.size = 0 then
    k ρ
  else
    let (x, e) := defs[0]
    lowerE e ρ fun v =>
      (.letVal x (.var v) ·) <$> lowerNonRecBinds defs[1:] (ρ.insert x x) k

partial def lowerE (e : Expr) (ρ : Env) (k : Name -> M σ LExpr) : M σ LExpr := do
  match matchBinaryPrim e with
  | some (op, x, y) =>
    lowerE x ρ fun vx =>
      lowerE y ρ fun vy => do
        let r <- fresh "p"
        let cont <- k r
        return .letRhs r (.prim op #[vx, vy]) cont
  | none =>
    match e with
    | .Ascribe e _ => lowerE e ρ k

    | .Var x =>
      k (ρ.getD x x)
    | .CI i =>
      let v <- fresh "c"
      let body <- k v
      return .letVal v (.cst (.int i)) body
    | .CB b =>
      let v <- fresh "c"
      let body <- k v
      return .letVal v (.cst (.bool b)) body
    | .CS s =>
      let v <- fresh "c"
      let body <- k v
      return .letVal v (.cst (.str s)) body
    | .CUnit =>
      let v <- fresh "c"
      let body <- k v
      return .letVal v (.cst .unit) body
    | .Prod' l r =>
      lowerE l ρ fun lv =>
        lowerE r ρ fun rv => do
          let p <- fresh "p"
          let body <- k p
          return .letRhs p (.mkPair lv rv) body
    | .Fun a body =>
      let lb <- lower body (ρ.insert a a)
      let f <- fresh "lam"
      let kbody <- k f
      return .letVal f (.lam a lb) kbody

    | .App f a =>
      lowerE f ρ fun vf =>
        lowerE a ρ fun va => do
          let r <- fresh "call"
          let body <- k r
          return .letRhs r (.call vf va) body

    | .Cond c t e' =>
      lowerE c ρ fun cv => do
        .seq #[] <$>
          ((.cond cv · ·) <$> lower t ρ <*> lower e' ρ)

    | .Let bs body =>
      let (recFuns, nonrecs) := splitLetGroup bs
--      let nonrecs := nonrecs.filter (fun (x, _) => !x.startsWith "(")
--      let recFuns := recFuns.filter (fun (fid, _, _, _) => !fid.startsWith "(")
      lowerNonRecBinds nonrecs.toSubarray ρ fun ρ' => do
        if recFuns.isEmpty then
          lower body ρ'
        else
          -- build all recursive functions in one letRec
          let funs <- recFuns.mapM fun (fid, selfN, params, core) =>
            lowerRecFun fid selfN params core ρ'
          let ρ'' := recFuns.foldl (init := ρ') fun acc (fid, _, _, _) => acc.insert fid fid
          let body' <- lower body ρ''
          return .letRec funs body'

    | .Fix lam | .Fixcomb lam =>
      match decomposeLamChain lam with
      | some (selfN, params, core) => do
        let fname <- fresh "f"
        let funIR <- lowerRecFun fname selfN params core ρ
        let r <- fresh "r"
        let cont <- k r
        return .letRec #[⟨fname, funIR.param, funIR.body⟩]
               (.letVal r (.var fname) cont)
      | none => lowerE lam ρ k

    | .Match scrs rows =>
      lowerMany scrs ρ fun svars => do
        lowerMatchDT svars rows ρ k

@[inline] partial def lower (e : Expr) (ρ : Env := ∅) : M σ LExpr :=
  lowerE e ρ $ pure ∘ .seq #[] ∘ .ret

partial def lowerMany
  (es : Array Expr)
  (ρ : Env)
  (k : Array Name -> M σ LExpr) : M σ LExpr := go 0 #[] where
  go i acc : M σ LExpr :=
    if h : i < es.size then
      lowerE es[i] ρ $ go i.succ ∘ acc.push
    else k acc

partial def lowerRecFun
  (fid : Name) (selfN : String) (params : Array String) (core : Expr) (ρ : Env)
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
    else lower core ρᵢ

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
  (k : Name -> M σ LExpr)
  (onFail : LExpr)
  : M σ LExpr := do
  match dt with
  | .fail => return onFail
  | .leaf row =>
    bindPatBinds roots row.binds ρ (lowerE row.rhs · k)
  | .splitProd j next =>
    letI s := cols[j]!
    letI cols' := cols.replaceAt j #[.field s 0, .field s 1]
    lowerDT cols' roots next ρ k onFail
  | .testConst j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM (fun (tc, sub) => do
        let br <- lowerDT (cols.eraseIdx! j) roots sub ρ k onFail
        pure (constOnly tc, br))
      let defIR? <- match d? with
                    | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ k onFail
                    | none   => pure (some onFail)
      return .seq #[] (.switchConst sv caseIRs defIR?)
  | .testCtor j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM fun (cname, ar, sub) => do
        let cols' := cols.replaceAt j $ .ofFn $ Sel.field cols[j]! ∘ @Fin.toNat ar
        let br <- lowerDT cols' roots sub ρ k onFail
        pure (cname, ar, br)
      let defIR? <- match d? with
                    | some d => some <$> lowerDT (cols.eraseIdx! j) roots d ρ k onFail
                    | none   => pure (some onFail)
      return .seq #[] (.switchCtor sv caseIRs defIR?)

partial def lowerMatchDT
  (scrs : Array Name) (rows : Array (Array Pattern × Expr))
  (ρ : Env) (k : Name -> M σ LExpr) : M σ LExpr := do
  let u <- fresh "u"
  let kont <- k u
  let fallback : LExpr := .letVal u (.cst .unit) kont
  let cols := Array.ofFn (Sel.base ∘ @Fin.toNat scrs.size)
  let rstates := rows.map fun (pats, rhs) => {pats, rhs}
  let dt := buildTree cols rstates
  lowerDT cols scrs dt ρ (fun x => pure (.seq #[] (.ret x))) fallback

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
    else
      k ρ'

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

partial def lowerModule (decls : Array TopDecl) : M σ (LModule × LModule) := do
  -- not used yet.
  let tyEnvRef : ST.Ref σ (Std.HashMap String TyDecl) <- ST.mkRef ∅

  let rec build (i : Nat) (ρ : Env) (last? : Option Name) : M σ LExpr := do
    if h : i < decls.size then
      match decls[i] with
      | .tyBind td =>
        tyEnvRef.modify fun m => m.insert td.tycon td
        build (i + 1) ρ last?

      | .idBind binds =>
        -- filter out operator-like names
        let binds := binds.filter $ not ∘ (·.startsWith "(") ∘ Prod.fst
        let (recFuns, nonrecs) := splitLetGroup binds
        lowerNonRecBinds nonrecs.toSubarray ρ fun ρ' => do
          if h : recFuns.size = 0 then
            build (i + 1) ρ' (if h : nonrecs.size = 0 then last? else some nonrecs.back.1)
          else
            -- Build all rec functions together
            let funIRs <- recFuns.mapM fun (fid, selfN, ps, core) =>
              lowerRecFun fid selfN ps core ρ'
            let ρ'' := recFuns.foldl (init := ρ') (fun acc (fid, _, _, _) => acc.insert fid fid)
            let next <- build (i + 1) ρ'' (some recFuns.back.1)
            return (.letRec funIRs next)

      | .patBind (pat, e) =>
        lowerE e ρ fun scr => do
          let onOk (ρ' : Env) := build (i + 1) ρ' last?
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
  let body <- optimizeLam <$> build 0 ∅ none
  let main : LFun := {fid, param, body}
  let mod := ⟨#[], main⟩
  return Prod.mk mod (runST fun _ => (IR.closureConvert mod).run' 1000)

end

@[inline] def toLamModule (decls : Array TopDecl) : LModule × LModule :=
  runST fun _ => IR.lowerModule decls |>.run' 0

def toLamModule1 e :=
  let e := optimizeLam $ runST fun _ => lower e |>.run' 0
  runST fun _ => closureConvert ⟨#[], "main", "arg", e⟩ |>.run' 0

@[inline] def dumpLamModule (decls : Array TopDecl) : Std.Format × Std.Format :=
  toLamModule decls |>.map fmtModule fmtModule

@[inline] def toLam1 e := runST fun _ => lower e |>.run' 0
@[inline] def toLam1O e := optimizeLam (toLam1 e)
def dumpLam1 s := IO.println $
  Std.Format.pretty (width := 80) $
  let e := Parsing.parse s initState
  match e with
  | .ok e => fmtLExpr $ runST fun _ => lower e |>.run' 0
  | .error e => e
def dumpLam1O s := IO.println $
  Std.Format.pretty (width := 80) $
  let e := Parsing.parse s initState
  match e with
  | .ok e => fmtLExpr ∘ optimizeLam $ runST fun _ => lower e |>.run' 0
  | .error e => e

private def cmpO s := IO.println $
  match Parsing.parse s initState with
  | .ok e =>
    letI le := runST fun _ => lower e |>.run' 0
    letI ole := optimizeLam le
    Std.Format.pretty (width := 80) $
      .group ("unoptimized:" ++ Std.Format.indentD (fmtLExpr le)) <+>
      .group ("optimized:" ++ Std.Format.indentD (fmtLExpr ole))

  | .error e => e

def cmpIR e :=
  letI le := runST fun _ => lower e |>.run' 0
  letI ole := optimizeLam le
  .group (mkBoldBlackWhite "unoptimized:" ++ Std.Format.indentD (fmtLExpr le)) <+>
  .group (mkBoldBlackWhite "optimized:" ++ Std.Format.indentD (fmtLExpr ole))

def ccExpr s := IO.println $
  Std.Format.pretty (width := 80) $
  let e := Parsing.parse s initState
  match e with
  | .ok e =>
    let e := optimizeLam $ runST fun _ => lower e |>.run' 0
    let c := runST fun _ => closureConvert ⟨#[], "main", "arg", e⟩ |>.run' 0
    fmtModule c
  | .error e => e
