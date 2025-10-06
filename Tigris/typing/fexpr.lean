import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.constraint
import Tigris.typing.resolve

/-! System F dictionary abstraction/application.

Given a scheme
```
∀ α₁ … αₙ [P₁,…,Pₖ], τ
```
we elaborate a binding rhs (`TExpr`) to
```
Λα₁,…,αₙ.λd₁,…,dₖ.body
```
where `d₁,…,dₖ` are the respective instances of preds `P₁,…,Pₖ`

- Except when the rhs already starts with the exact k dictionary lambdas
  (wrappers auto‑generated for class methods) in which case we only add TyLams.

At each `Var` occurrence:
  - `Var x : σ` where `σ = ∀ ..α.. [..P..], tyBody`
is elaborated to
```
  TyApp … (TyApp (Var x monoType) α₁) … αₙ   -- instantiate
  App (…) dict₁
  …
  App (…) dict_k
```

Dictionary arguments are either:
  - in scope (matching one of the predicate templates introduced by lambdas), or
  - synthesized by instance resolution (Resolve.resolvePred) producing an Expr;
    we re-run inference + elaboration on that Expr to an FExpr (recursive).

-/

namespace SysF open MLType TExpr Rewritable
open ConstraintInfer (unify)
open Resolve (resolvePred)

inductive FExpr where
  | CI     (i : Int)    (ty : MLType)
  | CS     (s : String) (ty : MLType)
  | CB     (b : Bool)   (ty : MLType)
  | CUnit               (ty : MLType)
  | Var    (x : String) (ty : MLType)                 -- monomorphic view at site
  | Fun    (param : String) (paramTy : MLType)
           (body : FExpr) (ty : MLType)               -- paramTy -> body.ty = ty
  | App    (f : FExpr) (a : FExpr) (ty : MLType)      -- result type after application
  | TyLam  (a : TV) (body : FExpr)                    -- type abstraction
  | TyApp  (f : FExpr) (arg : MLType)                 -- type application
  | Let    (binds : Array (String × Scheme × FExpr))  -- each binding elaborated & wrapped
           (body : FExpr) (ty : MLType)
  | Prod'  (l r : FExpr) (ty : MLType)
  | Cond   (c t e : FExpr) (ty : MLType)
  | Match  (discr : Array FExpr)
           (branches   : Array (Array Pattern × FExpr))
           (resTy      : MLType)
           (counterexample : Option (List Pattern))
           (redundantRows  : Array Nat)
  | Fix    (e : FExpr) (ty : MLType)                  -- rec tag
deriving Repr, Inhabited

def FExpr.getTy
  | CI _ ty | CS _ ty | CB _ ty | CUnit ty
  | Var _ ty | Fun _ _ _ ty | App _ _ ty
  | Let _ _ ty | Prod' _ _ ty | Cond _ _ _ ty
  | Match _ _ ty _ _ | Fix _ ty => ty
  | TyLam _ f
  | TyApp f _ => f.getTy
    -- TyApp currently doesn't carry result type.
    -- f.getTy should NOT yield a arrow type as polys are erased after instantiation

abbrev FEnv := Std.TreeMap String Scheme
abbrev DictScope := List (Pred × String)  -- predicate template + dict variable name
abbrev F := EStateM TypingError Logger

local instance : MonadLift (Except TypingError) F where
  monadLift
  | .error e => throw e
  | .ok res => return res

namespace Helper

@[inline] def dictTypeOfPred : Pred -> MLType
  | {cls, args,..} => TApp cls args

def instantiateArgs (qs : List TV) (schemeBody instTy : MLType)
  : F (List MLType × Subst) := do
  if qs.isEmpty then return ([], ∅)
  let sub <- unify schemeBody instTy
  return (qs.map (fun a => apply sub (TVar a)), sub)

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e
@[inline] def mkApp (f a : FExpr) : FExpr :=
  .App f a $ match f.getTy with | _ ->' b => b | other => other

-- linear search, scope is usually tiny.
def lookupDictVar (scope : DictScope) (goal : Pred) : Option (String × MLType) :=
  go scope where
  go
  | [] => none
  | (templ, v) :: xs =>
    if templ.cls != goal.cls || templ.args.length != goal.args.length then go xs
    else
      let (s, ok) := unify2 (∅ : Subst) templ.args goal.args
      if ok then some (v, apply s (dictTypeOfPred templ)) else go xs
  unify2 s
  | ta :: tas, ga :: gas =>
    match unify (apply s ta) (apply s ga) with
    | .ok s' => unify2 (s' ∪' s) tas gas
    | .error _ => (s, false)
  | _, _ => (s, true)

@[inline] def isGroundPred (p : Pred) : Bool :=
  (fv p.args).isEmpty

@[inline] def patOfIdx (ctor : Symbol) (idx : Nat) (sz : Nat) : Pattern :=
  .PCtor ctor $ Array.replicate sz .PWild |>.set! idx (.PVar s!"__m_{ctor}_{idx}")

def mvs (p : Pred) : List TV :=
  let vs := fv p.args
  vs.fold (fun a tv@(.mkTV s) => if s.startsWith "?m" then tv :: a else a) []

def stuckMessage (p : Pred) (method : String) : TypingError :=
  let metas := mvs p
  let metaS := if metas.isEmpty then ""
  else
    s!"{p}: typeclass elaboration is stuck because of metavariable(s)\n  "
    ++ toString metas
    ++ s!"\ninduced by a call to {method}. To resolve this, consider adding type ascriptions."
  let base := s!"{p}: missing in-scope instance for method {method}\n"
  if metas.isEmpty then .NoSynthesize base
  else .Ambiguous metaS

def peelFun (acc : List (String × MLType)) : FExpr -> List (String × MLType) × FExpr
  | .Fun p pty b _ => peelFun ((p, pty) :: acc) b
  | t => (acc.reverse, t)


end Helper

open Helper

mutual
partial def elaborateDict
  (Γsch : FEnv) (scope : DictScope) (p : Pred) (Γfull : Env)
  : F FExpr := do
  match lookupDictVar scope p with
  | some (v, dty) => return .Var v dty
  | none =>
    let dictExpr <- resolvePred Γfull p
    let (te, sch, _) <- runInferConstraintT dictExpr Γfull
    elaborateWithScope Γsch scope te sch Γfull

partial def elaborate (Γsch : FEnv) (scope : DictScope) (Γfull : Env) : TExpr -> F FExpr
  | .CI i ty => return .CI i ty
  | .CS s ty => return .CS s ty
  | .CB b ty => return .CB b ty
  | .CUnit ty => return .CUnit ty
  | .Ascribe e _ => elaborate Γsch scope Γfull e
  | .Prod' l r ty =>
    .Prod' (ty := ty) <$> elaborate Γsch scope Γfull l <*> elaborate Γsch scope Γfull r
  | .Cond c t e ty =>
    .Cond (ty := ty)
    <$> elaborate Γsch scope Γfull c
    <*> elaborate Γsch scope Γfull t
    <*> elaborate Γsch scope Γfull e
  | .Var x ty =>
    match Γsch[x]? with
    | none => return (.Var x ty)
    | some (.Forall qs ctx bodyTy) => do
      let (tArgs, sub) <- instantiateArgs qs bodyTy ty
      let instCtx := apply sub ctx
      let method? : Option (ClassInfo × MethodInfo) :=
        Γfull.clsInfo.fold (init := none) fun acc _ ci =>
          match acc with
          | some _ => acc
          | none =>
            ci.methods.find? (·.mname == x) |>.map fun m => (ci, m)
      match method? with
      | none =>
        let base := tArgs.foldl FExpr.TyApp (.Var x ty)
        instCtx.foldlM (fun acc p => mkApp acc <$> elaborateDict Γsch scope p Γfull) base
      | some (ci, m) =>
        let some classPred := instCtx.find? (·.cls == ci.cname)
          | throw (.Impossible s!"method {x} has no matching predicate after instantiation\n")
        let dict : FExpr <-
          match lookupDictVar scope classPred with
          | some (v, dty) => pure (.Var v dty)
          | none =>
            if isGroundPred classPred then
              elaborateDict Γsch scope classPred Γfull
            else
              throw $ stuckMessage classPred x
        let ar := ci.methods.size
        let methodTy := apply sub m.mty
        let pat := patOfIdx ci.cname m.idx ar
        let proj :=
          FExpr.Match #[dict]
            #[(#[pat], FExpr.Var s!"__m_{ci.cname}_{m.idx}" methodTy)]
            methodTy none #[]
        let others := instCtx.filter (·.cls != ci.cname)
        let proj <-
          others.foldlM (fun acc p => mkApp acc <$> elaborateDict Γsch scope p Γfull) proj
        let proj := tArgs.foldl .TyApp proj
        return proj
  | .Fun p pTy body ty => (.Fun p pTy · ty) <$> elaborate Γsch scope Γfull body
  | .Fix e ty | .Fixcomb e ty => (.Fix · ty) <$> elaborate Γsch scope Γfull e
  | .App f a ty => .App (ty := ty) <$> elaborate Γsch scope Γfull f <*> elaborate Γsch scope Γfull a
  | .Let binds body ty => do
    let Γsch := binds.foldl (fun g (x, sch, _) => g.insert x sch) Γsch
    let (localScope, out) <-
      binds.foldlM (init := (scope, #[])) fun (localScope, out) (x, sch@(Scheme.Forall qs ctx bTy), rhs) => do
        let dictVars := ctx.mapIdx fun i p => (p, s!"__d_{p.cls}_{i}")
        let scopeForRhs := dictVars.foldl (flip List.cons) localScope
        let rhsCore <- elaborate Γsch scopeForRhs Γfull rhs
        let bodyWithDicts :=
          if ctx.isEmpty then rhsCore
          else dictVars.foldr
            (fun (p, nm) acc =>
              let dty := dictTypeOfPred p
              .Fun nm dty acc (dty ->' acc.getTy))
            rhsCore
        let rhsFinal := wrapTyLams qs bodyWithDicts
        return (scopeForRhs, out.push (x, sch, rhsFinal))
    let bodyF <- elaborate Γsch localScope Γfull body
    return (.Let out bodyF ty)
  | .Match discr br resTy .. => do
    let discrF <- discr.mapM (elaborate Γsch scope Γfull)
    let discrTy := discr.map (TExpr.getTy)
    let brF <- br.mapM fun (ps, rhs) =>
      (ps, ·) <$> elaborate Γsch scope Γfull rhs
    let (ex, mat, ty) := Exhaustive.exhaustWitness Γfull discrTy br
    let red :=
      if let some _ := ex then #[] else
        Exhaustive.redundantRows Γfull ty mat
    let msg :=
      if let some ex := ex then
        Logging.warn
          s!"Partial pattern matching, an unmatched candidate is\
             \n  {ex.map (Pattern.render)}\n"
      else
        if red.isEmpty then "" else
          letI br := red.foldl (init := "") fun a i =>
            s!"{a}\n  {i + 1})  {br[i]!.1.map (Pattern.render)}"
          Logging.warn s!"Found redundant alternatives at{br}\n"
    let brF :=
      if red.isEmpty then brF else
        Prod.fst $ brF.size.fold (init := (#[], red, 0)) fun i _ (acc, red, idx) =>
          if red.binSearchContains i (fun m n => m < n) idx
          then (acc, red, idx + 1) else (acc.push brF[i], red, idx)
    modify fun l => (l ++ msg)
    return .Match discrF brF resTy ex red

partial def elaborateWithScope
    (Γsch : FEnv) (scope : DictScope) (te : TExpr) (sch : Scheme) (Γfull : Env)
    : F FExpr := do
    let (.Forall qs ctx _) := sch
    let dictVars := ctx.mapIdx fun i p => (p, s!"__d_{p.cls}_{i}")
    let scopeFor := dictVars.foldl (flip List.cons) scope
    let core <- elaborate Γsch scopeFor Γfull te
    let coreWithDicts :=
      if ctx.isEmpty then core
      else
        match core with
        |  .Fix (.Fun self selfTy funChain _) _ =>
          let (userParams, body) := peelFun [] funChain
          let userChain := userParams.foldr
            (fun (n, ty) acc =>
              .Fun n ty acc (ty ->' acc.getTy))
            body
          let fullChain := dictVars.foldr
            (fun (p, nm) acc =>
              let dty := dictTypeOfPred p
              .Fun nm dty acc (dty ->' acc.getTy))
            userChain
          let newSelfFun := .Fun self selfTy fullChain (selfTy ->' fullChain.getTy)
          .Fix newSelfFun newSelfFun.getTy
        | _ =>
          dictVars.foldr
          (fun (p, nm) acc =>
            let dty := dictTypeOfPred p
            .Fun nm dty acc (dty ->' acc.getTy))
          core
    let final := wrapTyLams qs coreWithDicts
    return final

end

def elaborate1 (e : TExpr) (sch : Scheme) (Γ : Env := ∅) : F FExpr := do
  elaborateWithScope Γ.E [] e sch Γ

end SysF
open MLType SysF
def runInferConstraintF (e : Expr) (Γ : Env)
  : Except TypingError (FExpr × Scheme × Logger) :=
  match runInferConstraintT e Γ with
  | .ok (te, sch, log) =>
    match elaborate1 te sch Γ |>.run "" with
    | .ok fe l => return (fe, sch, log ++ l)
    | .error e _ => throw e
  | .error err => throw err

def runInfer1F (e : TExpr) (sch : Scheme) (Γ : Env) : Except TypingError (FExpr × Logger) :=
  match elaborate1 e sch Γ |>.run "" with
  | .error e _ => throw e
  | .ok fe l => return (fe, l)

abbrev BindingF := Symbol × Scheme × FExpr

inductive TopDeclF
  | idBind : Array BindingF -> TopDeclF
  | patBind : Pattern × FExpr -> TopDeclF
deriving Repr

def inferToplevelF : Array TopDeclT × Env × Logger -> Except TypingError (Array TopDeclF × Logger)
  | (b, Γ, L) =>
    b.foldlM (init := (#[], L)) fun (bF, L) b => do
      match b with
      | .idBind binds =>
        let (acc, L) <- binds.foldlM (init := (#[], L)) fun (acc, L) (id, sch, te) =>
          runInfer1F te sch Γ <&> fun (fe, l) => (acc.push (id, sch, fe), L ++ l)
        return (bF.push $ .idBind acc, L)
      | .patBind (pat, sch, te) =>
        runInfer1F te sch Γ <&> fun (fe, l) =>
          (bF.push $ .patBind (pat, fe), L ++ l)
      | _ => return (bF, L)

local instance : Std.ToFormat Pattern where
  format := .text ∘ Pattern.toStr
open Std Std.Format in
partial def FExpr.unexpand : FExpr -> Format
  | .CI i _ | .CS i _ | .CB i _ => format i
  | .CUnit _ => format ()
  | .App f a _ =>
    let rec paren?
      | p@(.App ..) => paren (unexpand p)
      | p => unexpand p
    unexpand f <> paren? a
  | .Cond c t e _ =>
    "if" <> unexpand c <+> "then" ++ indentD (unexpand t)
    <+> "else" ++ indentD (unexpand e)
  | .Fix e _ => unexpand e
  | .Var x _ => format x
  | .Prod' p q _ => paren $ unexpand p <> "," <> unexpand q
  | .Fun param _ body _ =>
    "fun" <> param <> "=>"
    ++ indentD (unexpand body)
  | .Match discr branches .. =>
    let discr := discr.map unexpand
    let br := branches.map fun (pats, e) =>
      "|" <> joinSep' pats ", " <> "=>" ++ indentD (unexpand e)
    "match" <> joinSep' discr ", " <> "with" <+> joinSep' br line
  | .Let binds body _ =>
    let (binds, recflag) := binds.foldl (init := (#[], false)) fun (acc, recflag) (id, sch, fe) =>
      match fe with
      | .Fix (.Fun _ _ body _) _ =>
        (acc.push $ id <> ":" <> toString sch <> "=" ++ indentD (unexpand body), true)
      | _ =>
        (acc.push $ id <> ":" <> toString sch <> "=" ++ indentD (unexpand fe), recflag)
    let recStr := if recflag then .text " rec " else .text " "
    "let" ++ recStr ++ joinSep' binds "\nand" <+> "in" <> unexpand body
  | .TyLam a body => "Λ" <> toString a ++ "." ++ unexpand body
  | .TyApp f _ => unexpand f
in
def TopDeclF.unexpand : TopDeclF -> Format
  | .idBind binds =>
    let (binds, recflag) := binds.foldl (init := (#[], false)) fun (acc, recflag) (id, sch, fe) =>
      match fe with
      | .Fix (.Fun _ _ body _) _ =>
        (acc.push $ id <> ":" <> toString sch <> "=" ++ indentD (FExpr.unexpand body), true)
      | _ =>
        (acc.push $ id <> ":" <> toString sch <> "=" ++ indentD (FExpr.unexpand fe), recflag)
    let recStr := if recflag then .text " rec " else .text " "
    "let" ++ recStr ++ joinSep' binds "\nand"
  | .patBind (pat, e) =>
    "let" <> pat.toStr <> "=" ++ indentD (FExpr.unexpand e)
in instance : ToFormat FExpr := ⟨FExpr.unexpand⟩
in instance : ToFormat TopDeclF := ⟨TopDeclF.unexpand⟩
in
def unexpandDeclsF (arr : Array TopDeclF) : Format := joinSep' arr (line ++ line)
