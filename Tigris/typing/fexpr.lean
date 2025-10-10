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

If a method field type is polymorphic (embedded rank‑1): `TSch (Forall as [] τ)`,
we reify that as System F type abstractions by wrapping the projected field with
`TyLam` for each binder in `as`. But note that,

- Per-method predicate contexts inside TSch are currently unsupported and will be rejected.
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
abbrev Blocked := Std.HashSet String

local instance : MonadLift (Except TypingError) F where
  monadLift
  | .error e => throw e
  | .ok res => return res

namespace Helper

@[inline] def dictTypeOfPred : Pred -> MLType
  | {cls, args,..} => TApp cls args

@[inline] def monoOfTSch : MLType -> MLType
  | .TSch (.Forall _ _ t) => t
  | t => t

def αRename (qs : List TV) : Subst × List TV :=
  let mkFresh : TV -> Nat -> TV
    | _, i => .mkTV s!"?inst{i}"
  qs.foldrIdx (init := (∅, [])) fun i q (sub, acc) => 
    let q' := mkFresh q i
    (sub.insert q (.TVar q'), q' :: acc)

def instantiateArgs (qs : List TV) (ctx : List Pred) (schemeBody instTy : MLType)
  : F (List MLType × Subst × List Pred) := do
  if qs.isEmpty then return ([], ∅, ctx)
  let (rn, qs) := αRename qs
  let schemeBody := apply rn schemeBody
  let ctx := apply rn ctx
  let sub <- unify (monoOfTSch instTy) (monoOfTSch schemeBody)
  return (qs.map (fun a => apply sub (TVar a)), sub, apply sub ctx |>.map Helper.normHKPred)

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e
@[inline] def mkApp (f a : FExpr) : FExpr :=
  .App f a $ match f.getTy with | _ ->' b => b | other => other

def isSkolemOf (h : String) (v : TV) : Bool :=
  let h' := Substring.mk h ⟨4⟩ h.endPos
  let v := v.toStr.toSubstring
  h.startsWith "?sk." && h' == v
partial def eqSkolem : MLType -> MLType -> Bool
  | .TVar v, .TVar w => v == w
  | .TVar v, .TCon h => isSkolemOf h v
  | .KApp v asT, .KApp w asG
  | .TApp v asT, .TApp w asG =>
    v == w 
    && asT.length == asG.length 
    && List.all2 eqSkolem asT asG
  | .KApp v asT, .TApp h asG | .TApp h asG, .KApp v asT =>
    (isSkolemOf h v || (h.isLowerInit && toString v == h))
    && asT.length == asG.length
    && List.all2 eqSkolem asT asG
  | t₁ ->' t₂, u₁ ->' u₂ | t₁ ×'' t₂, u₁ ×'' u₂ => eqSkolem t₁ u₁ && eqSkolem t₂ u₂
  | .TCon a, .TCon b => a == b
  | _, _ => false

def mv? : TV -> Bool
  | .mkTV s => s.startsWith "?"

@[inline] def isHKVarTV : TV -> Bool
  | .mkTV s => s.isLowerInit

def templHasVarHead : MLType -> Bool
  | .TVar _ => true
  | .KApp _ [] => true
  | .TApp h [] => h.isLowerInit
  | _ => false

def eqGoal (templ goal : MLType) : Bool :=
  match goal with
  | .TVar v => mv? v || isHKVarTV v && templHasVarHead templ || eqSkolem templ goal
  | .KApp v [] => isHKVarTV v && templHasVarHead templ || eqSkolem templ goal
  | .TApp h [] => h.isLowerInit && templHasVarHead templ || eqSkolem templ goal
  | _ => eqSkolem templ goal

def predEqGoal (templ goal : Pred) : Bool :=
  templ.cls == goal.cls
  && templ.args.length == goal.args.length
  && List.all2 eqGoal templ.args goal.args

def predEqSkolem (templ goal : Pred) : Bool :=
  templ.cls == goal.cls
  && templ.args.length == goal.args.length
  && List.all2 eqSkolem templ.args goal.args

-- linear search, scope is usually tiny.
def lookupDictVar (scope : DictScope) (goal : Pred) : Option (String × MLType) :=
  go scope where
  go
  | [] => none
  | (templ, v) :: xs =>
    if predEqSkolem templ goal || predEqGoal templ goal then some (v, dictTypeOfPred templ)
    else go xs
#eval lookupDictVar 
  [({ cls := "Monad", args := [MLType.KApp (TV.mkTV "α") []] }, "d_Monad_0")] 
  { cls := "Monad", args := [MLType.KApp (TV.mkTV "m") []] }

@[inline] def isGroundPred (p : Pred) : Bool :=
  (fv p.args).isEmpty

@[inline] def patOfIdx (ctor : Symbol) (idx : Nat) (sz : Nat) : Pattern :=
  .PCtor ctor $ Array.replicate sz .PWild |>.set! idx (.PVar s!"m_{ctor}_{idx}")

def mvs (p : Pred) : List TV :=
  let vs := fv p.args
  vs.fold (fun a tv => if mv? tv then tv :: a else a) []

def stuckMessage (p : Pred) (method : String) : TypingError :=
  let metas := mvs p
  let metaS := if metas.isEmpty then ""
  else
    s!"{p}: typeclass elaboration is stuck because of metavariable(s)\n  \
       {toString metas}\n\
       induced by a call to {method}. To resolve this, consider adding type ascriptions.\n"
  let base := s!"{p}: missing in-scope instance for method {method}\n"
  if metas.isEmpty then .NoSynthesize base
  else .Ambiguous metaS

def peelFun (acc : List (String × MLType)) : FExpr -> List (String × MLType) × FExpr
  | .Fun p pty b _ => peelFun ((p, pty) :: acc) b
  | t => (acc.reverse, t)
def peelSch1 : MLType -> Option (List TV × List Pred × MLType)
  | .TSch (.Forall vs ps t) => some (vs, ps, t)
  | _ => none

def pvs : Pattern -> Array String
  | .PVar x => #[x] | .PWild => #[]
  | .PConst _ => #[] | .PProd' p q => pvs p ++ pvs q
  | .PCtor _ args => args.flatMap pvs

def wrapExtracted (sch : Scheme) (e : FExpr) : FExpr :=
  match sch with
  | .Forall _ _ b =>
    match peelSch1 b with
    | some (innerTVs, innerPs, _) =>
      if innerPs.isEmpty then wrapTyLams innerTVs e
      else e
    | none => e

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
    elaborateWithScope Γsch scope ∅ te sch Γfull

partial def elaborate (Γsch : FEnv) (scope : DictScope) (blocked : Blocked) (Γfull : Env) : TExpr -> F FExpr
  | .CI i ty => return .CI i ty
  | .CS s ty => return .CS s ty
  | .CB b ty => return .CB b ty
  | .CUnit ty => return .CUnit ty
  | .Ascribe e _ => elaborate Γsch scope blocked Γfull e
  | .Prod' l r ty =>
    .Prod' (ty := ty) <$> elaborate Γsch scope blocked Γfull l <*> elaborate Γsch scope blocked Γfull r
  | .Cond c t e ty =>
    .Cond (ty := ty)
    <$> elaborate Γsch scope blocked Γfull c
    <*> elaborate Γsch scope blocked Γfull t
    <*> elaborate Γsch scope blocked Γfull e
  | .Var x ty =>
    if x ∈ blocked then return (.Var x ty)
    else
      match Γsch[x]? with
      | none => return (.Var x ty)
      | some (.Forall qs ctx bodyTy) => do
        let (tArgs, sub, instCtx) <- instantiateArgs qs ctx bodyTy ty
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
              else throw $ stuckMessage classPred x
          let ar := ci.methods.size
          let methodTyFull := apply sub m.mty
          let (projTy, wrapPoly) :=
            match peelSch1 methodTyFull with
            | some (innerB, innerP, innerTy) =>
              if innerP.isEmpty then
                match unify innerTy (monoOfTSch ty) with
                | .ok sub => (apply sub innerTy, pure ∘ id)
                | .error e => (innerTy, pure ∘ wrapTyLams innerB)
              else (innerTy, fun _ => show F FExpr from throw TypingError.NoRankN)
            | none => (methodTyFull, pure ∘ id)
          let pat := patOfIdx ci.cname m.idx ar
          let projMono : FExpr :=
            .Match #[dict] #[(#[pat], .Var s!"m_{ci.cname}_{m.idx}" projTy)]
              projTy none #[]
          let others := instCtx.filter (·.cls != ci.cname)
          let projWithDicts <-
            others.foldlM (fun acc p => mkApp acc <$> elaborateDict Γsch scope p Γfull) projMono
          let projWrapped <- wrapPoly projWithDicts
          return tArgs.foldl .TyApp projWrapped
  | .Fun p pTy body ty => (.Fun p pTy · ty) <$> elaborate Γsch scope (blocked.insert p) Γfull body
  | .Fix e ty | .Fixcomb e ty => (.Fix · ty) <$> elaborate Γsch scope blocked Γfull e
  | .App f a ty =>
    .App (ty := ty)
    <$> elaborate Γsch scope blocked Γfull f
    <*> elaborate Γsch scope blocked Γfull a
  | .Let binds body ty => do
    let Γsch := binds.foldl (fun g (x, sch, _) => g.insert x sch) Γsch
    let (localScope, out) <-
      binds.foldlM (init := (scope, #[])) fun (localScope, out) (x, sch@(.Forall qs ctx bTy), rhs) => do
        let dictVars := ctx.mapIdx fun i p => (p, s!"d_{p.cls}_{i}")
        let scopeForRhs := dictVars.foldl (flip List.cons) localScope
        let rhsCore <- elaborate Γsch scopeForRhs blocked Γfull rhs
        let rhsCore := wrapExtracted sch rhsCore
        let bodyWithDicts :=
          if ctx.isEmpty then rhsCore
          else dictVars.foldr
            (fun (p, nm) acc =>
              let dty := dictTypeOfPred p
              .Fun nm dty acc (dty ->' acc.getTy))
            rhsCore
        let rhsFinal := wrapTyLams qs bodyWithDicts
        return (scopeForRhs, out.push (x, sch, rhsFinal))
    let bodyF <- elaborate Γsch localScope blocked Γfull body
    return (.Let out bodyF ty)
  | .Match discr br resTy .. => do
    let discrF <- discr.mapM (elaborate Γsch scope blocked Γfull)
    let discrTy := discr.map (TExpr.getTy)
    let brF <- br.mapM fun (ps, rhs) =>
      (ps, ·) <$> elaborate Γsch scope (blocked.insertMany (ps.flatMap pvs)) Γfull rhs
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
    (Γsch : FEnv) (scope : DictScope) (blocked : Blocked) (te : TExpr) (sch : Scheme) (Γfull : Env)
    : F FExpr := do
    let (.Forall qs ctx _) := sch
    let dictVars := ctx.mapIdx fun i p => (p, s!"d_{p.cls}_{i}")
    let scopeFor := dictVars.foldl (flip List.cons) scope
    let core <- elaborate Γsch scopeFor blocked Γfull te
    let core := wrapExtracted sch core
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
    return wrapTyLams qs coreWithDicts

end

def elaborate1 (e : TExpr) (sch : Scheme) (Γ : Env := ∅) : F FExpr := do
  elaborateWithScope Γ.E [] ∅ e sch Γ

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
  | .CI i _ | .CB i _ | .CS i _ => repr i
  | .CUnit _ => format ()
  | .App f a _ =>
    let rec parenR?
      | p@(.App ..) | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
      | p => unexpand p
    let rec parenL?
      | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
      | p => unexpand p
    parenL? f <> parenR? a
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

