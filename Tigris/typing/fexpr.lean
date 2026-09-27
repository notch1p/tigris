import Tigris.typing.fsyntax

/-! System F dictionary abstraction/application.

Given a scheme

- ∀ α₁ … αₙ [P₁,…,Pₖ], τ

we elaborate a binding rhs (`TExpr`) to

- Λα₁,…,αₙ.λd₁,…,dₖ.body

where `d₁,…,dₖ` are the respective instances of preds `P₁,…,Pₖ`

- Except when the rhs already starts with the exact k dictionary lambdas
  (wrappers auto‑generated for class methods) in which case we only add TyLams.

At each `Var` occurrence:
  - `Var x : σ` where `σ = ∀ ..α.. [..P..], tyBody`
is elaborated to

  TyApp … (TyApp (Var x monoType) α₁) … αₙ   -- instantiate
  App (…) dict₁
  …
  App (…) dict_k

Dictionary arguments are either:
  - in scope (matching one of the predicate templates introduced by lambdas), or
  - synthesized by instance resolution (Resolve.resolvePred) producing an Expr;
    we re-run inference + elaboration on that Expr to an FExpr (recursive).

If a method field type is polymorphic (embedded rank‑1): `TSch (Forall as [] τ)`,
we reify that as System F type abstractions by wrapping the projected field with
`TyLam` for each binder in `as`. But note that,

- Per-method predicate contexts inside TSch are currently unsupported and will be rejected.
-/
namespace SysF open MLType TExpr Rewritable SysF.Helper
open ConstraintInfer (unify)
open Resolve (resolvePred)

mutual
partial def elaborateDict
  (Γsch : FEnv) (scope : DictScope) (p : Pred) (Γfull : Env)
  : F FExpr := do
  match lookupDictVar scope p with
  | some (v, dty) => return .Var v dty
  | none =>
    match <- memoLookup p with
    | some d => return .Var d.name d.scheme.body
    | none =>
      unless isGroundPred p
      do     throw $ .NoSynthesize s!"{p}: missing in-scope instance for dictionary\n"

      let dictExpr <- resolvePred Γfull p
      let (te, sch, _, _) <- runInferConstraintT dictExpr Γfull
      let fe <- elaborateWithScope Γsch scope ∅ te sch Γfull
      let dty := dictTypeOfPred p
      let (nm, idx) <- freshIdx s!"rd_{p.cls}_"
      let dsch : Scheme := .Forall [] [] dty
      memoInsert p ⟨nm, idx, dsch, fe⟩
      return .Var nm dty

partial def elaborate (Γsch : FEnv) (scope : DictScope) (blocked : Blocked) (Γfull : Env) : TExpr -> F FExpr
  | .CI i ty => return .CI i ty
  | .CS s ty => return .CS s ty
  | .CB b ty => return .CB b ty
  | .CUnit ty => return .CUnit ty
  | .Ascribe e (.TSch (.Forall vs ctx ps)) => do
    let dictVars := ctx.mapIdx fun i p => (p, s!"d_{p.cls}_{i}")
    let scope' := dictVars.foldl (flip List.cons) scope
    let core <- elaborate Γsch scope' blocked Γfull e
    let coreWithDicts :=
      if ctx.isEmpty then core
      else dictVars.foldr (fun (p, nm) acc =>
        let dty := dictTypeOfPred p
        .Fun nm dty acc (dty ->' acc.getTy))
        core
    return wrapTyLams vs coreWithDicts
  | .Ascribe e _ => elaborate Γsch scope blocked Γfull e
  | .Prod' l r ty =>
    .Prod' (ty := ty) <$> elaborate Γsch scope blocked Γfull l <*> elaborate Γsch scope blocked Γfull r
  | .Cond c t e ty =>
    .Cond (ty := ty) <$> elaborate Γsch scope blocked Γfull c
                     <*> elaborate Γsch scope blocked Γfull t
                     <*> elaborate Γsch scope blocked Γfull e
  | .Var x tArgs ty =>
    if x ∈ blocked then return .Var x ty
    else
      match Γsch[x]? with
      | none => return .Var x ty
      | some (.Forall qs ctx _) => do
        -- reuse the instantiation args. we simply rebuild the binder subst from them.
        -- previously we solved args from unification. That has problem, see comment on TExpr.Var.
        let sub : Subst := List.foldl2 Std.TreeMap.insert ∅ qs tArgs
        let instCtx := apply sub ctx
        let method? : Option (ClassInfo × MethodInfo) :=
          Γfull.clsInfo.fold (init := none) fun acc _ ci =>
            match acc with
            | some _ => acc
            | none => ci.methods.find? (·.mname == x) |>.map (ci, ·)
        match method? with
        | none =>
          let base := tArgs.foldl FExpr.TyApp (.Var x ty)
          instCtx.foldlM (fun acc p => Helper.mkApp acc <$> elaborateDict Γsch scope p Γfull) base
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
          let ke <- get <&> (·.ke)
          let (projTy, wrapPoly) :=
            match peelSch1 methodTyFull with
            | some (innerB, innerP, innerTy) =>
              if innerP.isEmpty then
                match unify ke innerTy (monoOfTSch ty) with
                | .ok (sub, _) => (apply sub innerTy, pure ∘ id)
                | .error _ => (innerTy, pure ∘ wrapTyLams innerB)
              else
                let rec wrapPreds (i : Nat) (acc : FExpr) : List Pred -> FExpr
                  | [] => acc
                  | p :: ps =>
                    let (dty, nm) := (dictTypeOfPred p, s!"d_{p.cls}_{i}")
                    wrapPreds (i + 1) (FExpr.Fun nm dty acc (dty ->' acc.getTy)) ps
                let wrapDictsTyLams := (wrapTyLams innerB $ wrapPreds 0 · innerP)
                (innerTy, pure ∘ wrapDictsTyLams)
            | none => (methodTyFull, pure ∘ id)
          let projMono : FExpr := .Proj dict m.mname m.idx projTy
          let others := instCtx.filter (·.cls != ci.cname)
          let projWithDicts <-
            others.foldlM (fun acc p => Helper.mkApp acc <$> elaborateDict Γsch scope p Γfull) projMono
          tArgs.foldl .TyApp <$> wrapPoly projWithDicts
  | .Fun p pTy body ty =>
    -- a rank-n parameter binds a scheme and must be instantiated via TyApp in the body
    let Γsch := match pTy with
      | .TSch (.Forall vs ps t) => Γsch.insert p (.Forall vs ps t)
      | _ => Γsch
    (.Fun p pTy · ty) <$> elaborate Γsch scope (blocked.insert p) Γfull body
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
        let rhsFinal <- withMemoScope do
          let rhs := match rhs with | .Ascribe e .. => e | e => e
          let rhsCore <- elaborate Γsch scopeForRhs blocked Γfull rhs
          let rhsCore := wrapExtracted sch rhsCore
          let bodyWithDicts :=
            if ctx.isEmpty then rhsCore
            else dictVars.foldr
              (fun (p, nm) acc =>
                let dty := dictTypeOfPred p
                .Fun nm dty acc (dty ->' acc.getTy))
              rhsCore
          return wrapTyLams qs bodyWithDicts
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
             \n  {ex.map (Pattern.toStr)}\n"
      else
        if red.isEmpty then "" else
          letI br := red.foldl (init := "") fun a i =>
            s!"{a}\n  {i + 1})  {br[i]!.1.map (Pattern.toStr)}"
          Logging.warn s!"Found redundant alternatives at{br}\n"
    let brF :=
      if red.isEmpty then brF else
        Prod.fst $ brF.size.fold (init := (#[], red, 0)) fun i _ (acc, red, idx) =>
          if red.binSearchContains i (fun m n => m < n) idx
          then (acc, red, idx + 1) else (acc.push brF[i], red, idx)
    unless msg.isEmpty do logAppend msg
    return .Match discrF brF resTy ex red

partial def elaborateWithScope
    (Γsch : FEnv) (scope : DictScope) (blocked : Blocked) (te : TExpr) (sch : Scheme) (Γfull : Env)
    : F FExpr := withMemoScope do
    let (.Forall qs ctx _) := sch
    let te := match te with | .Ascribe e _ => e | e => e
    let dictVars := ctx.mapIdx fun i p => (p, s!"d_{p.cls}_{i}")
    let scopeFor := dictVars.foldl (flip List.cons) scope
    let core <- wrapExtracted sch <$> elaborate Γsch scopeFor blocked Γfull te
    let transform kont :=
      if ctx.isEmpty then kont core
      else kont $
        dictVars.foldr
          (fun (p, nm) acc =>
            let dty := dictTypeOfPred p
            .Fun nm dty acc (dty ->' acc.getTy))
          core
    return wrapTyLams qs $ transform (stripDupLeadingTyLams qs ∘ ηReduce ∘ βReduce)

end

def elaborate1 (e : TExpr) (sch : Scheme) (Γ : Env := ∅) : F (FExpr × Scheme) :=
  elaborateWithScope Γ.E [] ∅ e sch Γ <&> fun fe =>
    let (sch, sub, st) := renameMVSchFrom {} sch
    (applyFE st sub fe, sch)
end SysF

open MLType SysF
def runInferConstraintF (e : Expr) (Γ : Env)
  : Except TypingError (FExpr × Scheme × Logger) :=
  match runInferConstraintT e Γ with
  | .ok (te, sch, log, _) =>
    match elaborate1 te sch Γ |>.run {ke := KindEnv.ofEnv Γ} with
    | .ok (fe, sch) st => return (fe, sch, log ++ st.log)
    | .error e _ => throw e
  | .error err => throw err

def runInfer1F (e : TExpr) (sch : Scheme) (Γ : Env) : Except TypingError (FExpr × Scheme × Logger) :=
  match elaborate1 e sch Γ |>.run {ke := KindEnv.ofEnv Γ} with
  | .error e _ => throw e
  | .ok (fe, sch) st => return (fe, sch, st.log)

abbrev BindingF := Symbol × Scheme × FExpr

inductive TopDeclF
  | idBind : Array BindingF -> TopDeclF
  | patBind : Pattern × Scheme × FExpr -> TopDeclF
deriving Repr

def inferToplevelF : Array TopDeclT × Env × Logger -> (_ : Std.HashMap String Nat := ∅) -> Except TypingError (Array TopDeclF × Logger × Std.HashMap String Nat)
  | (b, Γ, L), ctors =>
    b.foldlM (init := (#[], L, ctors)) fun (bF, L, ctorsAcc) b => do
      match b with
      | .idBind binds =>
        let (acc, L) <- binds.foldlM (init := (#[], L)) fun (acc, L) (id, sch, te) =>
          runInfer1F te sch Γ <&> fun (fe, sch, l) => (acc.push (id, sch, fe), L ++ l)
        return (bF.push $ .idBind acc, L, ctorsAcc)
      | .patBind (pat, sch, te) =>
        runInfer1F te sch Γ <&> fun (fe, sch, l) =>
          (bF.push $ .patBind (pat, sch, fe), L ++ l, ctorsAcc)
      | .tyBind {ctors,..} =>
        return (bF, L, ctors.foldl (fun acc (name, _, ar) => acc.insert name ar) ctorsAcc)

open Std Std.Format in
def TopDeclF.unexpand : TopDeclF -> Format
  | .idBind binds =>
    let (binds, recflag) := binds.foldl (init := (#[], false)) fun (acc, recflag) (id, sch, fe) =>
      match fe with
      | .Fix (.Fun _ _ body _) _ =>
        (acc.push $ fill $ id ++ indentD (":" <> sch.renderFmt <> "=" <+> body.unexpand), true)
      | _ =>
        (acc.push $ fill $ id ++ indentD (":" <> sch.renderFmt <> "=" <+> fe.unexpand), recflag)
    let recStr := if recflag then .text " rec " else .text " "
    group $ "let" ++ recStr ++ joinSep' binds (line ++ "and ")
  | .patBind (pat, sch, e) =>
    group $ "let" <> pat.toStr ++ indentD (":" <> sch.renderFmt <+> "=" <> nest 1 e.unexpand)
in instance : ToFormat FExpr := ⟨FExpr.unexpand⟩
in instance : ToFormat TopDeclF := ⟨TopDeclF.unexpand⟩
in
def unexpandDeclsF (arr : Array TopDeclF) : Format := joinSep' arr (line ++ line)


-- example: No eagerly simplification
instance : Functor $ Sum α where
  map f
  | .inr b => .inr (f b)
  | .inl a => .inl a

def prog [ToString α] : IO Unit :=
  println! (1 + ·) <$> (Sum.inr 1 : α ⊕ Int)

/--
error: typeclass instance problem is stuck
  ToString ?m.2

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `ToString` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
#eval prog -- we mirror the approach used by Lean in Tigris by blocking all
           -- context with MVs, even though it makes sense to not to (as the program is still well typed.)

/--
info: (inr 2)
-/
#guard_msgs in
#eval prog (α := Unit) -- must be concrete
