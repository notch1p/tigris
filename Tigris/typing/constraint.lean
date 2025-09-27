import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.exhaust

namespace ConstraintInfer open MLType Rewritable Pattern Expr

inductive Constraint where
  | eq (t₁ t₂ : MLType)
  | classC (cls : String) (ty : MLType)
deriving Repr

structure CState where
  next                  := nat_lit 0
  cst : List Constraint := []
  log : Logger          := ""
deriving Inhabited

abbrev InferC σ := StateRefT CState (EST TypingError σ)

@[inline] def fresh : InferC σ MLType := do
  let n <- modifyGet fun ctx@{next,..} => (next, {ctx with next := next + 1})
  s!"?m{n}" |> pure ∘ TVar ∘ .mkTV

@[inline] def addEq (t₁ t₂ : MLType) : InferC σ Unit :=
  modify fun st@{cst,..} => {st with cst := .eq t₁ t₂ :: cst}

@[inline] def addClass (cls : String) (ty : MLType) : InferC σ Unit :=
  modify fun st@{cst,..} => {st with cst := .classC cls ty :: cst}
@[inline] def appendLog (s : String) : InferC σ Unit :=
  modify fun st@{log,..} => {st with log := log ++ s}

private def bindTV (a : TV) (t : MLType) : Except TypingError Subst :=
  if t == TVar a then pure ∅
  else if a ∈ fv t then throw (.Duplicates a t)
  else pure {(a, t)}

partial def unify : MLType -> MLType -> Except TypingError Subst
  | t₁ ×'' t₂, u₁ ×'' u₂
  | t₁ ->' t₂, u₁ ->' u₂ => do
    let s₁ <- unify t₁ u₁
    let s₂ <- unify (apply s₁ t₂) (apply s₁ u₂)
    return (s₂ ∪' s₁)
  | TVar a, t | t, TVar a => bindTV a t
  | TApp h₁ as₁, TApp h₂ as₂ =>
    if h₁ != h₂ then throw (.NoUnify (TApp h₁ as₁) (TApp h₂ as₂))
    else
      List.foldlM2
        (fun acc t₁ t₂ => (· ∪' acc) <$> unify (apply acc t₁) (apply acc t₂))
        ∅ as₁ as₂
  | TCon a, TCon b =>
    if a == b then return ∅
    else throw (.NoUnify (TCon a) (TCon b))
  | t@(TApp h []), u@(TCon h')
  | t@(TCon h), u@(TApp h' []) =>
    if h == h' then return ∅ else throw (.NoUnify t u)
  | t, u => throw (.NoUnify t u)

def solveAll (cs : List Constraint) : Except TypingError (Subst × List (String × MLType)) := do
  cs.foldrM (init := (∅, [])) fun s (sub, pending) =>
    match s with
    | .eq t u => do
      let unis := unify on apply sub
      let s <- unis t u
      return (s ∪' sub, pending)
    | .classC cls ty =>
      return (sub, (cls, apply sub ty) :: pending)

@[inline] def extend (Γ : Env) (x : String) (sch : Scheme) : Env :=
  {Γ with E := Γ.E.insert x sch}

def lookup (Γ : Env) (x : String) : InferC σ (MLType × List TV) :=
  match Γ.E[x]? with
  | none => throw (.Undefined x)
  | some (.Forall as t) => do
    let subst <- as.foldlM (·.insert · <$> fresh) ∅
    return (apply subst t, as)

def generalize (Γ : Env) (t : MLType) : Scheme :=
  let envFV := fv Γ.E.values
  let tfv := fv t
  let qs := tfv \ envFV |>.toList
  normalize $ .Forall qs t

partial def inferPattern (Γ : Env) (expt : MLType) : Pattern -> InferC σ (Env × Array (String × MLType))
  | PWild => return (Γ, #[])
  | PVar x => return (extend Γ x (.Forall [] expt), #[(x, expt)])
  | PConst (.PInt _) => addEq expt tInt $> (Γ, #[])
  | PConst (.PBool _) => addEq expt tBool $> (Γ, #[])
  | PConst (.PStr _) => addEq expt tString $> (Γ, #[])
  | PConst (.PUnit) => addEq expt tUnit $> (Γ, #[])
  | PProd' p q => do
    let a <- fresh let b <- fresh
    addEq expt (a ×'' b)
    let (Γ₁, bs₁) <- inferPattern Γ a p
    let (Γ₂, bs₂) <- inferPattern Γ₁ b q
    return (Γ₂, bs₁ ++ bs₂)
  | PCtor cname args => do
    let (ctorTy, _) <- lookup Γ cname
    let rec peel (acc : Array MLType)
      | a ->' b => peel (acc.push a) b
      | r => (acc, r)
    let (argTys, resTy) := peel #[] ctorTy
    if argTys.size == args.size then
      addEq expt resTy
      Array.foldlM2 (fun (Γ, bound) ty arg => do
        let (Γ, bs) <- inferPattern Γ ty arg
        return (Γ, bound ++ bs))
        (Γ, #[])
        argTys args
    else
      throw (.InvalidPat s!"{cname} expects {argTys.size} args, instead got {args.size}")

mutual
partial def inferExpr (Γ : Env) : Expr -> InferC σ (TExpr × MLType)
  | Var x => do
    let (t, _) <- lookup Γ x
    return (.Var x t, t)

  | CI i => return (.CI i tInt, tInt)
  | CS s => return (.CS s tString, tString)
  | CB b => return (.CB b tBool, tBool)
  | CUnit => return (.CUnit tUnit, tUnit)

  | Fun x body => do
    let tv <- fresh
    let Γ := extend Γ x (.Forall [] tv)
    let (tBody, tB) <- inferExpr Γ body
    let fnTy := tv ->' tB
    return (.Fun x tv tBody fnTy, fnTy)

  | Fix (Fun f body) => do
    let tv <- fresh
    let Γ := extend Γ f (.Forall [] tv)
    let (tBody, tB) <- inferExpr Γ body
    addEq tv tB
    return (.Fix (.Fun f tv tBody (tv ->' tB)) tv, tv)
  | Fixcomb (Fun f body) => do
    let tv <- fresh
    let Γ := extend Γ f (.Forall [] tv)
    let (tBody, tB) <- inferExpr Γ body
    addEq tv (tv ->' tB)
    return (.Fix (.Fun f tv tBody (tv ->' tB)) tv, tv)

  | Fix e | Fixcomb e => do
    let (te, t) <- inferExpr Γ e
    return (.Fix te t, t)

  | App e₁ e₂ => do
    let (tE₁, t₁) <- inferExpr Γ e₁
    let (tE₂, t₂) <- inferExpr Γ e₂
    let tv <- fresh
    addEq t₁ (t₂ ->' tv)
    return (.App tE₁ tE₂ tv, tv)

  | Prod' e₁ e₂ => do
    let (tE₁, t₁) <- inferExpr Γ e₁
    let (tE₂, t₂) <- inferExpr Γ e₂
    return (.Prod' tE₁ tE₂ (t₁ ×'' t₂), t₁ ×'' t₂)

  | Cond c t e => do
    let (tcE, tc) <- inferExpr Γ c
    addEq tc tBool
    let (ttE, tt) <- inferExpr Γ t
    let (teE, te) <- inferExpr Γ e
    addEq tt te
    return (.Cond tcE ttE teE tt, tt)

  | Let binds body => inferLet Γ binds body

  | Match discr br => inferMatch Γ discr br

  | Ascribe e ty => do
    let (te, tInfd) <- inferExpr Γ e
    addEq tInfd ty
    return (.Ascribe te ty, ty)

partial def inferLet (Γ : Env) (binds : Array (String × Expr)) (body : Expr)
  : InferC σ (TExpr × MLType) := do
  let startCs <- get <&> (·.cst.length)
  let (recs, nonrecs) := binds.partition $ isRecRhs ∘ Prod.snd

  let (Γrec, recTyVars) <-
    recs.foldlM (init := (Γ, show Std.HashMap String MLType from ∅))
      fun (Γrec, recTyVars) (n, _) => do
        let tv <- fresh
        return (extend Γrec n (.Forall [] tv), recTyVars.insert n tv)

  let tyRec <-
    recs.foldlM (init := #[]) fun tyRec (n, rhs) => do
      let (te, tr) <- inferExpr Γrec rhs
      let tv := recTyVars[n]!
      addEq tv tr
      return tyRec.push (n, te, tr)

  let tyNon <-
    nonrecs.foldlM (init := #[]) fun tyNon (n, rhs) => do
      let (te, tr) <- inferExpr Γrec rhs
      return tyNon.push (n, te, tr)

  let csAll <- get <&> (·.cst)
  let localCs := csAll.take (csAll.length - startCs)
  match solveAll localCs with
  | .error err => throw err
        --    unsolved
  | .ok (sub, _) =>
    let applyAll {α} [Rewritable α] : α -> α := apply sub
    let finalize n te ty Γ bindsTyped :=
      let ty := applyAll ty
      let sch := generalize Γ ty
      (extend Γ n sch, bindsTyped.push (n, sch, applyAll te))
    let (Γ, bindsTyped) :=
      tyRec.foldl (init := (Γ, #[])) fun (Γ, bindsTyped) (n, te, ty) =>
        finalize n te ty Γ bindsTyped
    let (Γ, bindsTyped) :=
      tyNon.foldl (init := (Γ, bindsTyped)) fun (Γ, bindsTyped) (n, te, ty) =>
        finalize n te ty Γ bindsTyped
    let (tBody, tB) <- inferExpr Γ body
    let tB := applyAll tB
    let tBody := applyAll tBody
    return (.Let bindsTyped tBody tB, tB)

partial def inferMatch (Γ : Env) (discr : Array Expr) (br : Array (Array Pattern × Expr))
  : InferC σ (TExpr × MLType) := do
  let (discrTyped, discrTys) <-
    discr.foldlM (init := (#[], #[])) fun (discrTyped, discrTys) e => do
      let (te, t) <- inferExpr Γ e
      return (discrTyped.push te, discrTys.push t)
  let ds := discr.size

  let tv <- fresh

  let mut typedBrs := #[]
  for (ps, rhs) in br do
    let pss := ps.size

    if pss != ds then
      throw (.InvalidPat s!"expected {ds} patterns instead got {pss}")

    let (Γ, localPats) <-
      pss.foldM (init := (Γ, #[])) fun i _ (Γ, localPats) => do
        let expt := discrTys[i]!
        let (Γ, _) <- inferPattern Γ expt ps[i]
        return (Γ, localPats.push ps[i])
    let (tRhs, tR) <- inferExpr Γ rhs
    addEq tR tv
    typedBrs := typedBrs.push (localPats, tRhs)

  let cst <- get <&> (·.cst)
  match solveAll cst with
  | .error err => throw err
  | .ok (sub, _) =>
    let discrTys := discrTys.map $ apply sub
    let (ex, mat, tyCols) := Exhaustive.exhaustWitness Γ discrTys br
    let red := if let some _ := ex then #[] else Exhaustive.redundantRows Γ tyCols mat
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
    appendLog msg
    typedBrs :=
      if red.isEmpty then typedBrs else
      Prod.fst $ typedBrs.size.fold (init := (#[], red, 0)) fun i _ (acc, red, idx) =>
          if red.binSearchContains i (fun m n => m < n) idx
          then (acc, red, idx + 1) else (acc.push typedBrs[i], red, idx)
    return (.Match discrTyped typedBrs tv ex red, tv)

end

end ConstraintInfer

open MLType ConstraintInfer

def runInferConstraintT (e : Expr) (Γ : Env) : Except TypingError (TExpr × Scheme × Logger) :=
  match runEST fun _ => inferExpr Γ e |>.run {} with
  | .error err => .error err
  | .ok ((te, ty), {log,cst,..}) =>
    match solveAll cst with
    | .error err => .error err
    | .ok (sub, _) =>
      let te := Rewritable.apply sub te
      let ty := Rewritable.apply sub ty
      let sch := generalize Γ ty
      .ok (te, sch, log)

def inferToplevelC
  (b : Array TopDecl) (E : Env)
  : Except TypingError (Array TopDeclT × Env × Logger) :=
  b.foldlM (init := (#[], E, "")) fun (acc, E, L) b => do
    match b with
    | .extBind s n sch@(.Forall _ t) => pure $
      (acc.push (.idBind #[(s, sch,TExpr.Var n t)]) ,{E with E := E.E.insert s sch}, L)
    | .idBind group =>
      let exprLet := Expr.Let group .CUnit
      let (te, _, l) <- runInferConstraintT exprLet E
      let (.Let bs _ _) := te | throw (.Impossible "unexpected shape after let inference\n")
      let E := bs.foldl (fun E (n, sc, _) => {E with E := E.E.insert n sc}) E
      return (acc.push (.idBind bs), E, L ++ l)
    | .tyBind ty@{ctors, tycon, param} =>
      return (acc.push (.tyBind ty), ·, L) <| ctors.foldl (init := E) fun {E, tyDecl} (cname, fields, _) =>
        letI s := ctorScheme tycon (param.foldr (List.cons ∘ .mkTV) []) fields
        ⟨E.insert cname s, tyDecl.insert tycon ty⟩
    | .patBind (pat, expr) => do
      let (e, .Forall _ te, l₁) <- runInferConstraintT expr E
      let ((E, _), {log := l₂,..}) <- runEST fun _ => inferPattern E te pat |>.run {}
      let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], .CUnit)]
      let l₃ :=
        if let some ex := ex then
          Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map Pattern.render} are ignored\n"
        else ""
      return (acc.push $ .patBind (pat, e), E, l₁ ++ l₂ ++ l₃)
