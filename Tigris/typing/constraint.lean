import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.exhaust

namespace ConstraintInfer open MLType Rewritable Pattern Expr

inductive Constraint where
  | eq (t₁ t₂ : MLType)
  | pr (eid : Nat) (p : Pred)
deriving Repr

structure CState where
  next                  := nat_lit 0
  nextEv                := nat_lit 0
  cst : List Constraint := []
  log : Logger          := ""
deriving Inhabited

abbrev InferC σ := StateRefT CState (EST TypingError σ)
variable {σ}

@[inline] def fresh : InferC σ MLType := do
  let n <- modifyGet fun ctx@{next,..} => (next, {ctx with next := next + 1})
  s!"?m{n}" |> pure ∘ TVar ∘ .mkTV

@[inline] def freshEvidence (p : Pred) : InferC σ Nat := do
  let n <- modifyGet fun st =>
    (st.nextEv, {st with nextEv := st.nextEv + 1, cst := .pr st.nextEv p :: st.cst})
  return n

@[inline] def addEq (t₁ t₂ : MLType) : InferC σ Unit :=
  modify fun st@{cst,..} => {st with cst := .eq t₁ t₂ :: cst}

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
  | KApp h₁ as₁, KApp h₂ as₂ => do
    if as₁.length != as₂.length then throw (.NoUnify (KApp h₁ as₁) (KApp h₂ as₂)) else
      let headSub <- unify (TVar h₁) (TVar h₂)
      List.foldlM2
        (fun acc x y => (· ∪' acc) <$> unify (apply acc x) (apply acc y))
        headSub as₁ as₂
  | KApp h₁ as₁, TApp h₂ as₂ | TApp h₂ as₂, KApp h₁ as₁ =>
    if as₁.length != as₂.length then throw (.NoUnify (KApp h₁ as₁) (TApp h₂ as₂))
    else do
      let headBind <- bindTV h₁ (TApp h₂ [])
      List.foldlM2
        (fun acc x y => (· ∪' acc) <$> unify (apply acc x) (apply acc y))
        headBind as₁ as₂
  | TApp h₁ as₁, TApp h₂ as₂ =>
    if h₁ != h₂ || as₁.length != as₂.length then throw (.NoUnify (TApp h₁ as₁) (TApp h₂ as₂))
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

def solveAll (cs : List Constraint) : Except TypingError (Subst × List (Nat × Pred)) := do
  cs.foldrM (init := (∅, [])) fun s (sub, pending) =>
    match s with
    | .eq t u => do
      let unis := unify on apply sub
      let s <- unis t u
      return (s ∪' sub, pending)
    | .pr eid p =>
      return (sub, (eid, p.mapArgs (apply sub)) :: pending)

@[inline] def extend (Γ : Env) (x : String) (sch : Scheme) : Env :=
  {Γ with E := Γ.E.insert x sch}

def instantiate : Scheme -> InferC σ (MLType × List (Nat × Pred))
  | .Forall as ps t => do
    let subst : Subst <- as.foldlM (fun a s => a.insert s <$> fresh) ∅
    let t := apply subst t
    let preds <- ps.foldlM (init := []) fun a p => do
      let p := p.mapArgs (apply subst)
      let eid <- freshEvidence p
      return (eid, p) :: a
    return (t, preds)


def generalize (Γ : Env) (t : MLType) (res : List Pred) : Scheme :=
  let envFV := fv Γ
  let tFV   := fv t
  -- predicate free vars
  let pfv := res.foldl (init := (∅ : Std.HashSet TV)) fun acc p =>
    acc ∪ (p.args.foldl (init := ∅) (fun a ty => a ∪ fv ty))
  let allFV := tFV ∪ pfv
  let qs := (allFV \ envFV).toList
  let keep (p : Pred) :=
    let pvs := p.args.foldl (· ∪ fv ·) ∅
    pvs.any $ not ∘ envFV.contains  -- predicate must mention at least one quantified var
  let ctx := res.filter keep |>.rmDup
  normalize (.Forall qs ctx t)

partial def inferPattern (Γ : Env) (expt : MLType) : Pattern -> InferC σ (Env × Array (String × MLType))
  | PWild => return (Γ, #[])
  | PVar x => return (extend Γ x (.Forall [] [] expt), #[(x, expt)])
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
    match Γ.E[cname]? with
    | none => throw (.Undefined cname)
    | some sch =>
      let (ctorTy, _) <- instantiate sch
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
partial def inferExpr (Γ : Env) : Expr -> InferC σ (TExpr × MLType × List Pred)
  | Var x => do
    match Γ.E[x]? with
    | none => throw (.Undefined x)
    | some sch =>
      let (t, preds) <- instantiate sch
      let preds := preds.map Prod.snd
      return (.Var x t, t, preds)

  | CI i => return (.CI i tInt, tInt, [])
  | CS s => return (.CS s tString, tString, [])
  | CB b => return (.CB b tBool, tBool, [])
  | CUnit => return (.CUnit tUnit, tUnit, [])

  | Fun x body => do
    let tv <- fresh
    let Γ := extend Γ x (.Forall [] [] tv)
    let (tBody, tB, pB) <- inferExpr Γ body
    let fnTy := tv ->' tB
    return (.Fun x tv tBody fnTy, fnTy, pB)

  | Fix (Fun f body) => do
    let tv <- fresh
    let Γ := extend Γ f (.Forall [] [] tv)
    let (tBody, tB, pB) <- inferExpr Γ body
    addEq tv tB
    return (.Fix (.Fun f tv tBody (tv ->' tB)) tv, tv, pB)
  | Fixcomb (Fun f body) => do
    let tv <- fresh
    let Γ := extend Γ f (.Forall [] [] tv)
    let (tBody, tB, pB) <- inferExpr Γ body
    addEq tv (tv ->' tB)
    return (.Fix (.Fun f tv tBody (tv ->' tB)) tv, tv, pB)

  | Fix e | Fixcomb e => do
    let (te, t, p) <- inferExpr Γ e
    return (.Fix te t, t, p)

  | App e₁ e₂ => do
    let (tE₁, t₁, p₁) <- inferExpr Γ e₁
    let (tE₂, t₂, p₂) <- inferExpr Γ e₂
    let tv <- fresh
    addEq t₁ (t₂ ->' tv)
    return (.App tE₁ tE₂ tv, tv, p₁ ++ p₂)

  | Prod' e₁ e₂ => do
    let (tE₁, t₁, p₁) <- inferExpr Γ e₁
    let (tE₂, t₂, p₂) <- inferExpr Γ e₂
    return (.Prod' tE₁ tE₂ (t₁ ×'' t₂), t₁ ×'' t₂, p₁ ++ p₂)

  | Cond c t e => do
    let (tcE, tc, pc) <- inferExpr Γ c
    addEq tc tBool
    let (ttE, tt, pt) <- inferExpr Γ t
    let (teE, te, pe) <- inferExpr Γ e
    addEq tt te
    return (.Cond tcE ttE teE tt, tt, pc ++ pt ++ pe)

  | Let binds body => inferLet Γ binds body

  | Match discr br => inferMatch Γ discr br

  | Ascribe e ty => do
    let (e, te, p) <- inferExpr Γ e
    addEq te ty
    return (.Ascribe e ty, ty, p)

partial def inferLet (Γ : Env) (binds : Array (String × Expr)) (body : Expr)
  : InferC σ (TExpr × MLType × List Pred) := do
  let startCs <- get <&> (·.cst.length)
  let (recs, nonrecs) := binds.partition $ isRecRhs ∘ Prod.snd

  let (Γrec, recTyVars) <-
    recs.foldlM (init := (Γ, show Std.HashMap String MLType from ∅))
      fun (Γrec, recTyVars) (n, _) => do
        let tv <- fresh
        return (extend Γrec n (.Forall [] [] tv), recTyVars.insert n tv)

  let tyRec <-
    recs.foldlM (init := #[]) fun tyRec (n, rhs) => do
      let (te, tr, ps) <- inferExpr Γrec rhs
      let tv := recTyVars[n]!
      addEq tv tr
      return tyRec.push (n, te, tr, ps)

  let tyNon <-
    nonrecs.foldlM (init := #[]) fun tyNon (n, rhs) => do
      let (te, tr) <- inferExpr Γrec rhs
      return tyNon.push (n, te, tr)

  let csAll <- get <&> (·.cst)
  let localCs := csAll.take (csAll.length - startCs)
  match solveAll localCs with
  | .error err => throw err
        --    unsolved
  | .ok (sub, wants) =>
    let applyAll {α} [Rewritable α] : α -> α := apply sub
    let residual := wants.map Prod.snd
    let finalize n te ty pl Γ bindsTyped :=
      let ty := applyAll ty
      let sch := generalize Γ ty (pl.map applyAll ++ residual)
      (extend Γ n sch, bindsTyped.push (n, sch, applyAll te))
    let (Γ, bindsTyped) :=
      tyRec.foldl (init := (Γ, #[])) fun (Γ, bindsTyped) (n, te, ty, ps) =>
        finalize n te ty ps Γ bindsTyped
    let (Γ, bindsTyped) :=
      tyNon.foldl (init := (Γ, bindsTyped)) fun (Γ, bindsTyped) (n, te, ty, ps) =>
        finalize n te ty ps Γ bindsTyped
    let (tBody, tB, pB) <- inferExpr Γ body
    let tB := applyAll tB
    let tBody := applyAll tBody
    return (.Let bindsTyped tBody tB, tB, pB)

partial def inferMatch (Γ : Env) (discr : Array Expr) (br : Array (Array Pattern × Expr))
  : InferC σ (TExpr × MLType × List Pred) := do
  let (discrTyped, discrTys, predsAll) <-
    discr.foldlM (init := (#[], #[], [])) fun (discrTyped, discrTys, predsAll) e => do
      let (te, t, p) <- inferExpr Γ e
      return (discrTyped.push te, discrTys.push t, predsAll ++ p)
  let ds := discr.size

  let tv <- fresh

  let (typedBrs, predsAll) <- br.foldlM (init := (#[], predsAll))
    fun (typedBrs, predsAll) (ps, rhs) => do
      let pss := ps.size
      if pss != ds then
        throw (.InvalidPat s!"expected {ds} patterns instead got {pss}")
      let Γ <-
        pss.foldM (init := Γ) fun i _ Γ => Prod.fst <$> inferPattern Γ discrTys[i]! ps[i]
      let (tRhs, tR, pR) <- inferExpr Γ rhs
      addEq tR tv
      return (typedBrs.push (ps, tRhs), predsAll ++ pR)
/-
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
    let typedBrs :=
      if red.isEmpty then typedBrs else
      Prod.fst $ typedBrs.size.fold (init := (#[], red, 0)) fun i _ (acc, red, idx) =>
          if red.binSearchContains i (fun m n => m < n) idx
          then (acc, red, idx + 1) else (acc.push typedBrs[i], red, idx)
-/
    return (.Match discrTyped typedBrs tv none #[], tv, predsAll)

end

end ConstraintInfer

open MLType ConstraintInfer Rewritable

def runInferConstraintT (e : Expr) (Γ : Env) : Except TypingError (TExpr × Scheme × Logger) :=
  match runEST fun _ => inferExpr Γ e |>.run {} with
  | .error err => .error err
  | .ok ((te, ty, preds), {log,cst,..}) =>
    match solveAll cst with
    | .error err => .error err
    | .ok (sub, wants) =>
      let te := apply sub te
      let ty := apply sub ty
      let ps := preds ++ wants.map Prod.snd |>.map (.mapArgs (apply sub))
      let sch := generalize Γ ty ps
      .ok (te, sch, log)

def inferToplevelC
  (b : Array TopDecl) (E : Env)
  : Except TypingError (Array TopDeclT × Env × Logger) :=
  b.foldlM (init := (#[], E, "")) fun (acc, E, L) b => do
    match b with
    | .extBind s n sch => pure $
      let sch := normalize sch
      (acc.push (.idBind #[(s, sch, .Var n sch.body)]) ,{E with E := E.E.insert s sch}, L)
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
      let (e, .Forall _ ps te, l₁) <- runInferConstraintT expr E
      let l :=
        if !ps.isEmpty then
          Logging.warn
            s!"pattern binding does not support addition of constraints"
        else ""
      let ((E, _), {log := l₂,..}) <- runEST fun _ => inferPattern E te pat |>.run {}
      let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
      let l₃ :=
        if let some ex := ex then
          Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map Pattern.render} are ignored\n"
        else ""
      return (acc.push $ .patBind (pat, e), E, L ++ l₁ ++ l ++ l₂ ++ l₃)
