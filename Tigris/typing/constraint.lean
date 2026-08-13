import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.exhaust
import Tigris.typing.scc

namespace ConstraintInfer open MLType Rewritable Pattern Expr

inductive Constraint where
  | eq (t₁ t₂ : MLType)
  | pr (eid : Nat) (p : Pred)
deriving Repr

abbrev Rigids := Std.TreeSet TV

structure CState where
  next                  := nat_lit 0
  nextEv                := nat_lit 0
  cst : List Constraint := []
  log : Logger          := ""
  rTV : Rigids          := ∅
  rTVs : List Rigids    := []
deriving Inhabited

abbrev InferC σ := StateRefT CState (EST TypingError σ)
local instance : MonadLift (Except TypingError) (InferC σ) where
  monadLift
  | .error e => throw e
  | .ok res => return res
variable {σ}

@[inline] def fresh : InferC σ MLType := do
  let n <- modifyGet fun ctx@{next,..} => (next, {ctx with next := next + 1})
  s!"?m.{n}" |> pure ∘ TVar ∘ .mkTV

@[inline] def freshEvidence (p : Pred) : InferC σ Nat := do
  let n <- modifyGet fun st =>
    (st.nextEv, {st with nextEv := st.nextEv + 1, cst := .pr st.nextEv p :: st.cst})
  return n

def elimForall : MLType -> InferC σ MLType
  | .TSch (.Forall vs ps t) => do
    let sub <- vs.foldlM (.insert · · <$> fresh) ∅
    for p in ps do
      () <$ freshEvidence (apply sub p)
    return apply sub t
  | t => return t

@[inline] def addEq (t₁ t₂ : MLType) : InferC σ Unit := do
  modify fun st@{cst,..} => {st with cst := .eq t₁ t₂ :: cst}

@[inline] def appendLog (s : String) : InferC σ Unit :=
  modify fun st@{log,..} => {st with log := log ++ s}

@[inline] def pushRigid (vs : List TV) : InferC σ Unit :=
  let s := vs.foldl .insert ∅
  modify fun st => {st with rTV := st.rTV ∪ s, rTVs := s :: st.rTVs}

@[inline] def popRigid : InferC σ Unit := do
  modify fun st =>
    match st.rTVs with
    | s :: rest => {st with rTV := st.rTV \ s, rTVs := rest}
    | []        => st

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
  | TCon a, TCon b =>
    if a == b then return ∅
    else throw (.NoUnify (TCon a) (TCon b))
  | MLType.TyLam x₁ b₁, MLType.TyLam x₂ b₂ => do
    -- α-equiv.
    let renameSub : Subst := (∅ : Subst).insert x₂ (TVar x₁)
    unify b₁ (apply renameSub b₂)
  | t₁@(TApp h₁ as₁), t₂@(TApp h₂ as₂) => do
    -- Claude: Spine unification with peeling. Length-equalize from the right so the
    -- shorter spine is matched against a prefix of the longer one's head.
    let n₁ := as₁.length
    let n₂ := as₂.length
    if n₁ == n₂ then
      let headSub <- unify h₁ h₂
      List.foldlM2
        (fun acc x y => (· ∪' acc) <$> unify (apply acc x) (apply acc y))
        headSub as₁ as₂
    else if n₁ > n₂ then
      -- Claude: Length-equalize: fuse the prefix of `as₁` into the head and unify
      -- the resulting "fused head" against `h₂`, then zip the suffix args
      -- with `as₂`. Do NOT rebuild the LHS via `mkApp` -- that re-flattens
      -- and recurses on the same input, looping forever.
      let d := n₁ - n₂
      let (as₁, as₁') := as₁.splitAt d
      let h₁' := mkApp h₁ as₁
      (do let headSub <- unify h₁' h₂
          List.foldlM2
            (fun acc x y => (· ∪' acc) <$> unify (apply acc x) (apply acc y))
            headSub as₁' as₂)
        <|> throw (.NoUnify t₁ t₂)
    else unify t₂ t₁
  | t₁@(TApp h₁ as₁), t₂ => do
    -- Claude: Pattern-fragment: head is a TVar and args are skolems/rigids -> bind the
    -- head to a TyLam abstraction of t₂. Otherwise, if there are zero args,
    -- unify against the head.
    if as₁.isEmpty then unify h₁ t₂
    else
      match h₁ with
      | TVar v =>
        -- requires args to be rigid in t₂.
        let binders : List TV <-
          as₁.foldrM (init := ([] : List TV)) fun a acc =>
            match a with
            | TVar w => pure (w :: acc)
            | TCon h => if h.startsWith "?sk." then pure (.mkTV (h.drop 4 |>.toString) :: acc)
                        else throw (.NoUnify t₁ t₂)
            | _ => throw (.NoUnify t₁ t₂)
        let body := binders.foldr (init := t₂) fun b acc => .TyLam b acc
        bindTV v body
      | _ => throw (.NoUnify t₁ t₂)
  | t₁, t₂@(TApp ..) => unify t₂ t₁
  | ts₁@(.TSch (.Forall tvs₁ ps₁ t₁)), ts₂@(.TSch (.Forall tvs₂ ps₂ t₂)) => do
    if ps₁.length != ps₂.length || tvs₁.length != tvs₂.length then
      throw (.NoUnify ts₁ ts₂)
    let renameSub : Subst := List.foldl2 (·.insert · $ .TVar ·) ∅ tvs₂ tvs₁
    let ps₂ := apply renameSub ps₂
    if ps₁ != ps₂ then throw $ .NoUnify ts₁ ts₂
    unify t₁ (apply renameSub t₂)
  | t, u =>
    throw (.NoUnify t u)

def solveAll (cs : List Constraint) : Except TypingError (Subst × List (Nat × Pred)) := do
  cs.foldrM (init := (∅, [])) fun s (sub, pending) =>
    match s with
    | .eq t u => do
      unify (apply sub t) (apply sub u) <&> (· ∪' sub, pending)
    | .pr eid p =>
      return (sub, (eid, apply sub p) :: pending)

@[inline] def mkSkol v := MLType.TCon $ "?sk." ++ TV.toStr v

partial def sk? : MLType -> Bool
  | .TCon h => h.startsWith "?sk"
  | a ->' b | a ×'' b => sk? a || sk? b
  | .TApp h as => sk? h || as.any sk?
  | .TyLam _ body => sk? body
  | .TSch (.Forall _ _ t) => sk? t
  | .TVar _ => false

def skolemizeTSch : MLType -> Except TypingError MLType
  | .TSch (.Forall tvs _ t) =>
    let sub : Subst := tvs.foldl (fun s v => s.insert v (mkSkol v)) ∅
    return apply sub t
  | _ => throw (.Impossible "skolemizeTSch: expected TSch")

@[inline] def extend (Γ : Env) (x : String) (sch : Scheme) : Env :=
  {Γ with E := Γ.E.insert x sch}

def instantiate : Scheme -> InferC σ (MLType × List (Nat × Pred))
  | .Forall as ps t => do
    let subst : Subst <- as.foldlM (fun a s => a.insert s <$> fresh) ∅
    let t := apply subst t
    let preds <- ps.foldlM (init := []) fun a p => do
      let p := apply subst p
      let eid <- freshEvidence p
      return (eid, p) :: a
    return (t, preds)

def generalize (Γ : Env) (t : MLType) (res : List Pred) : Scheme :=
  let envFV := fv Γ
  let tFV   := fv t
  -- predicate free vars
  let pfv := res.foldl (· ∪ ·.args.foldl (· ∪ fv ·) ∅) ∅
  let allFV := tFV ∪ pfv
  let qs := (allFV \ envFV).toList
  let keep (p : Pred) :=
  -- Keep a predicate only if it mentions at least one quantified variable
  -- that also appears in the result type (otherwise it is vacuous / removable).
    let pvs := p.args.foldl (· ∪ fv ·) ∅
    let qVars := pvs.filter $ not ∘ envFV.contains
    !(qVars.filter tFV.contains).isEmpty
  let ctx := res.filter keep |>.rmDup
  .Forall qs ctx t

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
        | .TSch (.Forall _ _ t) => peel acc t
        | a ->' b               => peel (acc.push a) b
        | r                     => (acc, r)
      let (argTys, resTy) := peel #[] ctorTy
      -- check against declared arity in `TyDecl`
      let declaredArity? : Option Nat :=
        Γ.tyDecl.valuesArray.findSome? fun td =>
          td.ctors.findSome? fun (n, _, ar) =>
            if n == cname then some ar else none
      let expectedArity := declaredArity?.getD argTys.size
      if expectedArity != args.size then
        throw $ .InvalidPat
          s!"constructor {cname} expects {expectedArity} argument(s), \
             pattern provides {args.size}"
      if expectedArity != argTys.size then -- should not happen
        throw $ .Impossible
          s!"constructor {cname}: declared arity {expectedArity} disagrees \
             with arrow-peeled arity {argTys.size} from its scheme"
      addEq expt resTy
      Array.foldlM2 (fun (Γ, bound) ty arg => do
        let (Γ, bs) <- inferPattern Γ ty arg
        return (Γ, bound ++ bs))
        (Γ, #[])
        argTys args

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
    let tv@(TVar tv') <- fresh | unreachable!
    let Γ := extend Γ x (.Forall [] [] tv)
    pushRigid [tv']
    let (tBody, tB, pB) <- inferExpr Γ body
    popRigid
    let fnTy := tv ->' tB
    return (.Fun x tv tBody fnTy, fnTy, pB)

  | Fix (Fun f body) | Fixcomb (Fun f body) => do
    let tv <- fresh
    let Γ := extend Γ f (.Forall [] [] tv)
    let (tBody, tB, pB) <- inferExpr Γ body
    addEq tv tB
    return (.Fix (.Fun f tv tBody (tv ->' tB)) tv, tv, pB)

  | Fix e => do
    let (te, t, p) <- inferExpr Γ e
    return (.Fix te t, t, p)
  | Fixcomb e => do
    let (te, t, p) <- inferExpr Γ e
    let tv <- fresh
    addEq t (tv ->' tv)
    return (.Fix te tv, tv, p)

  | App e₁ e₂ => do
    let (tE₁, t₁, p₁) <- inferExpr Γ e₁
    let t₁ <- elimForall t₁
    match t₁ with
    | a@(.TSch $ .Forall ..) ->' b =>
      let (tE₂, t₂, p₂) <- inferExpr Γ e₂
      let t₂ <- elimForall t₂
      let aSk <- skolemizeTSch a
      addEq t₂ aSk
      return (.App tE₁ tE₂ b, b, p₁ ++ p₂)
    | _ =>
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

  | Ascribe e sch@(.TSch $ .Forall vs ps t) => do
    let (te, teTy, preds) <- inferExpr Γ e
    let teMono <- elimForall teTy
    let sub <- vs.foldlM (Std.TreeMap.insert · · <$> fresh) (∅ : Subst)
    let inst := apply sub t

    let (cs0, rigid) <- get <&> fun st => (st.cst, st.rTV)
    match solveAll $ .eq teMono inst :: cs0 with
    | .error _ => throw (.NoUnify teMono inst)
    | .ok (sub, _) =>
      let bad :=
        sub.any (fun tv rhs =>
          tv ∈ rigid && rhs != MLType.TVar tv)
      if bad then throw (.NoUnify teMono inst)
      else addEq teMono inst

    for p in ps do
      () <$ freshEvidence (apply sub p)

    let skTy <- skolemizeTSch sch
    solveAll (.eq teMono skTy :: cs0) $> (.Ascribe te sch, inst, preds)

  | Ascribe e ty => do
    let (e, te, p) <- inferExpr Γ e
    addEq te ty
    return (.Ascribe e ty, ty, p)

/--
infers/checks/generalizes a group in topo order from dependency analysis.

Previously we used a overapproximation heuristics that
transform every non-Fun head RHS to a normal let-binding,
which is dumb and has a fixed order, leading to problems.

Consider the example in `examples/where.tig`. main and boxedAdd are
in the same let group, therefore when typechecking main, boxedAdd is
undefined since `where` group binding are inserted before main.
And the fact that boxedAdd can reference (^) and (`on`) really is
because they are Fun-headed, therefore belong in the rec group,
which, was processed first in the previous version of `inferLet`.
-/
partial def inferGroup (Γ : Env) (binds : Array (String × Expr))
  : InferC σ (Env × Array (String × Scheme × TExpr)) := do
  let startCs <- get <&> (·.cst.length)
  let (recs, nonrecs) := binds.partition $ isRecRhs ∘ Prod.snd
  let (Γrec, recTyVars) <-
    recs.foldlM (init := (Γ, show Std.HashMap String MLType from ∅))
      fun (Γrec, recTyVars) (n, _) => do
        let tv <- fresh
        return (extend Γrec n (.Forall [] [] tv), recTyVars.insert n tv)

  let tyRec <-
    recs.foldlM (init := #[]) fun tyRec (n, rhs) => do
      let evStart <- get <&> (·.nextEv)
      let (te, tr, ps) <- inferExpr Γrec rhs
      let evEnd <- get <&> (·.nextEv)
      let tv := recTyVars[n]!
      addEq tv tr
      return tyRec.push (n, te, tr, ps, evStart, evEnd)

  let tyNon <-
    nonrecs.foldlM (init := #[]) fun tyNon (n, rhs) => do
      let evStart <- get <&> (·.nextEv)
      let (te, tr, ps) <- inferExpr Γrec rhs
      let evEnd <- get <&> (·.nextEv)
      return tyNon.push (n, te, tr, ps, evStart, evEnd)

  let csAll <- get <&> (·.cst)
  let localCs := csAll.take (csAll.length - startCs)
  match solveAll localCs with
  | .error err => throw err
  | .ok (sub, wants) =>
    let applyAll {α} [Rewritable α] : α -> α := apply sub
    let predsFor evStart evEnd :=
      wants.foldr (init := []) fun (eid, p) acc =>
        if evStart <= eid && eid < evEnd then (applyAll p) :: acc else acc
    let gen := fun (Γ, bindsTyped) (n, te, ty, ps, l, r) =>
      let ty := applyAll ty
      let sch := generalize Γ ty (applyAll ps ++ predsFor l r)
      (extend Γ n sch, bindsTyped.push (n, sch, applyAll te))
    return (tyNon.foldl (init := tyRec.foldl (init := (Γ, #[])) gen) gen)

partial def inferLet (Γ : Env) (binds : Array (String × Expr)) (body : Expr)
  : InferC σ (TExpr × MLType × List Pred) := do
  -- process strongly-connected components in dependency order; flat, topo-ordered
  let (Γ, bindsTyped) <-
    (depOrder binds).foldlM (init := (Γ, #[])) fun (Γ, acc) grp => do
      let (Γ, bt) <- inferGroup Γ grp
      return (Γ, acc ++ bt)
  let (tBody, tB, pB) <- inferExpr Γ body
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
      let (Γ, bound) <-
        pss.foldM (init := (Γ, #[])) fun i _ (Γacc, accBs) => do
          let (Γnext, bs) <- inferPattern Γacc discrTys[i]! ps[i]
          return (Γnext, accBs ++ bs)
      let rigidsBr : List TV :=
        bound.foldl (init := []) fun acc (_, ty) =>
          fv ty |>.foldr (fun s a => if s.tv? then s :: a else a) acc
      pushRigid rigidsBr
--      let Γ <-
--        pss.foldM (init := Γ)
--          fun i _ Γ => Prod.fst <$> inferPattern Γ discrTys[i]! ps[i]
      let (tRhs, tR, pR) <- inferExpr Γ rhs
      popRigid
      addEq tR tv
      return (typedBrs.push (ps, tRhs), predsAll ++ pR)
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
      let ps := preds ++ wants.map (apply sub ∘ Prod.snd)
      let sch := generalize Γ ty ps
      .ok (te, sch, log)

namespace Helper

mutual
partial def normHK : MLType -> MLType
  | .TApp h args =>
    let h' :=
      match h with
      | .TCon s => if s.isLowerInit then .TVar (.mkTV s) else .TCon s
      | other => normHK other
    MLType.mkApp h' (args.map normHK)
  | .TCon s =>
    if s.isLowerInit then .TVar (.mkTV s) else .TCon s
  | .TyLam x body => .TyLam x (normHK body)
  | a ->' b => normHK a ->' normHK b
  | a ×'' b => normHK a ×'' normHK b
  | t => t

partial def normHKPred := Pred.mapArgs normHK
end
def methodScheme (cls : Symbol) (param : Array $ String × Kind) (mty : MLType) : Scheme :=
  let binders := param.foldr (List.cons ∘ TV.mkTV ∘ Prod.fst) []
  let args    := binders.map TVar
  .Forall binders [⟨cls, args⟩] (normHK mty)

private def instQuantifiers (headArgs : List MLType) (ctx : List Pred) : List TV :=
  let (headArgs, ctx) := (headArgs.map normHK, ctx.map normHKPred)
  fv headArgs ∪ fv ctx |>.toList

private def orderInstanceMethods
  (ci : ClassInfo)
  (methods : Array (String × Expr))
  : Except TypingError (Array $ MethodInfo × Expr) := do
  let mp : Std.HashMap String Expr := methods.foldl (fun m (n, e) => m.insert n e) ∅
  ci.methods.foldlM (init := #[]) fun a m =>
    if let some e := mp[m.mname]? then
      return a.push (m, e)
    else throw $ .Undefined s!"missing method {m.mname} for instance of {ci.cname}\n"

private def paramSubst (ci : ClassInfo) (headArgs : List MLType) : Subst :=
  let binders := ci.params.foldr (List.cons ∘ .mkTV ∘ Prod.fst) []
  List.foldl2 .insert ∅ binders headArgs

private def buildInstProvider
  (ci : ClassInfo) (orderedMethods : Array (MethodInfo × Expr))
  (headArgs : List MLType)
  : Expr :=
  let sub := paramSubst ci headArgs
  let dictCore :=
    orderedMethods.foldl (fun acc (m, e) => .App acc $ .Ascribe e (apply sub m.mty)) (.Var ci.ctorName)
  .Ascribe dictCore (MLType.mkApp (TCon ci.cname) headArgs)
end Helper

open Helper
in @[inline] private def methodSchemes (ci : ClassInfo) : Array (String × Scheme) :=
  ci.methods.map fun m => (m.mname, methodScheme ci.cname ci.params m.mty)
in private def inferInstanceDecl (E : Env) (ci : ClassInfo) (existingCount : Nat)
  : InstanceDecl -> Except TypingError (String × Scheme × TExpr × Logger × InstanceInfo)
  | {args, methods, ctxPreds,..} => do
    let iname := s!"i_{ci.cname}_{existingCount}"
    let ordered <- orderInstanceMethods ci methods
    let rigidTVs := fv args ∪ fv ctxPreds
    let rigidSub : Subst := rigidTVs.foldl (fun s v => s.insert v (mkSkol v)) ∅
    let argsSk := apply rigidSub args
    let rawBody := buildInstProvider ci ordered argsSk
    let (typedBody, inferredSch, l) <- runInferConstraintT rawBody E
    let (.Forall _ _ infRes) := inferredSch
    let wantHeadSk := MLType.mkApp (TCon ci.cname) argsSk
    match unify infRes wantHeadSk with
    | .error _ => throw (.NoUnify infRes wantHeadSk)
    | .ok sub =>
      let detectedSpecialized :=
        args.any fun
          | MLType.TVar v | MLType.TApp (MLType.TVar v) [] =>
            match apply sub (MLType.TVar v) with
            | MLType.TVar v' => v' != v
            | _ => true
          | _ => false
      if detectedSpecialized then
        throw $ .NoSynthesize s!"{Pred.mk ci.cname args}: body is too specific. Supply a specialized scheme instead.\n"

      let declaredCtx := apply sub ctxPreds |>.map normHKPred
      let qs := instQuantifiers args declaredCtx
      let bodyTy := MLType.mkApp (TCon ci.cname) args
      let finalSch := .Forall qs declaredCtx (normHK bodyTy)
      let typedBody := typedBody |>.mapTypes (normHK ∘ unSkolem) (unSkolemS)
      return ⟨iname, finalSch, typedBody, l, iname, ci.cname, args, ctxPreds⟩

def inferToplevelC
  (b : Array TopDecl) (E : Env)
  : Except TypingError (Array TopDeclT × Env × Logger) :=
  b.foldlM (init := (#[], E, "")) fun (acc, E, L) b => do
    match b with
    | .extBind s n sch => pure $
      (acc.push (.idBind #[(s, sch, .Var n sch.body)]) ,{E with E := E.E.insert s sch}, L)
    | .idBind group =>
      let exprLet := Expr.Let group .CUnit
      let (.Let bs _ _, _, l) <- runInferConstraintT exprLet E | throw (.Impossible "unexpected shape after let inference\n")
      let (E, bs) := bs.foldl
        (fun (E, bs) (n, sc, te) =>
          ( {E with E := E.E.insert n sc}
          , bs.push (n, sc, te)))
        (E, #[])
      return (acc.push (.idBind bs), E, L ++ l)
    | .tyBind ty@{ctors, tycon, param, cls?} =>
      let (acc, E) :=
        ctors.foldl (init := (acc, E)) fun (acc, {E, tyDecl, clsInfo, instInfo}) (cname, fields, _) =>
          let s := ctorScheme tycon (param.foldr (List.cons ∘ .mkTV ∘ Prod.fst) []) fields
          if h : cls? ∧ ctors.size ≠ 0 then
            let methods : Array MethodInfo := Prod.fst $ ctors[0].snd.fst.foldl (init := (#[], 0))
                fun (a, i) (mname, mty) =>
                  (a.push ⟨mname, mty, i⟩, i + 1)
            let cls := ⟨tycon, cname, param, methods⟩
            let E := methodSchemes cls |>.foldl (fun E (n, sch) => E.insert n sch) E
            ( acc
            , ⟨E.insert cname s, tyDecl.insert tycon ty, clsInfo.insert tycon cls, instInfo⟩)
          else (acc, ⟨E.insert cname s, tyDecl.insert tycon ty, clsInfo, instInfo⟩)
      return (acc.push (.tyBind ty), E, L)
    | .patBind (pat, expr) => do
      let (e, sch@(.Forall _ ps te), l₁) <- runInferConstraintT expr E
      let l :=
        if !ps.isEmpty then
          Logging.warn
            s!"pattern binding does not support addition of constraints (it is dropped.)\n"
        else ""
      let ((E, b), {log := l₂, cst,..}) <- runEST fun _ => inferPattern E te pat |>.run {}
      let (subst, _) <- solveAll cst
      let E := apply subst E
      let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
      let l₃ :=
        if let some ex := ex then
          Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map Pattern.toStr} are ignored\n"
        else ""
      return (acc.push $ .patBind (pat, sch, e), E, L ++ l₁ ++ l ++ l₂ ++ l₃)
    | .instBind inst => do
      let (some ci) := E.clsInfo[inst.cname]?
        | throw (.Undefined inst.cname)
      let existing := E.instInfo.getD ci.cname #[]
      let (iname, sch, te, l, info) <- inferInstanceDecl E ci existing.size inst
      let instInfo := E.instInfo.alter ci.cname $ some ∘
        fun
        | some arr => arr.push info
        | none => #[info]
      return ( acc.push $ .idBind #[(iname, sch, te)]
             , {E with E := E.E.insert iname sch, instInfo}
             , L ++ l)
