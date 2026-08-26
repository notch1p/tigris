import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.exhaust
import Tigris.typing.scc
import Tigris.typing.kinds
import Tigris.typing.freshen

namespace ConstraintInfer open MLType Rewritable Pattern Expr

inductive Constraint where
  | eq (t₁ t₂ : MLType)
  | pr (eid : Nat) (p : Pred)
deriving Repr
instance : Rewritable Constraint where
  fv
  | .eq t₁ t₂ => fv t₁ ∪ fv t₂
  | .pr _ p => fv p
  apply s
  | .eq t₁ t₂ => .eq (apply s t₁) (apply s t₂)
  | .pr e p   => .pr e (apply s p)
open Std.Format Std.ToFormat in
instance : Std.ToFormat Constraint where
  format
  | .eq t₁ t₂ => group $ format t₁ ++ " ~ " ++ format t₂
  | .pr eid p => group $ paren (format p) ++ "@" ++ format eid
in instance : Std.ToFormat $ List (Nat × Pred) where
  format xs :=
    sbracket (xs.foldr (fun (idx, pred) acc => Std.Format.paren (format pred) ++ "@" ++ format idx ++ "," ++ line ++ acc) .nil )
in instance : Std.ToFormat Subst where
  format xs :=
    sbracket (xs.foldl (fun acc tv ty => acc ++ Std.Format.paren (format tv ++ " ↦ " ++ format ty) ++ "," ++ line ) nil)
abbrev Rigids := Std.TreeSet TV

structure CState where
  next                  := nat_lit 0
  nextEv                := nat_lit 0
  cst : List Constraint := []
  log : Logger          := ""
  rTV : Rigids          := ∅
  rTVs : List Rigids    := []
  ke  : KindEnv         := ∅
deriving Inhabited

/-- wanted-pool solve result -/
structure SolveResult where
  sub      : Subst
  ke       : KindEnv
  next     : Nat
  wants    : List (Nat × Pred)       -- leftover preds for generalization
  leftover : List (MLType × MLType)  -- leftover eqs
deriving Inhabited

abbrev InferC σ := StateRefT CState (EST TypingError σ)
local instance : MonadLift (Except TypingError) (InferC σ) where
  monadLift
  | .error e => throw e
  | .ok res => return res
variable {σ}

@[inline] def fresh : InferC σ MLType := do
  let n <- modifyGet fun ctx@{next,..} => (next, {ctx with next := next + 1})
  pure $ TVar (.mv n)

@[inline] def freshEvidence (p : Pred) : InferC σ Nat := do
  let n <- modifyGet fun st =>
    (st.nextEv, {st with nextEv := st.nextEv + 1, cst := .pr st.nextEv p :: st.cst})
  return n

/-- rule Inst1, implements |-ᵢ in inference mode. See also comments above checkExpr.
binds the scheme's quantified vars to fresh mvs, registers the ctx preds as
evidence, and returns the instantiated body plus the instantiation args for Var nodes.

elimForall is the same as instantiate, but for outermost TSch i.e. polytype.
Together they deal with the two shapes a scheme takes at inference sites.

Previously they are defined independently but there's no reason to do so.
Now it is clearer and from a theoretic perspective they both reduce to Inst1.
-/
def instantiate : Scheme -> InferC σ (MLType × List MLType × List (Nat × Pred))
  | .Forall as ps t => do
    let subst : Subst <- as.foldlM (fun a s => a.insert s <$> fresh) ∅
    let t := apply subst t
    -- collect instantiation args for the Var node
    let tArgs := as.map (apply subst ∘ TVar)
    let preds <- ps.foldlM (init := []) fun a p => do
      let p := apply subst p
      let eid <- freshEvidence p
      return (eid, p) :: a
    return (t, tArgs, preds)

def elimForall : MLType -> InferC σ MLType
  | .TSch sch => Prod.fst <$> instantiate sch
  | t => return t

@[inline] def addEq (t₁ t₂ : MLType) : InferC σ Unit := do
  modify fun st@{cst,..} => {st with cst := .eq t₁ t₂ :: cst}

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
  else
    match a with
    | .sk _ =>
      -- rigidity says that only a bindable MV (anything execpt skolems)
      -- on the RHS may absorb LHS (Obviously, RHS needs to be a TV first).
      -- previsouly skolems become TCons which rejects in the unification engine
      -- which is a rough hack.
      match t with
      | .TVar w =>
        match w with
        | .sk _ => throw (.NoUnify (TVar a) t)
        | _ => pure ({(w, TVar a)}) -- fv (TVar a) is erased for skolems: no occurs
      | _ => throw (.NoUnify (TVar a) t)
    | _ =>
      if a ∈ fv t then throw (.Duplicates a t)
      else pure {(a, t)}

partial def unifyGo (ke : KindEnv) (n : Nat) : MLType -> MLType -> Except TypingError (Subst × KindEnv × Nat)
  | t₁ ×'' t₂, u₁ ×'' u₂
  | t₁ ->' t₂, u₁ ->' u₂ => do
    let (s₁, ke, n) <- unifyGo ke n t₁ u₁
    let (s₂, ke, n) <- unifyGo ke n (apply s₁ t₂) (apply s₁ u₂)
    return (s₂ ∪' s₁, ke, n)
  | TVar a, t | t, TVar a => (·, ke, n) <$> bindTV a t
  | TCon a, TCon b => if a == b then return (∅, ke, n) else throw (.NoUnify (TCon a) (TCon b))
  | TyLam x₁ b₁, TyLam x₂ b₂ =>
    -- α-equiv.
    let renameSub : Subst := {(x₂, (TVar x₁))}
    unifyGo ke n b₁ (apply renameSub b₂)
  | t₁@(TApp h₁ as₁), t₂@(TApp h₂ as₂) => do
    -- Claude: Spine unification with peeling. Length-equalize from the right so the
    -- shorter spine is matched against a prefix of the longer one's head.
    let m₁ := as₁.length
    let m₂ := as₂.length
    if m₁ == m₂ then
      let (headSub, ke, n) <- unifyGo ke n h₁ h₂
      List.foldlM2
        (fun (acc, ke, n) x y =>
          (fun (s, ke, n) => (s ∪' acc, ke, n)) <$> unifyGo ke n (apply acc x) (apply acc y))
        (headSub, ke, n)
        as₁ as₂
    else if m₁ > m₂ then
      -- Claude: Length-equalize: fuse the prefix of `as₁` into the head and unify
      -- the resulting "fused head" against `h₂`, then zip the suffix args
      -- with `as₂`. Do NOT rebuild the LHS via `mkApp` -- that re-flattens
      -- and recurses on the same input, looping forever.
      let d := m₁ - m₂
      let (as₁, as₁') := as₁.splitAt d
      let h₁' := mkApp h₁ as₁
      (do let (headSub, ke, n) <- unifyGo ke n h₁' h₂
          List.foldlM2
            (fun (acc, ke, n) x y =>
              (fun (s, ke, n) => (s ∪' acc, ke, n)) <$> unifyGo ke n (apply acc x) (apply acc y))
            (headSub, ke, n) as₁' as₂)
        <|> throw (.NoUnify t₁ t₂)
    else unifyGo ke n t₂ t₁

    /- we now solve ?m args≠[] ~ t only after the tycon ?m is computed from
       the instance rule (satisfying queued pred & deferred eq & unique match)
       or a literal MV binding (then through bindTV it's trivial).

       This is mostly GHC-like first-order unification instead of
       the higher-order pattern fragment we had before.

       See examples/typeclass0.tig for the reason (it's unsound).
       Note: ``inert'' in GHC jargon. It falls through the last NoUnify case but
       is not actually a failure but returns to the wanted pool. -/
  | TApp h₁ [], t₂ => unifyGo ke n h₁ t₂
  | t₁, t₂@(TApp ..) => unifyGo ke n t₂ t₁
  | ts₁@(.TSch (.Forall tvs₁ ps₁ t₁)), ts₂@(.TSch (.Forall tvs₂ ps₂ t₂)) => do
    if ps₁.length != ps₂.length || tvs₁.length != tvs₂.length then throw (.NoUnify ts₁ ts₂)
    let renameSub : Subst := List.foldl2 (·.insert · $ .TVar ·) ∅ tvs₂ tvs₁
    let ps₂ := apply renameSub ps₂
    if ps₁ != ps₂ then throw $ .NoUnify ts₁ ts₂
    unifyGo ke n t₁ (apply renameSub t₂)
  | ts₁@(.TSch (.Forall vs ps body)), t₂ | t₂, ts₁@(.TSch (.Forall vs ps body)) =>
    /- Another Inst1 in the wanted pool. This allows for first-class, _unannotated_
       rank-n passing where a rank-n function hides behind a metavariable. e.g.

        let g x f : Int -> (∀ a, a -> a) -> Int = f x
            apply f x = f x
         in apply g 1 fun x => x -- use site

       We would need to unify ∀a, a -> a ~ ?m -> ?m at usesite, that is, rule Inst1 from |-dsk.
       Skolemizing would be unsound since it rejects ∀a, a -> a ~ ?m -> Int where a should := Int
       but that is not possible with skolems since they can't bind.
       For this reason we need to thread the counter through unification
       and all of its references.

       This allows the above equation to be solved, see also App branch.
       Interestingly, GHC rejects the above for some reason I don't know of.
       Maybe semantic discipline concerns? --

        Recall that an equivalence is an equality solvable with unification.
        However, ∀α, α -> α = τ has no solution for a fixed mono τ. It is only
        derivable using |-ᵢ, which is not equational (relational in fact).
        We nevertheless chose to keep it given that it is sound,
        though not the job unification should be doing.

       Though the main motivation for removing this branch is that
       counter threading is ugly. -/
    if ps.isEmpty then
      let (sub, n) := vs.foldl (fun (s, n) v => (s.insert v (.TVar (.mv n)), n + 1)) (∅, n)
      unifyGo ke n (apply sub body) t₂
    else throw (.NoUnify ts₁ t₂)
  | t, u => throw (.NoUnify t u)

/--
check and unifying for kind first then structural unifying MLType.

an important assumption worth noting is that subterms of well-kind types are well kinded.
therefore it suffices to check kinds at toplevel and pattern unification need not
to be mutually recursive with it. Faster.
-/
def unify (ke : KindEnv) (n : Nat) : MLType -> MLType -> Except TypingError (Subst × KindEnv × Nat) :=
  fun t₁ t₂ => do
    let (ke, k₁) <- kindOf ke t₁
    let (ke, k₂) <- kindOf ke t₂
    let ke <- KindEnv.kindUnify ke k₁ k₂
    unifyGo ke n (ηNF t₁) (ηNF t₂)

def unifyHead (ke : KindEnv) (n : Nat) (goalArgs : List MLType) (instArgs : List MLType) : Except TypingError (Subst × KindEnv × Nat) := do
  if goalArgs.length != instArgs.length then
    throw (.NoUnify (mkApp (MLType.TCon "_goal") goalArgs)
                    (mkApp (MLType.TCon "_inst") instArgs))
  else
    List.foldlM2
      (fun (s, ke, n) g i =>
        (fun (s', ke, n) => (s' ∪' s, ke, n)) <$> unify ke n (apply s g) (apply s i))
      ((∅ : Subst), ke, n)
      goalArgs instArgs

/-- refines 1 pred if there exists exactly 1 matching instance.
Returns on multiple matches to solveAll which, in this case,
does nothing and let SysF elab paas handles it. -/
def refineStep (env : Env) (ke : KindEnv) (n : Nat) (p : Pred) : Except TypingError (Subst × KindEnv × Nat × List Pred) := do
  let some insts := env.instInfo[p.cls]?
    | throw $ .NoSynthesize s!"{p}: no matching instance found\n"

  let found : Option (Subst × KindEnv × Nat × List Pred) <- insts.foldrM (init := none) fun info found => do

    let qs := info.args.foldl (· ∪ fv ·) ∅ ∪ info.ctx.foldl (· ∪ fvP ·) ∅
    let (ren, _) : Subst × Nat := qs.foldl (init := (∅, 0)) fun (s, i) q =>
      (s.insert q $ .TVar $ .inst n i, i + 1)

    match unifyHead ke n p.args (apply ren info.args) with
    | .error _ => return none
    | .ok (sub, ke, n) =>
      match found with
      | some _ => throw $ .Ambiguous s!"{p}: multiple instances match\n" -- return to solveAll.
      | none => return some (sub, ke, n, apply (sub ∪' ren) info.ctx)

  match found with
  | some r => return r
  | none => throw $ .NoSynthesize s!"{p}: no matching instance found\n"

/--
Solve equations and refine pending class predicates, similar to GHC's
wanted-pool (goals, really) model of interleaving solving/resolution.
each round retries the deferred (previsouly failed, or worklist in GHC jargon) equations
with the current substitution, then refines one predicate when exactly one
instance matches then we recursively work on its context (subgoals) together with others.
see also the classic OutsideIn(x).

Below we describe the need for this approach.
Consider example/statem.tig. To type the program, we must solve

  ?m Int ~ Int -> Int × Int (*)

One easily sees that ?m |-> StateM Int being a valid solution yet this equivalence
can't be solved under HM pattern unification because of principality requirement
as ?m args ~ t₂ only unifies iff args are TVs (or skolems, see unify).
(Note that realistically StateM has gone because of expander. We keep it for brevity)

Since RHS is fixed, we can only eliminate the synonym TApp on the LHS, which,
simply means that ?m |-> StateM Int must be known (from unification) before
the TApp occurence of ?m Int -- To solve that is to match the predicate
Monad (m |-> ?m) against Monad (StateM s), which, must come earlier (through refinement)
since previously it only happens in SysF elab. We now describe refinement controlling.

It's not always a good idea to refine predicates. Consider tests/cases/error/amb.tig.
Tigris/Lean/GHC all blocks instance resolution when there are MVs -- indeed ambiguous.
Though, the unique instance (HAdd Int Int Int) matches, gets picked up and
fixes c to Int which otherwise is impossible to deduce since the concrete return
type of (hadd 2 3) can't be known without type ascription. Thus, we permit refinement
iff all of the conditions below is true for a given pred p, a list of deferred equations eqs:

1. eqs is nonempty: the whole point of refinement in advance: to solve equations;
2. refineStep succeeds (unique match -- it throws .Ambiguous otherwise).

We have removed condition 3 (a result-fv view protecting to-be-generalized vars from
monomorphization, to solve listEq) in the first order unification refactoring
since it's no longer needed. Now, a nested let whose generalized var is both pred-shared and
equation-blocked is considered ``residual'' (See the paper below) and we generalize
them carefully using a similar strategy already presented in inferInstanceDecl a long time ago.

And thanks to AI's confirmation, it coincides with what
GHC's been using (simplifyInfer, Tc/Solver.hs:~932).
For details, see notes in inferGroup.

> Vytiniotis D. et al, "Let Should Not Be Generalised."
(I quoted this just because some ideas are from it, let-generalization policy is neither changed
 nor needed since we don't have open type family or indexed family at the moment.)

However, a combination of removal of pattern fragments and views rendered
the exact example (statem) above invalid again. Why is that?
Just by looking at the failing eq: ?m ?sk ~ ?sk' -> ?sk' × ?sk (**), one might assume
it is the same equation as (*) -- it is NOT. This is the provider's
internal equation that failed (i.e. not caused by the calls within main, but at instdecl) -- and it
had skolems -- all TVs, which, got passed the pattern fragments
(meanwhile, Int is a concrete type which makes sure it got deferred), then
in Miller style solves by binding ?m |-> Λ?sk. ?sk' -> ?sk' × ?sk which the guess is lucky.
Now we've removed such guessing, through tracing we found out that though (**) is deferred to be solved here,
refineStep (Monad ?m) throws NoSynthesize since we are checking the instance being declared
(thus not in instInfo yet) and ?m stays unresolved throughout the process then fails;
Although it is clear that ?m := StateM ?sk since that is what the user writes,
the solution to ?m isn't seen by inner applications since that arises from
the outermost ascription (refer to inferInstance* for why that is the case).
Thus, we use a flag `bestEffot` to toggle the behavior: instead of reporting the first
unsolved equation, we solve what we can and returns the partial substs and the leftover
preds so that Ascribe branch's two local solves can use it. Since their equations are
non-consuming, the outer pool solves the whole leftovers, which contains ?m |-> StateM ?sk.

Decidability. Table resolution with ground predicates (canonical) is decidable, as is done in SysF elab. see also
> Selsam D. et al "Tabled typeclass resolution."
> https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/#The-Lean-Language-Reference--Type-Classes--Instance-Synthesis--Instance-Search-Summary

However, the direct implication of refine in advance is that we have to
deal with non-ground predicates (otherwise why refine at all). For cycles at this stage
we must set a maximum recursion depth though cycles surpassing this depth
still get handled by SysF elab so correctness unaffected. Besides, its likely
not going to loop for most programs (must satisfy (1) first).
-/
partial def solveAllWith (bestEffort : Bool) (refine : Bool) (env : Env) (ke : KindEnv) (n₀ : Nat) (cs : List Constraint)
  : Except TypingError SolveResult :=
  let (sub₀, eqs₀, pending₀) := cs.foldr (init := (∅, [], []))
    fun | .eq t u  , (sub, eqs, pending) => (sub, (t, u) :: eqs, pending)
        | .pr eid p, (sub, eqs, pending) => (sub, eqs, (eid, p) :: pending)
  go 64 sub₀ ke n₀ ∅ eqs₀ pending₀ []
where
  mkRes (sub : Subst) (ke : KindEnv) (n : Nat) (done : List $ Nat × Pred) (eqs : List $ MLType × MLType)
    : SolveResult := ⟨sub, ke, n, done.map fun (eid, q) => (eid, apply sub q), eqs⟩

  go (fuel : Nat) (sub : Subst) (ke : KindEnv) (n : Nat) (seen : Std.HashSet Pred)
     (eqs : List $ MLType × MLType) (queue : List $ Nat × Pred) (done : List $ Nat × Pred)
    : Except TypingError SolveResult :=

    let (sub, ke, n, eqs) := eqs.foldl (init := (sub, ke, n, [])) fun (sub, ke, n, rest) (t, u) =>
      match unify ke n (apply sub t) (apply sub u) with
      | .ok (s, ke, n) => (s ∪' sub, ke, n, rest)
      | .error _ => (sub, ke, n, (t, u) :: rest)
    match queue with
    | [] =>
      match eqs with
      | [] => return mkRes sub ke n done []
      | (t, u) :: _ =>
        -- re-run to recover the true failure (a kind error would otherwise
        -- be masked by the retry loop deferring every failure)
        match unify ke n (apply sub t) (apply sub u) with
        | .error err =>
          if bestEffort
          then return mkRes sub ke n done eqs
          else throw err
        | .ok _ =>
          if bestEffort
          then return mkRes sub ke n done []
          else throw (.NoUnify (apply sub t) (apply sub u))
    | (eid, p) :: rest =>
      let p := apply sub p
      if p ∈ seen || fuel == 0 || eqs.isEmpty || !refine
      then go fuel sub ke n seen eqs rest ((eid, p) :: done)
      else match refineStep env ke n p with
        | .error _ => go fuel sub ke n (seen.insert p) eqs rest ((eid, p) :: done)
        | .ok (sub', ke, n, ctx) =>
          let sub := sub' ∪' sub
          go (fuel - 1) sub ke n (seen.insert p) eqs (rest ++ ctx.map (0, ·)) ((eid, apply sub' p) :: done)

@[macro_inline] def solveAll := solveAllWith (bestEffort := false) (refine := true)

/-- solve all w/o refinement, thus does not consume predicates. Used by the pure phase
of generalize-first (GHC's simplifyInfer adapted): -/
@[macro_inline] def solvePure := solveAllWith (bestEffort := true) (refine := false)

/-- Invariant: mkSkol n = ?sk.n. counter is shared. -/
private def mkSkol := MLType.TVar ∘ .sk ∘ TV.id
@[inherit_doc mkSkol] theorem mkSkol_eq : mkSkol tv = TVar (.sk tv.id) := by simp[mkSkol, TV.id]
/-- skolemize over a set (or list) of vars to make instance refinement structurally unable to
touch them. Cf. MLType.unSkolem in ttypes. -/
def rigidize (tvs : Std.TreeSet TV) : Subst := tvs.foldl (fun s v => s.insert v (mkSkol v)) ∅
@[inherit_doc rigidize] def rigidize'(tvs : List TV) : Subst := tvs.foldl (fun s v => s.insert v (mkSkol v)) ∅
attribute [inline] rigidize rigidize' mkSkol

def skolemizeTSch : MLType -> Except TypingError MLType
  | .TSch (.Forall tvs _ t) => return apply (rigidize' tvs) t
  | t => throw (.Impossible s!"skolemizeTSch: expected TSch but got {repr t}")

@[inline] def extend (Γ : Env) (x : String) (sch : Scheme) : Env := {Γ with E := Γ.E.insert x sch}

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
    let pvs := fv p
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
      let (ctorTy, _, _) <- instantiate sch
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
/--
> `[jones2007]` Jones SP, et al. "Practical type inference for arbitrary-rank types."
Bidirectional check mode similar to [jones2007] but simpler since some rules (e.g. lambda with annotated param)
require syntax we currently do not have. The rule (Fig. 8, pp 24) from that paper we concern,

Γ, x : σ |-ₚ t <== σ'
---------------------- Abs2
Γ |- λx, t <== σ -> σ'

the parameter is bound with the raw domain σ (it may itself be a forall), which
is what lets a rank-n argument instantiate at each use.
Top-level foralls are skolemized rigid. See also Ascribe branch.

Note: the judgement |-ₚ (t · σ) reads: t is (checked/inferred to)
have a polytype σ. where the hole [·] ::= ==>     infer
                                        | <==     check
                                        | :       insensitive to either

similarly |-ᵢ σ ==> ρ says σ instantiates to ρ (we only have this direction), as in

tvᵢ ∈ tvs for i ∈ |tvs|
-----------------------------  Inst1
|-ᵢ ∀tvs, ρ ==> ρ[tvᵢ |-> τᵢ]

Inst1 is important as it is used in several part of the constraint solver through
instantiate (Scheme/Var) and elimForall (polytypes). It also appeared independently in
Unification; Rule Spec from Ascribe branch's inst-view is also an instantiation.

Inst1 peels only outermost foralls per the paper. an inference premise producing
an arrow is precisely because this instantiation has exposed it (see App branch),
whereas foralls embedded in the arrow's components are the check mode's job
(skolemization below), never inst.
-/
partial def checkExpr (Γ : Env) (exp : MLType) (e : Expr)
  : InferC σ (TExpr × MLType × List Pred) := do
  match exp with
  | .TSch (.Forall vs ps body) => -- Also the Skol rule
    if ps.isEmpty then checkExpr Γ (apply (rigidize' vs) body) e
    else throw .NoRankN
  | _ =>
    match exp, e with
    | a ->' b, Fun x e => do
      -- abs2 (raw binding): the domain is bound as-is; a free MV stays mono
      let sch : Scheme <- match a with
        | .TSch (.Forall vs ps t) =>
          if ps.isEmpty then pure (.Forall vs [] t) else throw TypingError.NoRankN
        | t => pure (.Forall [] [] t)
      let (tBody, tB, pB) <- checkExpr (extend Γ x sch) b e
      return (.Fun x a tBody (a ->' tB), a ->' tB, pB)
    | _, _ => do
      let (te, t, p) <- inferExpr Γ e
      let t <- elimForall t
      addEq t exp -- subsumption unify for rank-n
      return (.Ascribe te exp, exp, p)

partial def inferExpr (Γ : Env) : Expr -> InferC σ (TExpr × MLType × List Pred)
  | Var x => do
    match Γ.E[x]? with
    | none => throw (.Undefined x)
    | some sch =>
      let (t, tArgs, preds) <- instantiate sch
      let preds := preds.map Prod.snd
      return (.Var x tArgs t, t, preds)

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
    | a ->' b => do
      /-                |-ᵢ t₁
                        -------
            Γ |- e₁ ==> a -> b;  Γ |-ₚ e₂ <== a ;  |-ᵢ b : ρ
            ------------------------------------------------  App
            Γ |- e₁ e₂ : ρ

         (Recall that ρ ::= τ | σ -> σ'; We subst σ, σ' for a, b for better readability)
         rule App consumes the arrow (σ -> σ') eagerly (since t₁ can be break into
         an arrow between schemes, the judgement implicitly instantiates t₁)
         so the result type of a sub-application (e₂) keeps its syntactic shape instead of
         hiding behind a fresh result metavariable, then Γ |-ₚ u <== σ checks
         the argument against the domain. This solves (cf. Inst1 in unification)

                             |----- subapp -----|
          let g x f : Int -> (∀ a, a -> a) -> Int = f x
           in g 1 fun x => x -- use site typable

         this way subapp isn't aliased to a mv, which then goes through the
         fall back branch in check mode then fail. -/
      let (tE₂, _, p₂) <- checkExpr Γ a e₂
      return (.App tE₁ tE₂ b, b, p₁ ++ p₂)
    | _ =>
      /- the function's type is not yet an arrow, probably an unsolved metavariable.
         we simply let the wanted pool instantiate any forall it surfaces (Inst1 in unification). -/
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

  | Ascribe e sch@(.TSch $ .Forall vs ps t) =>
    if containsTSch t then do
      /- rank-n annotation (the let-annotation parser wraps every annotation
         in a top TSch, so `(forall a, ...) -> ...` lands here with a nested
         TSch in the body): check mode -- the paper's annot/checkSigma. The
         top-level context is evidenced; nested contexts are rejected by
         checkExpr.

          tvs ∉ fv Γ;  pr(σ) = ∀tvs, ρ;  Γ |- t <== ρ
          ------------------------------------------- Gen2
          Γ |-ₚ t <== σ

          Γ |-ₚ t <== α;  |-ᵢ α <= ρ
          ------------------------- Annot
          Γ |- (t : α) : ρ

          NOTE: parenthesized formula (x : α) is type ascription. not a judgement.

          The pr (prenex conversion, floating foralls) is
          the coercion counterpart of its deep skolemization (|-dsk)
          Since we don't do deep skolemization (lambda parameters bind their raw domain,
          other positions unify structurally), so nothing is floated and no pr is needed.
          Thus ∀a b, a -> b -> b ≅/≅ ∀a, a -> ∀b, b -> b, in our unification -- and no,
          it's not because of value restriction since we don't have that either,
          we just don't allow that isomorphism.
      -/
      let sub <- vs.foldlM (Std.TreeMap.insert · · <$> fresh) ∅
      for p in ps do () <$ freshEvidence (apply sub p)
      let (te, _, p) <- checkExpr Γ (apply sub t) e
      return (.Ascribe te sch, apply sub t, p)
    else do
      let (te, teTy, preds) <- inferExpr Γ e
      let teMono <- elimForall teTy
      let sub <- vs.foldlM (Std.TreeMap.insert · · <$> fresh) (∅ : Subst)
      let inst := apply sub t

      let (cs₀, rigid) <- get <&> fun st => (st.cst, st.rTV)
      let {ke, next,..} <- get
      /-
        Below the two solveAll implements the judgement |-ₛₕ σ <= σ'
         |-ₛₕ ρ₁[sub*] <= ρ₂
         -------------------------- Spec
         |-ₛₕ ∀(dom sub)*, ρ₁ <= ρ₂
      -/
      match solveAllWith (bestEffort := true) (refine := true) Γ ke next $ .eq teMono inst :: cs₀
      with
      | .error err => throw err
      | .ok {sub, ke, next, ..} =>
        modify ({· with ke, next})
        if sub.any (fun tv rhs => tv ∈ rigid && rhs != MLType.TVar tv)
        then throw (.NoUnify teMono inst)
        else addEq teMono inst

      ps.forM fun p => () <$ freshEvidence (apply sub p)

      let skTy <- skolemizeTSch sch
      let {ke, next,..} <- get
      /-
         tvs ∉ fv σ;  |-ₛₕ σ <= ρ
         ------------------------ Skol
         |-ₛₕ σ <= ∀ tvs. ρ
      -/
      match solveAllWith (bestEffort := true) (refine := true) Γ ke next (.eq teMono skTy :: cs₀)
      with
      | .error err => throw err
      | .ok {ke, next, ..} => (.Ascribe te sch, inst, preds) <$ modify ({· with ke, next})

  | Ascribe e ty =>
    if containsTSch ty then do -- the TSch branch above keeps its wanted-pool structure
      let (te, _, p) <- checkExpr Γ ty e
      return (.Ascribe te ty, ty, p)
    else do
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
  let {ke, next,..} <- get

  /- GHC's simplifyInfer adapted to the deferred pool. It is simplified because
     we don't have eager instance rules (Cf. hkt-dict-parametricity.tig & hkt-eager-specialize.tig)
     which matches what Lean does. (see also similar approach in inferInstanceDecl)

     1. solvePure solves the equations to exhaustion without refinement so that
        everything the equations alone can determine (including the rec names' mvs) is fixed;
     2. skolemizes all TVs (TVᵣ) shared between the result types
        (subst'd from step 1) and the pending predicates,
        minus the environment's and the leftover equations'. Concretely,

          TVᵣ := fv [sub₁]trs ∩ fv wants \ fv Γ \ fv leftover

        TVᵣ is now effectively _untouchable_ (see OutsideIn(X)), preventing them from being
        refined/specialized/monomorphized to a concrete instance head in step 3 (see bindTV)
        (parametric instances still bind their ?inst TVs to the skolem, unchanged)

     3. normal solving as before (*) on the skolemized constraints.
     (*) except that we must undo 2 (unSkolem) before generalization since it
         relies on fvT which doesn't count skolems.

     Above is mostly standard procedure; Most importantly, we must consume the constraints
     after this. Otherwise this leads to a new problem examined in let-gen.tig which previously
     blocked by views, described below.

     1. the group (f x, g y) infers and generalizes to f : ∀α β [C α]... which is correct
     2. but in this process the constraints are non-consuming, outer toplevel solve re-solves
        them again, where, in the outer pool, from g we yield ?m |-> Λa. a, it is then used
        to rewrite f's body with tArgs become that.
     3. We now have a desync between the body and the scheme in f. While we quantified α
        in the scheme, in the body it is a groud, concrete Λa. a. SysF elab thus
        directly synthesizes C Id instead of using the dict parameter (not even there
        in the program since the goal is erroneously solved already)
     4. Previously an implicit assumption is that re-solving constraints is harmless
        thanks to the views. Now that's unsound. -/
  let ⟨sub₁, ke, next, wants₁, leftEqs₁⟩ <- solvePure Γ ke next localCs
  let trs := Array.seq2 (Prod.fst ∘ .snd ∘ .snd) tyRec tyNon
  let resFV := Array.foldl (· ∪ fv ·) ∅ $ apply sub₁ trs
  let predFV := wants₁.foldl (· ∪ fv ·.snd) ∅
  let eqFV := leftEqs₁.foldl (fun acc (t, u) => acc ∪ fv t ∪ fv u) ∅
  let rigidSub := rigidize $ ((resFV ∩ predFV) \ fv Γ) \ eqFV
  let cs₂ := apply rigidSub localCs
  match solveAll Γ ke next cs₂ with
  | .error err => throw err
  | .ok {sub, ke, next, wants, ..} =>
    -- manually consume (drop, really) and modify the state to avoid outer solveAll
    -- re-solving the group's original/unskolemized constraints which otherwise
    -- defeats the hard work that has been done (to the local copy cs₂) here.
    modify fun st => {st with ke, next, cst := st.cst.drop (st.cst.length - startCs)}

    let predsFor evStart evEnd :=
      wants.foldr (init := []) fun (eid, p) acc =>
        if evStart <= eid && eid < evEnd
        then unSkolemP (apply sub p) :: acc else acc
    let gen := fun (Γ, bindsTyped) (n, te, ty, ps, l, r) =>
      let ty := unSkolem $ apply sub ty
      let sch := generalize Γ ty $ ps.map (unSkolemP ∘ apply sub) ++ predsFor l r
      (extend Γ n sch, bindsTyped.push (n, sch, (apply sub te) |>.mapTypes unSkolem unSkolemS))

    return Array.seq2fold gen (Γ, #[]) tyRec tyNon

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

/--
  elim all type abbreviation. Now that we unify up to η-NF,
  η-expanded abbreviation bodies work as well.
  e.g. Apply Maybe where Apply f a = f a unifies
  with Maybe. β-redexes still never survive construction.
-/
partial def expandExpr (E : Env) : Expr -> Expr
  | c@(.CI ..) | c@(.CS ..) | c@(.CB ..) | c@(.CUnit) | c@(.Var ..) => c
  | .App e₁ e₂ => .App (expandExpr E e₁) (expandExpr E e₂)
  | .Cond e₁ e₂ e₃ => .Cond (expandExpr E e₁) (expandExpr E e₂) (expandExpr E e₃)
  | .Let ae e₂ => .Let (ae.map fun (s, e) => (s, expandExpr E e)) (expandExpr E e₂)
  | .Fix e => .Fix (expandExpr E e)
  | .Fixcomb e => .Fixcomb (expandExpr E e)
  | .Fun a e => .Fun a (expandExpr E e)
  | .Prod' e₁ e₂ => .Prod' (expandExpr E e₁) (expandExpr E e₂)
  | .Match aginst discr =>
    .Match (aginst.map (expandExpr E)) (discr.map fun (ps, e) => (ps, expandExpr E e))
  | .Ascribe e ty => .Ascribe (expandExpr E e) (MLType.expandT (fun S => E.synTy[S]?) ty)


def runInferConstraintT (e : Expr) (Γ : Env) : Except TypingError (TExpr × Scheme × Logger × Nat) :=
  match runInfer1 with
  | .error err => .error err
  | .ok ((te, ty, preds), {log,cst,ke,next,..}) =>
    match solveAll Γ ke next cst with
    | .error err => .error err
    | .ok {sub, next, wants, ..} =>
      let te := apply sub te
      let ty := apply sub ty
      let ps := preds ++ wants.map (apply sub ∘ Prod.snd)
      let sch := generalize Γ ty ps
      .ok (te, sch, log, next)
where runInfer1 :=
  runEST fun σ =>
    (show InferC σ $ TExpr × MLType × List Pred from do
      -- freshen parser binders to session mvs before inference
      let st <- get
      let (e', (n', _)) := runST fun _ => freshenE (expandExpr Γ e) |>.run (st.next, ∅)
      set {st with next := n'}
      inferExpr Γ e')
    |>.run {ke := KindEnv.ofEnv Γ, next := Γ.nextTV}

namespace Helper

def methodScheme (cls : Symbol) (param : Array $ TV × Kind) (mty : MLType) : Scheme :=
  let binders := param.foldr (List.cons ∘ Prod.fst) []
  let args    := binders.map TVar
  .Forall binders [⟨cls, args⟩] mty

private def instQuantifiers (headArgs : List MLType) (ctx : List Pred) : List TV :=
  let (headArgs, ctx) := (headArgs, ctx)
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
  let binders := ci.params.foldr (List.cons ∘ Prod.fst) []
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
  : InstanceDecl -> Except TypingError (String × Scheme × TExpr × Logger × InstanceInfo × Nat)
  | {args, methods, ctxPreds,..} => do
    let iname := s!"i_{ci.cname}_{existingCount}"
    let ordered <- orderInstanceMethods ci methods
    let rigidTVs := fv args ∪ fv ctxPreds
    let rigidSub : Subst := rigidize rigidTVs
    let argsSk := apply rigidSub args
    let rawBody := buildInstProvider ci ordered argsSk
    let (typedBody, inferredSch, l, n') <- runInferConstraintT rawBody E
    let (.Forall _ _ infRes) := inferredSch
    let wantHeadSk := MLType.mkApp (TCon ci.cname) argsSk
    let ke := KindEnv.ofEnv E
    match unify ke n' infRes wantHeadSk with
    | .error _ => throw (.NoUnify infRes wantHeadSk)
    | .ok (sub, _, _) =>
      let detectedSpecialized :=
        args.any fun
          | MLType.TVar v | MLType.TApp (MLType.TVar v) [] =>
            match apply sub (MLType.TVar v) with
            | MLType.TVar v' => v' != v
            | _ => true
          | _ => false
      if detectedSpecialized then
        throw $ .NoSynthesize s!"{Pred.mk ci.cname args}: body is too specific. Supply a specialized scheme instead.\n"

      let declaredCtx := apply sub ctxPreds
      let qs := instQuantifiers args declaredCtx
      let bodyTy := MLType.mkApp (TCon ci.cname) args
      let finalSch := .Forall qs declaredCtx bodyTy
      let typedBody := typedBody |>.mapTypes unSkolem unSkolemS
      return ⟨iname, finalSch, typedBody, l, ⟨iname, ci.cname, args, ctxPreds⟩, n'⟩

/-- kind inference based on the usage in tys.

The parser generates fresh kind metavariables for tvs, user-supplied kind annotation
constrains them; metavariables default to Type. -/
private def inferParamKinds (E : Env) (param : Array (TV × Kind)) (tys : List MLType)
  : Except TypingError (Array (TV × Kind)) := do
  let ke := param.foldl (init := KindEnv.ofEnv E) fun ke (tv, k) =>
    {ke with tv := ke.tv.insert tv k}
  -- the parser and kindOf both produces kind mvs; keep kindOf's fresh
  -- ones clear of the declared kvars so kind unification never conflates them
  let ke := {ke with nxt := param.foldl (fun m (_, k) => (Kind.fv k).foldl max m) ke.nxt + 1}

  let ke <- tys.foldlM (init := ke) fun ke t => kindOf ke t <&> Prod.fst
  return param.map fun (n, k) => (n, Kind.defaultKV (Kind.apply ke.ks k))

def inferToplevelC
  (b : Array TopDecl) (E : Env)
  : Except TypingError (Array TopDeclT × Env × Logger) :=
  b.foldlM (init := (#[], E, "")) fun (acc, E, L) b => do
    let syn := (E.synTy[·]?)
    -- freshen parser binders to session mvs (per-decl name map, session-wide
    -- counter stream)
    let (b, n') :=
      match runST fun _ => freshenTopDecl b |>.run (E.nextTV, ∅) with
      | (b, (n', _)) => (b, n')
    let E := {E with nextTV := n'}
    match b with
    | .extBind s n sch =>
      let sch@(.Forall qs _ body) := MLType.expandS syn sch
      () <$ kindOf (KindEnv.ofEnv E) body
      pure (acc.push (.idBind #[(s, sch, .Var n (qs.map TVar) sch.body)]), {E with E := E.E.insert s sch}, L)
    | .idBind group =>
      let exprLet := Expr.Let group .CUnit
      let (.Let bs _ _, _, l, n') <- runInferConstraintT exprLet E | throw (.Impossible "unexpected shape after let inference\n")
      let (E, bs) := bs.foldl
        (fun (E, bs) (n, sc, te) =>
          ( {E with E := E.E.insert n sc}
          , bs.push (n, sc, te)))
        ({E with nextTV := n'}, #[])
      return (acc.push (.idBind bs), E, L ++ l)
    | .tyBind ty@{ctors, tycon, param, cls?, rhs} =>
      match rhs with
      | some rhs => -- synonym
        let tvs := param.foldr (List.cons ∘ Prod.fst) []
        -- infer un-annotated param kinds from the RHS (kvar defaults, zonked)
        let param <- inferParamKinds E param [rhs]
        let ty := {ty with param}
        -- register the declared kind
        let E := {E with tyDecl := E.tyDecl.insert tycon ty, synTy := E.synTy.insert tycon (tvs, rhs)}
        return (acc.push (.tyBind ty), E, L)
      | none =>
        let ty := {ty with ctors := ctors.map fun (cname, fields, ar) =>
                    (cname, fields.map fun (f, t) => (f, MLType.expandT syn t), ar)}
        -- infer un-annotated param kinds from the field types; the own tycon
        -- is pre-registered with the provisional (kvar) kinds so recursive
        -- fields like `T f` are checked against the declaration itself
        let E' := {E with tyDecl := E.tyDecl.insert tycon ty}
        let param <- inferParamKinds E' param (ty.ctors.toList.flatMap fun (_, fields, _) => fields.map Prod.snd)
        let ty := {ty with param}
        let E' := {E with tyDecl := E.tyDecl.insert tycon ty}
        for (cname, fields, _) in ty.ctors do
          for (_, t) in fields do if badTSch t then throw .NoRankN
          let s := ctorScheme tycon (param.foldr (List.cons ∘ Prod.fst) []) fields
          () <$ kindOf (KindEnv.ofEnv E') s.body
        let (acc, E) :=
          ctors.foldl (init := (acc, E)) fun (acc, {E, tyDecl, clsInfo, instInfo, synTy, nextTV, ..}) (cname, fields, _) =>
            let s := ctorScheme tycon (param.foldr (List.cons ∘ Prod.fst) []) fields
            if h : cls? ∧ ctors.size ≠ 0 then
              let methods : Array MethodInfo := Prod.fst $ ctors[0].snd.fst.foldl (init := (#[], 0))
                  fun (a, i) (mname, mty) =>
                    (a.push ⟨mname, mty, i⟩, i + 1)
              let cls := ⟨tycon, cname, param, methods⟩
              let E := methodSchemes cls |>.foldl (fun E (n, sch) => E.insert n sch) E
              ( acc
              , ⟨E.insert cname s, tyDecl.insert tycon ty, clsInfo.insert tycon cls, instInfo, synTy, nextTV⟩)
            else (acc, ⟨E.insert cname s, tyDecl.insert tycon ty, clsInfo, instInfo, synTy, nextTV⟩)
        return (acc.push (.tyBind ty), E, L)
    | .patBind (pat, expr) => do
      let (e, sch@(.Forall _ ps te), l₁, n') <- runInferConstraintT expr E
      () <$ validateNoRankN sch
      let l :=
        if !ps.isEmpty then
          Logging.warn
            s!"pattern binding does not support addition of constraints (it is dropped.)\n"
        else ""
      let ((E, b), {log := l₂, cst, ke, next,..}) <- runEST fun _ => inferPattern E te pat |>.run {ke := KindEnv.ofEnv E, next := n'}
      let {sub := subst, next, ..} <- solveAll E ke next cst
      let E := {apply subst E with nextTV := next}
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
      let inst := {inst with ctxPreds := inst.ctxPreds.map (MLType.expandP syn)
                             args     := inst.args.map (MLType.expandT syn)}
      for a in inst.args do if badTSch a then throw .NoRankN
      let (some ci) := E.clsInfo[inst.cname]?
        | throw (.Undefined inst.cname)
      let existing := E.instInfo.getD ci.cname #[]
      let (iname, sch, te, l, info, n') <- inferInstanceDecl E ci existing.size inst
      let instInfo := E.instInfo.alter ci.cname $ some ∘
        fun
        | some arr => arr.push info
        | none => #[info]
      return ( acc.push $ .idBind #[(iname, sch, te)]
             , {E with E := E.E.insert iname sch, instInfo, nextTV := n'}
             , L ++ l)
