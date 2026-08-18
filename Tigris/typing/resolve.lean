import Tigris.typing.ttypes
import Tigris.typing.constraint

/-!
Tabled Typeclass Resolution, similar to Lean 4's. See also

> Selsam, Daniel, Sebastian Ullrich, and Leonardo de Moura.
> "Tabled typeclass resolution." arXiv preprint arXiv:2001.04301 (2020).
-/

namespace Resolve open MLType ConstraintInfer Rewritable

structure ResolveState where
  /-- per-call table of each pred's resolution outcome -/
  done   : Std.HashMap Pred (Except TypingError Expr)
  /-- current goals (cycle detection) -/
  inProg : Std.HashSet Pred

instance : EmptyCollection ResolveState := ⟨∅, ∅⟩

abbrev ResolveM σ := StateRefT ResolveState (EST TypingError σ)

variable {σ : Type}

instance : MonadLift (Except TypingError) (EST TypingError σ) where
  monadLift
  | .error e => throw e
  | .ok e => return e

@[inline] def markVisited : Pred -> ResolveM σ Unit := (modify fun st => {st with inProg := st.inProg.insert ·})
@[inline] def unmarkVisited : Pred -> ResolveM σ Unit := (modify fun st => {st with inProg := st.inProg.erase ·})
@[inline] def already? : Pred -> ResolveM σ Bool := (get <&> fun {inProg,..} => · ∈ inProg)
@[inline] def cacheResult : Pred -> Except TypingError Expr -> ResolveM σ Unit :=
  (modify fun st => {st with done := st.done.insert · ·})

partial def resolve (env : Env) (p : Pred) : ResolveM σ Expr := do
  let s : ResolveState <- get
  match s.done[p]? with
  | some (.ok e) => return e
  | some (.error e) => throw e
  | none =>
    if <- already? p
    then throw $ TypingError.Ambiguous s!"cyclic instance resolution involving {p}\n"

    markVisited p
    try
      let some insts := env.instInfo[p.cls]? | throw $ .NoSynthesize s!"{p}: no matching instance found\n"

      -- newest declaration first so we find from right.
      let res? : Option Expr <- insts.findSomeRevM? fun info => do
        try
          let ke := KindEnv.ofEnv env
          let (sub, _) <- unifyHead ke p.args info.args
          let ctx := apply sub info.ctx
          ctx.forM fun s => resolve env s $> ()
          let specializedHead := MLType.mkApp (.TCon p.cls) p.args
          pure $ some $ .Ascribe (.Var info.iname) specializedHead
        catch _ => pure none
      match res? with
      | some res => cacheResult p (.ok res) *> return res
      | none =>
        cacheResult p $ .error $ .NoSynthesize s!"{p}: no matching instance found\n"
        throw $ .NoSynthesize s!"{p}: no matching instance found\n"
    finally unmarkVisited p

@[inline] def resolvePred (env : Env) (p : Pred) : Except TypingError Expr :=
  runEST fun _ => Resolve.resolve env p |>.run' ∅

/-- search for an instance C α₁ ... where C matches p.cls, ignoring
contexts. p's args must be rigid so that only instance variables are bindable. -/
def matchHead (env : Env) (p : Pred) : Except TypingError String := do
  let some insts := env.instInfo[p.cls]?
    | throw $ .NoSynthesize s!"{p}: no matching instance found\n"

  let some i := insts.findSomeRev? fun info =>
                  if (unifyHead (KindEnv.ofEnv env) p.args info.args).isOk
                  then some info.iname
                  else none
    | throw $ .NoSynthesize s!"{p}: no matching instance found\n"
  return i

end Resolve
