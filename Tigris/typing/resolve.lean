import Tigris.typing.ttypes
import Tigris.typing.constraint

namespace Resolve open MLType ConstraintInfer Rewritable

def unifyHead (goalArgs : List MLType) (instArgs : List MLType) : Except TypingError Subst := do
  if goalArgs.length != instArgs.length then
    throw (.NoUnify (MLType.TApp "_goal" goalArgs) (MLType.TApp "_inst" instArgs))
  else
    List.foldlM2
      (fun s g i =>
        (· ∪' s) <$> unify (apply s g) (apply s i))
      (∅ : Subst)
      goalArgs instArgs

abbrev ResolveState := Std.HashSet Pred
abbrev ResolveM σ := StateRefT ResolveState (EST TypingError σ)

variable {σ : Type}

instance : MonadLift (Except TypingError) (EST TypingError σ) where
  monadLift
  | .error e => throw e
  | .ok e => return e


@[inline] def markVisited (p : Pred) : ResolveM σ Unit :=
  modify fun st => st.insert p
@[inline] def already? (p : Pred) : ResolveM σ Bool :=
  get <&> (p ∈ ·)

def classParamNames (env : Env) (cls : String) : Std.HashSet String :=
  match env.clsInfo[cls]? with
  | some ci => ci.params.foldl (fun acc (n, _) => acc.insert n) ∅
  | none => ∅

partial def resolve (env : Env) (p : Pred) : ResolveM σ Expr := do
  if <- already? p then
    throw $ .Ambiguous s!"cyclic instance resolution involving {p}\n"
  markVisited p
  let some insts := env.instInfo[p.cls]?
    | throw $ .NoSynthesize s!"{p}: no matching instance found\n"

  let mut found : Option Expr := none
  for info in insts do

    try
      let res <- do
        let sub <- unifyHead p.args info.args
        let ctx := apply sub info.ctx
        ctx.forM fun s => resolve env s $> ()
        let specializedHead := MLType.TApp p.cls p.args
        pure $ .Ascribe (.Var info.iname) specializedHead
      match found with
      | none => found := some res
      | some _ => throw $ .Ambiguous s!"instance {p}: multiple instances exist\n"

    catch _ => continue

  match found with
  | some d => return d
  | none   => throw $ .NoSynthesize s!"{p}: no matching instance found\n"

@[inline] def resolvePred (env : Env) (p : Pred) : Except TypingError Expr :=
  runEST fun _ => Resolve.resolve env p |>.run' ∅

end Resolve
