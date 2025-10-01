import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.constraint

namespace SysF open MLType TExpr Rewritable
open ConstraintInfer (unify)

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

abbrev FEnv := Std.TreeMap String Scheme
abbrev F := EStateM TypingError (Logger × Env)

local instance : MonadLift (Except TypingError) F where
  monadLift
  | .error e => throw e
  | .ok res => return res

def instantiateArgs (qs : List TV) (schemeBody instTy : MLType)
  : F (List MLType) := do
  if qs.isEmpty then return []
  let sub <- unify schemeBody instTy
  return qs.map (fun a => apply sub (TVar a))

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e

local infixr:80 " <> " => Nat.lt_trans
def elaborate (Γ : FEnv) : TExpr -> F FExpr
  | .CI i ty => return .CI i ty
  | .CS s ty => return .CS s ty
  | .CB b ty => return .CB b ty
  | .CUnit ty => return .CUnit ty
  | .Ascribe e _ => elaborate Γ e
  | .Prod' l r ty => .Prod' (ty := ty) <$> elaborate Γ l <*> elaborate Γ r
  | .Cond c t e ty =>
    .Cond (ty := ty) <$> elaborate Γ c <*> elaborate Γ t <*> elaborate Γ e
  | .Var x ty =>
    match Γ.get? x with
    | none => return .Var x ty
    | some (.Forall qs _ bodyTy) =>
      if qs.isEmpty then return .Var x ty
      else
        instantiateArgs qs bodyTy ty <&> List.foldl .TyApp (.Var x ty)
  | .Fun p pTy body ty => (.Fun p pTy · ty) <$> elaborate Γ body
  | .Fix e ty | .Fixcomb e ty => (.Fix · ty) <$> elaborate Γ e
  | .App f a ty => .App (ty := ty) <$> elaborate Γ f <*> elaborate Γ a
  | .Let binds body ty => do
    let Γ := binds.foldl (fun g (x, sch, _) => g.insert x sch) Γ
    let out <- binds.attach.foldlM (init := #[]) fun out {val, property} => do
      let x := val.1; let sch := val.2.1; let rhs := val.2.2
      have := (prod_sizeOf_lt val.2 |>.2)
           <> (prod_sizeOf_lt val |>.2)
           <> Array.sizeOf_lt_of_mem property
      let rhsF <- elaborate Γ rhs
      let (.Forall qs _ bodyTy) := sch
      return out.push (x, sch, wrapTyLams qs rhsF)
    let bodyF <- elaborate Γ body
    return .Let out bodyF ty
  | .Match discr br resTy .. => do
    let discrF <- discr.mapM (elaborate Γ)
    let discrTy := discr.map (TExpr.getTy)
    let brF <- br.attach.mapM fun {val, property} =>
      let ps := val.1; let rhs := val.2
      have := (prod_sizeOf_lt val).2 <> Array.sizeOf_lt_of_mem property
      (ps, ·) <$> elaborate Γ rhs
    let E <- get <&> Prod.snd
    let (ex, mat, ty) := Exhaustive.exhaustWitness E discrTy br
    let red :=
      if let some _ := ex then #[] else
        Exhaustive.redundantRows E ty mat
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
    modify fun (l, E) => (l ++ msg, E)
    return .Match discrF brF resTy ex red
termination_by e => e

def elaborate1 (e : TExpr) (sch : Scheme) (Γ : Env := ∅) : F FExpr :=
  let (.Forall qs _ _) := sch
  (wrapTyLams qs ·) <$> elaborate Γ.E e


end SysF
open MLType SysF
def runInferConstraintF (e : Expr) (Γ : Env)
  : Except TypingError (FExpr × Scheme × Logger) :=
  match runInferConstraintT e Γ with
  | .ok (te, sch, log) =>
    match elaborate1 te sch Γ |>.run ("", Γ) with
    | .ok fe (l, _) => return (fe, sch, log ++ l)
    | .error e _ => throw e
  | .error err => throw err
