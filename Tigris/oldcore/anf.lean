import Tigris.parsing.types

namespace ANF open Expr
abbrev M σ := StateRefT Nat (ST σ)

@[inline] def fresh (h := "x") : M σ String :=
  modifyGet fun n => (h ++ toString n, n + 1)

mutual

partial def normalize : Expr -> M σ Expr
  | .Fun x body =>
    .Fun x <$> normalize body

  | .App f a =>
    ensureVar f fun fv =>
    ensureVar a fun av =>
      pure (.App (.Var fv) (.Var av))

  | .Prod' l r =>
    -- Ensure fields are variables
    ensureVar l fun lv =>
    ensureVar r fun rv =>
      pure (.Prod' (.Var lv) (.Var rv))

  | .Cond c t e =>
    ensureVar c fun cv =>
      .Cond (.Var cv) <$> normalize t <*> normalize e

  | .Let x e₁ e₂ =>
    .Let x <$> normalize e₁ <*> normalize e₂

  | .Fix e =>
    .Fix <$> normalize e

  | .Fixcomb e =>
    .Fixcomb <$> normalize e

  | .Match scrut rows =>
    ensureVars scrut.toList fun vs =>
      letI scrut' := vs.foldl (Array.push · $ Var ·) #[]
      (.Match scrut') <$> rows.mapM fun (ps, rhs) =>
        (ps, ·) <$> normalize rhs
  | .Ascribe e _ => normalize e
  | e => pure e

partial def ensureVar (e : Expr) (k : String -> M σ Expr) : M σ Expr := do
  match <- normalize e with
  | .Var x => k x
  | e => let x <- fresh "a"; .Let x e <$> k x

partial def ensureVars (es : List Expr) (k : List String -> M σ Expr) : M σ Expr := do
  match es with
  | [] => k []
  | e :: es =>
    ensureVar e fun x =>
      ensureVars es fun xs => k (x :: xs)

end
end ANF
