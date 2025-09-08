import Tigris.typing.types

namespace TExpr open Rewritable
open Array (sizeOf_lt_of_mem)
local infixr:80 " <> " => Nat.lt_trans
def applyTE : Subst -> TExpr -> TExpr
  | s, .CI i ty           => .CI i (apply s ty)
  | s, .CS v ty           => .CS v (apply s ty)
  | s, .CB b ty           => .CB b (apply s ty)
  | s, .CUnit ty          => .CUnit (apply s ty)
  | s, .Var x ty          => .Var x (apply s ty)
  | s, .Fun p pt b ty     => .Fun p (apply s pt) (applyTE s b) (apply s ty)
  | s, .Fixcomb e ty      => .Fixcomb (applyTE s e) (apply s ty)
  | s, .Fix e ty          => .Fix (applyTE s e) (apply s ty)
  | s, .App f a ty        => .App (applyTE s f) (applyTE s a) (apply s ty)
  | s, .Let bs b ty       =>
    .Let (bs.attach.map fun ⟨p, prop⟩ =>
            have :=
              (prod_sizeOf_lt p.2 |>.2)
              <> (prod_sizeOf_lt p |>.2)
              <> sizeOf_lt_of_mem prop
            (p.1, apply s p.2.1, applyTE s p.2.2))
         (applyTE s b) (apply s ty)
  | s, .Cond c t e ty     => .Cond (applyTE s c) (applyTE s t) (applyTE s e) (apply s ty)
  | s, .Prod' l r ty      => .Prod' (applyTE s l) (applyTE s r) (apply s ty)
  | s, .Match scr br ty ex red =>
    .Match (scr.map (applyTE s))
           (br.attach.map fun ⟨p, prop⟩ =>
             have := (prod_sizeOf_lt p |>.2) <> sizeOf_lt_of_mem prop
             (p.1, applyTE s p.2))
           (apply s ty) ex red
  | s, .Ascribe e ty      => .Ascribe (applyTE s e) (apply s ty)
termination_by _ t => t

def fvTE : TExpr -> Std.HashSet TV
  | .CI _ ty
  | .CS _ ty
  | .CB _ ty
  | .CUnit ty
  | .Var _ ty
  | .Fixcomb _ ty
  | .Fix _ ty
  | .Ascribe _ ty =>
      fv ty

  | .Fun _ paramTy body ty =>
      fv ty ∪ fv paramTy ∪ fvTE body

  | .App f a ty =>
      fv ty ∪ fvTE f ∪ fvTE a

  | .Cond c t e ty =>
      fv ty ∪ fvTE c ∪ fvTE t ∪ fvTE e

  | .Prod' l r ty =>
      fv ty ∪ fvTE l ∪ fvTE r

  | .Let binds body ty =>
      let fvBinds :=
        binds.attach.foldl (init := (∅ : Std.HashSet TV)) fun acc ⟨p, prop⟩ =>
          have := (prod_sizeOf_lt p.2 |>.2) <> (prod_sizeOf_lt p |>.2) <> (Array.sizeOf_lt_of_mem prop)
          acc ∪ fv p.2.1 ∪ fvTE p.2.2
      fv ty ∪ fvBinds ∪ fvTE body

  | .Match scrutinees branches resTy _ex _red =>
      let fvScrs :=
        scrutinees.attach.foldl (init := (∅ : Std.HashSet TV)) fun acc ⟨te, prop⟩ =>
          have := sizeOf_lt_of_mem prop
          acc ∪ fvTE te
      let fvBranches :=
        branches.attach.foldl (init := (∅ : Std.HashSet TV)) fun acc ⟨p, prop⟩ =>
          have := (prod_sizeOf_lt p |>.2) <> sizeOf_lt_of_mem prop
          acc ∪ fvTE p.2
      fv resTy ∪ fvScrs ∪ fvBranches
termination_by te => te

instance : Rewritable TExpr := ⟨applyTE, fvTE⟩

end TExpr
