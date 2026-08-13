import Tigris.typing.ttypes

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
    .Let (bs.attach.map fun ⟨(sym, sch, expr), mem⟩ =>
                            have := prod_sizeOf_lt_snd sch expr
                                 <> prod_sizeOf_lt_snd sym (sch, expr)
                                 <> sizeOf_lt_of_mem mem
                            (sym, apply s sch, applyTE s expr))
         (applyTE s b) (apply s ty)
  | s, .Cond c t e ty     => .Cond (applyTE s c) (applyTE s t) (applyTE s e) (apply s ty)
  | s, .Prod' l r ty      => .Prod' (applyTE s l) (applyTE s r) (apply s ty)
  | s, .Match scr br ty ex red =>
    .Match (scr.map (applyTE s))
           (br.attach.map fun ⟨(ps, expr), mem⟩ =>
             have := prod_sizeOf_lt_snd ps expr <> sizeOf_lt_of_mem mem
             (ps, applyTE s expr))
           (apply s ty) ex red
  | s, .Ascribe e ty      => .Ascribe (applyTE s e) (apply s ty)
termination_by _ t => t

def fvTE : TExpr -> Std.TreeSet TV
  | .CI _ ty
  | .CS _ ty
  | .CB _ ty
  | .CUnit ty
  | .Var _ ty
  | .Fixcomb _ ty
  | .Fix _ ty
  | .Ascribe _ ty => fv ty
  | .Fun _ paramTy body ty => fv ty ∪ fv paramTy ∪ fvTE body
  | .App f a ty => fv ty ∪ fvTE f ∪ fvTE a
  | .Cond c t e ty => fv ty ∪ fvTE c ∪ fvTE t ∪ fvTE e
  | .Prod' l r ty => fv ty ∪ fvTE l ∪ fvTE r
  | .Let binds body ty =>
    let fvBinds :=
      binds.attach.foldl (init := ∅) fun acc ⟨(sym, sch, expr), prop⟩ =>
        have := prod_sizeOf_lt_snd sch expr
             <> prod_sizeOf_lt_snd sym (sch, expr)
             <> sizeOf_lt_of_mem prop
        acc ∪ fv sch ∪ fvTE expr
    fv ty ∪ fvBinds ∪ fvTE body

  | .Match scrutinees branches resTy _ex _red =>
    let fvScrs :=
      scrutinees.attach.foldl (init := ∅) fun acc ⟨te, prop⟩ =>
        have := sizeOf_lt_of_mem prop
        acc ∪ fvTE te
    let fvBranches :=
      branches.attach.foldl (init := ∅) fun acc ⟨(ps, expr), prop⟩ =>
        have := prod_sizeOf_lt_snd ps expr <> sizeOf_lt_of_mem prop
        acc ∪ fvTE expr
    fv resTy ∪ fvScrs ∪ fvBranches
termination_by te => te

instance : Rewritable TExpr := ⟨applyTE, fvTE⟩

def mapTypes (f : MLType -> MLType) (g : Scheme -> Scheme := id) : TExpr -> TExpr
  | .CI i ty              => .CI i (f ty)
  | .CS s ty              => .CS s (f ty)
  | .CB b ty              => .CB b (f ty)
  | .CUnit ty             => .CUnit (f ty)
  | .Var x ty             => .Var x (f ty)
  | .Fun p pTy b ty       => .Fun p (f pTy) (mapTypes f g b) (f ty)
  | .Fixcomb e ty         => .Fixcomb (mapTypes f g e) (f ty)
  | .Fix e ty             => .Fix (mapTypes f g e) (f ty)
  | .App fn arg ty        => .App (mapTypes f g fn) (mapTypes f g arg) (f ty)
  | .Let binds body ty    =>
    let binds' := binds.attach.map fun ⟨(x, sch, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd sch rhs <> prod_sizeOf_lt_snd x (sch, rhs) <> sizeOf_lt_of_mem h
      (x, g sch, mapTypes f g rhs)
    .Let binds' (mapTypes f g body) (f ty)
  | .Cond c t e ty        => .Cond (mapTypes f g c) (mapTypes f g t) (mapTypes f g e) (f ty)
  | .Prod' l r ty         => .Prod' (mapTypes f g l) (mapTypes f g r) (f ty)
  | .Match scr br ty ex rd =>
    let scr' := scr.map (mapTypes f g)
    let br'  := br.attach.map fun ⟨(ps, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd ps rhs <> sizeOf_lt_of_mem h
      (ps, mapTypes f g rhs)
    .Match scr' br' (f ty) ex rd
  | .Ascribe e ty         => .Ascribe (mapTypes f g e) (f ty)
termination_by te => te
end TExpr
