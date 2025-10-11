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
      binds.attach.foldl (init := ∅) fun acc ⟨p, prop⟩ =>
        have := (prod_sizeOf_lt p.2 |>.2) <> (prod_sizeOf_lt p |>.2) <> (Array.sizeOf_lt_of_mem prop)
        acc ∪ fv p.2.1 ∪ fvTE p.2.2
    fv ty ∪ fvBinds ∪ fvTE body

  | .Match scrutinees branches resTy _ex _red =>
    let fvScrs :=
      scrutinees.attach.foldl (init := ∅) fun acc ⟨te, prop⟩ =>
        have := sizeOf_lt_of_mem prop
        acc ∪ fvTE te
    let fvBranches :=
      branches.attach.foldl (init := ∅) fun acc ⟨p, prop⟩ =>
        have := (prod_sizeOf_lt p |>.2) <> sizeOf_lt_of_mem prop
        acc ∪ fvTE p.2
    fv resTy ∪ fvScrs ∪ fvBranches
termination_by te => te

instance : Rewritable TExpr := ⟨applyTE, fvTE⟩

partial def mapTypes (f : MLType -> MLType) (g : Scheme -> Scheme := id) : TExpr -> TExpr
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
    let binds' := binds.map fun (x, sch, rhs) => (x, g sch, mapTypes f g rhs)
    .Let binds' (mapTypes f g body) (f ty)
  | .Cond c t e ty        => .Cond (mapTypes f g c) (mapTypes f g t) (mapTypes f g e) (f ty)
  | .Prod' l r ty         => .Prod' (mapTypes f g l) (mapTypes f g r) (f ty)
  | .Match scr br ty ex rd =>
    let scr' := scr.map (mapTypes f g)
    let br'  := br.map (fun (ps, rhs) => (ps, mapTypes f g rhs))
    .Match scr' br' (f ty) ex rd
  | .Ascribe e ty         => .Ascribe (mapTypes f g e) (f ty)

def tv? : TV -> Bool
  | .mkTV s => s.startsWith "?m"

partial def alignAscribes : TExpr -> TExpr
  | .Ascribe e sch@(.TSch (.Forall vs _ _)) =>
    let e := alignAscribes e
    let metas := fvTE e |>.foldl (fun a s => if tv? s then s :: a else a) []
    if metas.length == vs.length then
      let sub := List.foldl2 (·.insert · $ .TVar ·) ∅ metas vs
      .Ascribe (applyTE sub e) sch
    else .Ascribe e sch
  | .Ascribe e ty => .Ascribe (alignAscribes e) ty
  | .CI i ty              => .CI i ty
  | .CS s ty              => .CS s ty
  | .CB b ty              => .CB b ty
  | .CUnit ty             => .CUnit ty
  | .Var x ty             => .Var x ty
  | .Fun p pTy b ty       => .Fun p pTy (alignAscribes b) ty
  | .Fixcomb e ty         => .Fixcomb (alignAscribes e) ty
  | .Fix e ty             => .Fix (alignAscribes e) ty
  | .App fn arg ty        => .App (alignAscribes fn) (alignAscribes arg) ty
  | .Let binds body ty    =>
      let binds' := binds.map (fun (x, sch, rhs) => (x, sch, alignAscribes rhs))
      .Let binds' (alignAscribes body) ty
  | .Cond c t e ty        => .Cond (alignAscribes c) (alignAscribes t) (alignAscribes e) ty
  | .Prod' l r ty         => .Prod' (alignAscribes l) (alignAscribes r) ty
  | .Match scr br ty ex rd =>
    let scr' := scr.map alignAscribes
    let br'  := br.map fun (ps, rhs) => (ps, alignAscribes rhs)
    .Match scr' br' ty ex rd

def alignToScheme (te : TExpr) (sch : Scheme) : TExpr :=
  match sch with
  | .Forall qs _ _ =>
    let vs := (fvTE te).toList
    if vs.length != qs.length then te
    else
      let sub : Subst := List.foldl2 (init := ∅) (fun s v q => s.insert v (MLType.TVar q)) vs qs
      applyTE sub te

def rebindTopSch (te : TExpr) (sch : Scheme) : TExpr :=
  match te, sch with
  | .Ascribe e (.TSch (.Forall vs ctx t)), .Forall qs _ _ =>
    if vs.length == qs.length then
      let sub :=
        List.foldl2 (fun s v q => s.insert v (.TVar q)) ∅ vs qs
      .Ascribe (applyTE sub e) $ .TSch $ .Forall qs ctx $ apply sub t
    else te
  | _, _ => te

partial def alignLetBinds : TExpr -> TExpr
  | .Let binds body ty =>
    let binds := binds.map fun (x, sch, rhs) =>
      let rhs := rhs.alignLetBinds.alignAscribes.alignToScheme sch |>.rebindTopSch sch
      (x, sch, rhs)
    .Let binds (alignLetBinds body) ty
  | .Ascribe e ty         => .Ascribe (alignLetBinds e) ty
  | .CI i ty              => .CI i ty
  | .CS s ty              => .CS s ty
  | .CB b ty              => .CB b ty
  | .CUnit ty             => .CUnit ty
  | .Var x ty             => .Var x ty
  | .Fun p pTy b ty       => .Fun p pTy (alignLetBinds b) ty
  | .Fixcomb e ty         => .Fixcomb (alignLetBinds e) ty
  | .Fix e ty             => .Fix (alignLetBinds e) ty
  | .App fn arg ty        => .App (alignLetBinds fn) (alignLetBinds arg) ty
  | .Cond c t e ty        => .Cond (alignLetBinds c) (alignLetBinds t) (alignLetBinds e) ty
  | .Prod' l r ty         => .Prod' (alignLetBinds l) (alignLetBinds r) ty
  | .Match scr br ty ex rd =>
    let scr := scr.map alignLetBinds
    let br  := br.map fun (ps, rhs) => (ps, alignLetBinds rhs)
    .Match scr br ty ex rd

def deSkolemize (e : TExpr) : TExpr :=
  mapTypes MLType.unSkolem MLType.unSkolemS e
end TExpr
