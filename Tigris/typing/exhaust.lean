import Tigris.typing.types
open Pattern

namespace Exhaustive
def 𝒮₀ (p : Pattern) (pps : List $ List Pattern) : List $ List Pattern :=
  match p, pps with
  | PCtor c a, ((PCtor c' _) :: ps) :: pps =>
    if c == c' then
      a.foldr (· :: ·) ps :: 𝒮₀ p pps
    else 𝒮₀ p pps
  | PCtor _ a, (PVar _ :: ps) :: pps
  | PCtor _ a, (PWild :: ps) :: pps =>
    let p := a.foldr (fun _ a => PWild :: a) ps
    if p matches [] then pps else p :: pps
  | _, _ => []

def 𝒟₀ (pps : List $ List Pattern) : List $ List Pattern :=
  pps.foldr (init := []) fun s a =>
    match s with
    | PWild :: ss => ss :: a
    | _ => a

def ςcomp? (t : TyDecl) (sig : Std.HashSet (Symbol × Nat)) : Unit ⊕ (Symbol × List MLType) :=
  match t with
  | {ctors,..} =>
    Id.run do
      let mut res := true
      let mut i   := 0
      for (c, a) in ctors do
        if sig.contains (c, a.length) then i := i + 1; continue
        else res := false break
      return if res then .inl () else .inr ctors[i]!

def ctorsToPat (t : Symbol × Nat) := PCtor t.1 (t.2.fold (fun _ _ a => a.push PWild) #[])

def ς (pps : List $ List Pattern) : Std.HashSet (Symbol × Nat) :=
  pps.foldl (init := ∅) fun a s =>
    match s with
    | PCtor n as :: _ => a.insert (n, as.size)
    | _ => a

partial def ℐ (t : TyDecl) (pps : List $ List Pattern) (i : Nat) : Option (List Pattern) :=
  if i = 0 then if pps matches [] then some [] else none
  else
    let ς := ς pps
    let ςarr := ς.toArray
    match ςcomp? t ς with
    | .inl () =>
      let rec go it :=
        if it = ςarr.size then none
        else
          let p@(_, a) := ςarr[it]!
          let res := ℐ t (𝒮₀ (ctorsToPat p) pps) (a + i - 1)
          if let some x := res then some x
          else go it.succ
      go 0
    | .inr ls =>
      match ℐ t (𝒟₀ pps) (i - 1) with
      | none => none
      | some xs =>
        if ςarr.isEmpty then some $ PWild :: xs
        else
          let (a, ls) := ls
          some $ ctorsToPat (a, ls.length) :: xs

def matPeel1 (ls : List $ List Pattern) : List (List Pattern) :=
  ls.foldr (init := []) fun s a =>
    if let _ :: xs := s then
      xs :: a
    else []

def exhaust (t : Array TyDecl) (pps : List $ List Pattern) (i : Nat) : List Pattern :=
  (·.1) <| t.foldl (init := ([], pps)) fun (res, pps) t =>
    if let some x := ℐ t pps i then
      (res ++ x, matPeel1 pps)
    else (res, matPeel1 pps)

--open MLType TV in
--#eval
--  let ty1 : TyDecl := ⟨"Expr", #["a"], #[ ("Atom", [TVar $ mkTV "a"])
--                                       , ("Add", [TApp "Expr" [TVar $ mkTV "a"], TApp "Expr" [TVar $ mkTV "a"]])
--                                       , ("Sub",[TApp "Expr" [TVar $ mkTV "a"], TApp "Expr" [TVar $ mkTV "a"]])]⟩
--  let ty2 : TyDecl := ⟨"Expr", #["a"], #[ ("Atom", [TVar $ mkTV "a"])
--                                       , ("Add", [TApp "Expr" [TVar $ mkTV "a"], TApp "Expr" [TVar $ mkTV "a"]])
--                                       , ("Sub",[TApp "Expr" [TVar $ mkTV "a"], TApp "Expr" [TVar $ mkTV "a"]])]⟩
--  ℐ ty1 [ [PCtor "Atom" #[(PVar "a")], PCtor "Add" #[(PVar "a"), (PVar "a")]]
--          , [PCtor "Add" #[(PVar "a"), (PVar "a")], PCtor "Atom" #[(PVar "a")]]] 2

end Exhaustive
