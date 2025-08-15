import Tigris.typing.types
open Pattern MLType

namespace Exhaustive

abbrev 𝓜 := List (List Pattern)
abbrev 𝓥 := List Pattern

def 𝒮 (head : Symbol) (arity : Nat) (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PCtor c args :: ps =>
        if c == head ∧ args.size = arity then
          (args.toList ++ ps) :: acc
        else
          acc
    | PVar _ :: ps | PWild :: ps =>
        (List.replicate arity PWild ++ ps) :: acc
    | _ => acc

def 𝒮ₚ (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PProd' p q :: ps => (p :: q :: ps) :: acc
    | PVar _ :: ps | PWild :: ps => (PWild :: PWild :: ps) :: acc
    | _ => acc

inductive FinDom | unit | bool deriving Repr
namespace FinDom open TConst
def headFinDom : MLType -> Option FinDom
  | TCon "Unit" | TApp "Unit" _ => unit
  | TCon "Bool" | TApp "Bool" _ => bool
  | _ => none
def constsOf : FinDom -> List TConst
  | unit => [PUnit] | bool => [PBool true, PBool false]
def constMatch : FinDom -> TConst -> Bool
  | unit, .PUnit | bool, PBool _ => true
  | _, _ => false
def ςₖ (d : FinDom) (M : 𝓜) : Std.HashSet TConst :=
  M.foldl (init := ∅) fun a s =>
    match s with
    | PConst k :: _ => if constMatch d k then a.insert k else a
    | _ => a
def 𝒮ₖ (k : TConst) (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun s a =>
    match s with
    | PConst k' :: ps => if k == k' then ps :: a else a
    | PVar _ :: ps | PWild :: ps => ps :: a
    | _ => a
end FinDom

def 𝒟 (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PVar _ :: ps => ps :: acc
    | PWild :: ps  => ps :: acc
    | _ => acc
def ς (M : 𝓜) : Std.HashSet (Symbol × Nat) :=
  M.foldl (init := ∅) fun acc row =>
    match row with
    | PCtor n args :: _ => acc.insert (n, args.size)
    | _ => acc

def inς (td : TyDecl) (sig : Std.HashSet (Symbol × Nat)) : Option (Symbol × Nat) :=
  td.ctors.findSome? fun (n, fts) =>
    let key := (n, fts.length)
    if sig.contains key then none else some key

private def substTV (m : Std.HashMap TV MLType) : MLType -> MLType
  | MLType.TVar a =>
    match m.get? a with | some t => t | none => MLType.TVar a
  | MLType.TCon s => MLType.TCon s
  | MLType.TArr a b => MLType.TArr (substTV m a) (substTV m b)
  | MLType.TProd a b => MLType.TProd (substTV m a) (substTV m b)
  | MLType.TApp s ts => MLType.TApp s (ts.map (substTV m))

def ctorFieldTypes (td : TyDecl) (cname : Symbol) (tyArgs : List MLType) : Option (List MLType) :=
  let paramTVs := td.param.toList.map (fun n => TV.mkTV n)
  let substMap := paramTVs.foldl2 Std.HashMap.insert ∅ tyArgs
  match td.ctors.find? (fun (n, _) => n == cname) with
  | none => none
  | some (_, fts) => some (fts.map (substTV substMap))

def headTyconArgs : MLType -> Option (Symbol × List MLType)
  | MLType.TApp s args => some (s, args)
  | MLType.TCon s      => some (s, [])
  | _ => none
open FinDom in
partial def uncover
  (lookup : Symbol -> Option TyDecl)
  (tys : List MLType)
  (M : 𝓜)
  : Option 𝓥 :=
  match tys with
  | []     => if M.isEmpty then some [] else none
  | τ :: σ =>
    match τ with
    | t₁ ×'' t₂ => -- 1. (· × ·) head
      match uncover lookup (t₁ :: t₂ :: σ) (𝒮ₚ M) with
      | none => none
      | some res =>
        let pL := res.headD PWild
        let res1 := res.drop 1
        let pR := res1.headD PWild
        let rest := res1.drop 1
        some (PProd' pL pR :: rest)
    | _ =>
      match headFinDom τ with -- 2. a) const (ₖ) head
      | some d =>
        let sig := ςₖ d M
        let all := constsOf d
        let missing := all.filter (fun k => not (sig.contains k))
        if missing.isEmpty then
          let rec tryKs : List TConst -> Option (List Pattern)
            | [] => none
            | k :: ks =>
              let M' := 𝒮ₖ k M
              match uncover lookup σ M' with
              | none => tryKs ks
              | some us => some (PConst k :: us)
          tryKs all
        else -- 2. b) incomplete head -- defaults to PWild
          match uncover lookup σ (𝒟 M) with
          | none => none
          | some us =>
            if sig.isEmpty then
              some (PWild :: us)
            else
              some (PConst missing.head! :: us)
      | none => -- 3. inductive type
        match headTyconArgs τ with
        | none =>
            match uncover lookup σ (𝒟 M) with
            | none => none
            | some us => some (PWild :: us)
        | some (tycon, tyArgs) =>
          match lookup tycon with
          | none =>
              match uncover lookup σ (𝒟 M) with
              | none => none
              | some us => some (PWild :: us)
          | some td =>
            let sig := ς M
            match inς td sig with
            | none =>
              let rec tryCtors (cs : List (Symbol × List MLType)) : Option 𝓥 :=
                match cs with
                | [] => none
                | (cname, fts) :: cs' =>
                  let arity := fts.length
                  match ctorFieldTypes td cname tyArgs with
                  | none => tryCtors cs'
                  | some fieldTys =>
                    let M' := 𝒮 cname arity M
                    match uncover lookup (fieldTys ++ σ) M' with
                    | none => tryCtors cs'
                    | some res =>
                      let argsP := res.take arity
                      let restP := res.drop arity
                      some (PCtor cname argsP.toArray :: restP)
              tryCtors td.ctors.toList
            | some (missingName, ar) =>
              match uncover lookup σ (𝒟 M) with
              | none => none
              | some us =>
                if sig.isEmpty then
                  some (PWild :: us)
                else
                  some (PCtor missingName (List.replicate ar PWild |>.toArray) :: us)

def exhaustWitness (env : Env) (colTypes : Array MLType) (rows : Array (Array Pattern × Expr)) : Option 𝓥 :=
  let lookup (s : Symbol) := env.tyDecl.get? s
  let M : 𝓜 := rows.foldr (init := []) fun (pat, _) a => pat.toList :: a
  let tys := colTypes.toList
  uncover lookup tys M

end Exhaustive
