import Tigris.typing.ttypes
open Pattern MLType

namespace Exhaustive

abbrev 𝓜 := List (List Pattern)
abbrev 𝓥 := List Pattern

def 𝒮 (head : Symbol) (arity : Nat) (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PCtor c args :: ps =>
        if c == head && args.size == arity then
          (args.toList ++ ps) :: acc
        else
          acc
    | PVar .. :: ps | PWild :: ps =>
        (List.replicate arity PWild ++ ps) :: acc
    | _ => acc

def 𝒮ₚ (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PProd' p q :: ps => (p :: q :: ps) :: acc
    | PVar .. :: ps | PWild :: ps => (PWild :: PWild :: ps) :: acc
    | _ => acc

inductive FinDom | unit | bool deriving Repr
namespace FinDom open TConst
def headFinDom : MLType -> Option FinDom
  | TCon "Unit" | TApp (TCon "Unit") _ => unit
  | TCon "Bool" | TApp (TCon "Bool") _ => bool
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
    | PVar .. :: ps | PWild :: ps => ps :: a
    | _ => a
end FinDom

def 𝒟 (M : 𝓜) : 𝓜 :=
  M.foldr (init := []) fun row acc =>
    match row with
    | PVar .. :: ps => ps :: acc
    | PWild :: ps  => ps :: acc
    | _ => acc
def ς (M : 𝓜) : Std.HashSet (Symbol × Nat) :=
  M.foldl (init := ∅) fun acc row =>
    match row with
    | PCtor n args :: _ => acc.insert (n, args.size)
    | _ => acc

def completeData (td : TyDecl) (sig : Std.HashSet (Symbol × Nat)) : Bool :=
  td.ctors.all fun (n, _, ar) => sig.contains (n, ar)

def inς (td : TyDecl) (sig : Std.HashSet (Symbol × Nat)) : Option (Symbol × Nat) :=
  td.ctors.findSome? fun (n, _, ar) =>
    let key := (n, ar)
    if sig.contains key then none else some key

private partial def substTV (m : Std.HashMap TV MLType) : MLType -> MLType
  | TVar a => m.getD a (TVar a)
  | TCon s => TCon s
  | TArr a b => TArr (substTV m a) (substTV m b)
  | TProd a b => TProd (substTV m a) (substTV m b)
  | TApp h ts => MLType.mkApp (substTV m h) (ts.map (substTV m))
  | MLType.TyLam x body =>
    -- Shadowing: drop `x` from the substitution before recursing.
    MLType.TyLam x (substTV (m.erase x) body)
  | TSch (.Forall vs ps t) =>
    let m := vs.foldl .erase m
    .TSch (.Forall vs (ps.map fun p => p.mapArgs (substTV m)) t)

def ctorFieldTypes (td : TyDecl) (cname : Symbol) (tyArgs : List MLType) : Option (List MLType) :=
  let paramTVs := td.param.foldr (List.cons ∘ TV.mkTV ∘ Prod.fst) []
  let substMap := paramTVs.foldl2 Std.HashMap.insert ∅ tyArgs
  match td.ctors.find? (fun (n, _) => n == cname) with
  | none => none
  | some (_, fts, _) => some (fts.map (substTV substMap ∘ Prod.snd))

def headTyconArgs : MLType -> Option (Symbol × List MLType)
  | MLType.TApp (MLType.TCon s) args => some (s, args)
  | MLType.TCon s                    => some (s, [])
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
              let rec tryCtors (cs : List (Symbol × List (String × MLType) × Nat)) : Option 𝓥 :=
                match cs with
                | [] => none
                | (cname, _, arity) :: cs' =>
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
              tryCtors $ td.ctors.toList
            | some (missingName, ar) =>
              match uncover lookup σ (𝒟 M) with
              | none => none
              | some us =>
                if sig.isEmpty then
                  some (PWild :: us)
                else
                  some (PCtor missingName (List.replicate ar PWild |>.toArray) :: us)

open FinDom in
partial def useful
  (lookup : Symbol -> Option TyDecl)
  (tys : List MLType)
  (M : 𝓜)
  (row : 𝓥)
  : Bool :=
  match tys, row with
  | [], [] => M.isEmpty
  | τ :: σ, p :: ps =>
    match τ with
    | t₁ ×'' t₂ =>
      match p with
      | PProd' p1 p2 => useful lookup (t₁ :: t₂ :: σ) (𝒮ₚ M) (p1 :: p2 :: ps)
      | PVar .. | PWild =>
        useful lookup (t₁ :: t₂ :: σ) (𝒮ₚ M) (PWild :: PWild :: ps)
      | _ => false
    | _ =>
      match headFinDom τ with
      | some d =>
        let sig := ςₖ d M
        let all := constsOf d
        let complete := all.all (fun k => sig.contains k)
        match p with
        | PConst k => useful lookup σ (𝒮ₖ k M) ps
        | PVar .. | PWild =>
          if complete then
            all.any (fun k => useful lookup σ (𝒮ₖ k M) ps)
          else
            useful lookup σ (𝒟 M) ps
        | _ => false
      | none =>
        match headTyconArgs τ with
        | some (tycon, tyArgs) =>
          match lookup tycon with
          | some td =>
            match p with
            | PCtor cname args =>
              match ctorFieldTypes td cname tyArgs with
              | some fts => useful lookup (fts ++ σ) (𝒮 cname args.size M) (args.toList ++ ps)
              | none     => false
            | PVar .. | PWild =>
              let sig := ς M
              let complete := completeData td sig
              if complete then
                td.ctors.any fun (cname, fts, ar) =>
                  useful lookup (fts.appendMap Prod.snd σ) (𝒮 cname ar M) (List.replicate ar PWild ++ ps)
              else
                useful lookup σ (𝒟 M) ps
            | _ => false
          | none =>
            -- unknown type: fall back to default
            match p with
            | PVar .. | PWild => useful lookup σ (𝒟 M) ps
            | PConst k       => useful lookup σ (FinDom.𝒮ₖ k M) ps
            | _              => useful lookup σ (𝒟 M) ps
        | none =>
          -- not a product/finite/data head: default
          match p with
          | PVar .. | PWild => useful lookup σ (𝒟 M) ps
          | PConst k       => useful lookup σ (FinDom.𝒮ₖ k M) ps
          | _              => useful lookup σ (𝒟 M) ps
  | _, _ => false

def exhaustWitness -- α is `Expr` / `TExpr`
  (env : Env)
  (colTypes : Array MLType)
  (rows : Array (Array Pattern × α)) : Option 𝓥 × 𝓜 × List MLType :=
  letI lookup := env.tyDecl.get?
  let M : 𝓜 := rows.foldr (List.cons ∘ Array.toList ∘ Prod.fst) []
  let tys := colTypes.toList
  (uncover lookup tys M, M, tys)

def redundantRows
  (env : Env)
  (colTypes : List MLType)
  (rows : 𝓜) : Array Nat :=
  letI lookup := env.tyDecl.get?
  Prod.snd ∘ Prod.snd <| rows.foldl (init := (0, [], #[])) fun (i, prevM, acc) s =>
    letI useful? := useful lookup colTypes prevM s
    ( i + 1
    , s :: prevM
    , if useful? then acc else acc.push i)

end Exhaustive
