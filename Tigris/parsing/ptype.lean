import Tigris.typing.types
import Tigris.parsing.types
import Tigris.lexing

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing
variable {σ}

def registerTy (name : String) (arity : Nat) : TParser σ Unit := do
  modify fun (st@{tys,..}, l) => ({st with tys := tys.insert name arity}, l)

def getTyArity (name : String) : TParser σ $ Option Nat := do
  get <&> (·.1.tys.find? name)

mutual
partial def tyCtor : TParser σ MLType := do
  let id <- ID
  if isUpperInit id then return TApp id []
  else return TVar (.mkTV id)
partial def tyApps (mt : Bool) : TParser σ MLType := withErrorMessage "TyTerm" do
  let hd <- tyAtom mt
  match hd with
  | .TApp h [] =>
    match <- getTyArity h with
    | some 0 => return TCon h
    | some k =>
      let arg <- take k $ tyAtom mt
      return TApp h arg.toList
    | none =>
      if mt then
        modify fun (pe@{undTy,..}, s) => ({pe with undTy := h :: undTy}, s)
        let arg <- takeMany $ tyAtom mt; return TApp h arg.toList
      else
        error s!"The type {Logging.magenta h} is undefined\n"
        throwUnexpected
  | _ => return hd

partial def tyProd (mt : Bool) : TParser σ MLType := do
  let t₁ <- tyApps mt
  let tn <- takeMany (ws (char '×' <|> char '*') *> tyApps mt)
  return (t₁ :: tn.toList).foldr1 TProd (List.cons_ne_nil _ _)

partial def tyArrow (mt : Bool) : TParser σ MLType := do
  let lhs <- tyProd mt
  (ARROW *> tyArrow mt >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

partial def tyAtom (mt : Bool) : TParser σ MLType :=
  tyCtor <|> parenthesized (tyArrow mt)
end

def tyEmpty : TParser σ $ Binding ⊕ TyDecl := do
  TYPE let tycon <- ID let param <- takeMany ID;
  return .inr {tycon, param, ctors := #[]}

def tyDecl (mt : Bool) : TParser σ $ Binding ⊕ TyDecl := withErrorMessage "TyDecl" do
  TYPE let tycon <- ID let param <- takeMany ID; EQ
  registerTy tycon param.size
  let hd <- (optional BAR *> ctor mt)
  let tl <- takeMany (BAR *> ctor mt)
  return .inr {tycon, param, ctors := #[hd] ++ tl}
where
  ctor mt := do let cname <- ID let args <- takeMany (tyApps mt) return (cname, args.toList)

end PType

end Parsing
