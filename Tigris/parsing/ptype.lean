import Tigris.typing.types
import Tigris.parsing.types
import Tigris.lexing

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing
variable {σ}

def registerTy (name : String) (arity : Nat) : TParser σ Unit := do
  modify fun (st@{tys,..}, l) => ({st with tys := tys.insert name arity}, l)

def getTyArity (name : String) : TParser σ Nat := do
  get <&> (·.1.tys.getD name 0)

mutual
partial def tyCtor : TParser σ MLType := do
  let id <- ID
  if isUpperInit id then return TApp id []
  else return TVar (.mkTV id)

partial def tyApps : TParser σ MLType := do
  let hd <- tyAtom
  match hd with
  | .TApp h [] =>
    let k <- getTyArity h
    if k = 0 then return TCon h
    else
      let arg <- take k tyAtom
      return TApp h arg.toList

  | _ => return hd

partial def tyProd : TParser σ MLType := do
  let t₁ <- tyApps
  let tn <- takeMany (ws (char '×' <|> char '*') *> tyApps)
  return tn.foldr TProd t₁

partial def tyArrow : TParser σ MLType := do
  let lhs <- tyProd
  (ARROW *> tyArrow >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

partial def tyAtom : TParser σ MLType :=
  tyCtor <|> parenthesized tyArrow
end

def tyEmpty : TParser σ $ Binding ⊕ TyDecl := do
  TYPE let tycon <- ID let param <- takeMany ID;
  return .inr {tycon, param, ctors := #[]}

def tyDecl : TParser σ $ Binding ⊕ TyDecl := do
  TYPE let tycon <- ID let param <- takeMany ID; EQ
  registerTy tycon param.size
  let hd <- (optional BAR *> ctor)
  let tl <- takeMany (BAR *> ctor)
  return .inr {tycon, param, ctors := #[hd] ++ tl}
where
  ctor := do let cname <- ID let args <- takeMany tyApps return (cname, args.toList)

end PType

end Parsing
