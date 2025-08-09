import Tigris.typing.types
import Tigris.parsing.types
import Tigris.lexing

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing

mutual
partial def tyCtor : TParser MLType := do
  let id <- ID
  if isUpperInit id then return TApp id []
  else return TVar (.mkTV id)

partial def tyApps : TParser MLType := do
  let hd <- tyAtom
  match hd with
  | .TApp h [] =>
    let args <- takeMany tyAtom
    if args.isEmpty then return (TCon h)
    else return TApp h args.toList
  | _ => return hd

partial def tyProd : TParser MLType := do
  let t₁ <- tyApps
  let tn <- takeMany (ws (char '×') *> tyApps)
  return tn.foldr TProd t₁

partial def tyArrow : TParser MLType := do
  let lhs <- tyProd
  (ARROW *> tyArrow >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

partial def tyAtom : TParser MLType :=
  tyCtor <|> parenthesized tyArrow
end


def tyDecl : TParser $ Binding ⊕ TyDecl := do
  TYPE <|> DATA let tycon <- ID let param <- takeMany ID; EQ
  let hd <- (optional BAR *> ctor)
  let tl <- takeMany (BAR *> ctor)
  return .inr {tycon, param, ctors := #[hd] ++ tl}
where
  ctor := do let cname <- ID let args <- takeMany tyApps return (cname, args.toList)

end PType

end Parsing
