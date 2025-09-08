import Tigris.typing.types
import Tigris.parsing.types
import Tigris.lexing

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing
variable {σ}

def registerTy (name : String) (arity : Nat) (mt : Bool) (flag := true) : TParser σ Unit := do
  if let true <- modifyGet fun orig@(st@{tys,..}, l) =>
    match tys.find? name with
    | none =>
      (true, {st with tys := tys.insert name (arity, flag)}, l)
    | some (arity', k) =>
      if arity' == arity && mt then
        if !k && flag then (true, {st with tys := tys.insert name (arity, flag)}, l)
        else (true, orig)
      else
        let err := Logging.error $
          if mt then
            s!"mutual inductive type {Logging.magenta name} arity mismatch,\n\
              expected {arity'} but received {arity}\n"
          else s!"type {Logging.magenta name}/{Logging.cyan ∘ toString $ arity'} may not be redefined\n"
        (false, st, l ++ err)
  then return ()
  else throwUnexpected

def getTyArity (name : String) : TParser σ $ Option (Nat × Bool) := do
  get <&> (·.1.tys.find? name)

mutual
partial def tyCtor (param : Array String) : TParser σ MLType := do
  let id <- ID
  if isUpperInit id then return TApp id []
  else
    if id ∈ param then
      return TVar (.mkTV id)
    else
      error s!"unbound type variable {id}\n"
      throwUnexpected
partial def tyApps (mt : Bool) (param : Array String) : TParser σ MLType := withErrorMessage "TyTerm" do
  let hd <- tyAtom mt param
  match hd with
  | .TApp h [] =>
    match <- getTyArity h with
    | some (0, _) => return TCon h
    | some (k, _) =>
      let arg <- take k $ tyAtom mt param
      let s <- takeMany $ tyAtom mt param
      if s.isEmpty then
        return TApp h arg.toList
      else
        error s!"type {Logging.magenta h} arity mismatch, \
              expected {k} but received {k + s.size}\n"
        throwUnexpected
    | none =>
      if mt then
        modify fun (pe@{undTy,..}, s) => ({pe with undTy := h :: undTy}, s)
        let arg <- takeMany $ tyAtom mt param;
        registerTy h arg.size mt false
        return TApp h arg.toList
      else
        error s!"undefined type {Logging.magenta h}\n"
        throwUnexpected
  | _ => return hd

partial def tyProd (mt : Bool) (param : Array String) : TParser σ MLType := do
  let t₁ <- tyApps mt param
  let tn <- takeMany (ws (char '×' <|> char '*') *> tyApps mt param)
  return (t₁ :: tn.toList).foldr1 TProd (List.cons_ne_nil _ _)

partial def tyArrow (mt : Bool) (param : Array String) : TParser σ MLType := do
  let lhs <- tyProd mt param
  (ARROW *> tyArrow mt param >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

partial def tyAtom (mt : Bool) (param : Array String) : TParser σ MLType :=
  tyCtor param <|> parenthesized (tyArrow mt param)
end

def tyEmpty : TParser σ TyDecl := do
  TYPE let tycon <- ID let param <- takeMany ID;
  return {tycon, param, ctors := #[]}

@[inline]
def tyExp : TParser σ MLType := tyArrow false #[]

def tyDecl (mt : Bool) : TParser σ TyDecl := withErrorMessage "TyDecl" do
  TYPE let tycon <- ID
  if isUpperInit tycon then
    let param <- takeMany ID; EQ
    registerTy tycon param.size mt
    let hd <- (optional BAR *> ctor mt param)
    let tl <- takeMany (BAR *> ctor mt param)
    return {tycon, param, ctors := #[hd] ++ tl}
  else
    error "type constructor must begin with an uppercase letter\n"
    throwUnexpected
where
  ctor mt param := do
    let cname <- ID
    if isUpperInit cname then
      let args <- takeMany (tyApps mt param)
      return (cname, args.toList, args.size)
    else
      error "value constructor must begin with an uppercase letter\n"
      throwUnexpected

end PType

end Parsing
