import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.pexpSimple

open Expr Lexing Parser Parser.Char Pattern Associativity
namespace Parsing

def opTable : OpTable Expr := .ofArray (cmp := opIndexOrd.compare)
  #[ ((0   , DOL)     , (App       , rightAssoc))
   , ((0   , ATT)     , (App       , rightAssoc))
   , ((50  , "=")     , (link "eq" , leftAssoc))
   , ((65  , ADD)     , (link "add", leftAssoc))
   , ((65  , SUB)     , (link "sub", leftAssoc))
   , ((70  , MUL)     , (link "mul", leftAssoc))
   , ((70  , DIV)     , (link "div", leftAssoc))]

def infixlDecl : TParser $ Binding ⊕ α := do
  INFIXL; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    ARROW let e <- parseExpr
    modify (·.insert (i.toNat, op) (η₂ e, .leftAssoc))
    return .inl (op, e)
  | _, _ => pure $ .inl ("_", CUnit)

def infixrDecl : TParser $ Binding ⊕ α := do
  INFIXR; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    ARROW let e <- parseExpr
    modify (·.insert (i.toNat, op) (η₂ e, .rightAssoc))
    return .inl (op, e)
  | _, _ => pure $ .inl ("_", CUnit)

def letDecl : TParser $ Binding ⊕ α := do
  LET; let id <- ID; let a <- takeMany ID; EQ; let b <- parseExpr;  return .inl (id, a.foldr Fun b)
def letrecDecl : TParser $ Binding ⊕ α := do
  LET;
  REC; let id <- ID; let a <- takeMany ID; EQ; let b <- parseExpr;  return .inl (id, Fix $ Fun id $ a.foldr Fun b)

def value {α} p := show TParser $ Binding ⊕ α from (.inl ∘ ("_", ·)) <$> p
end Parsing

