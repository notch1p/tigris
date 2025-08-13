import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.pexpSimple

open Expr Lexing Parser Parser.Char Pattern Associativity
namespace Parsing

def opTable : OpTable := .ofList
   [ (DOL , ⟨1  , rightAssoc , App⟩)
   , (ATT , ⟨1  , rightAssoc , App⟩)
   , ("=" , ⟨50 , leftAssoc  , link "eq"⟩)
   , (ADD , ⟨65 , leftAssoc  , link "add"⟩)
   , (SUB , ⟨65 , leftAssoc  , link "sub"⟩)
   , (MUL , ⟨70 , leftAssoc  , link "mul"⟩)
   , (DIV , ⟨70 , leftAssoc  , link "div"⟩)]

def initState : PEnv := ⟨opTable, ∅⟩

def infixlDecl : TParser $ Binding ⊕ α := do
  INFIXL; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.contains op then throwUnexpectedWithMessage none s!"this operator {op} may not be redefined."
    ARROW let e <- parseExpr
    modify fun s@{ops,..} => {s with ops := ops.insert op ⟨i.toNat, .leftAssoc, η₂ e⟩}
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def infixrDecl : TParser $ Binding ⊕ α := do
  INFIXR; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.contains op then throwUnexpectedWithMessage none s!"this operator {op} may not be redefined."
    ARROW let e <- parseExpr
    modify fun s@{ops,..} => {s with ops := ops.insert op ⟨i.toNat, .rightAssoc, η₂ e⟩}
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def letDecl : TParser $ Binding ⊕ α := do
  LET let id <- ID
      let a <- takeMany funBinder
  EQ  let b <- parseExpr
  return .inl (id, transMatch a b)

def letPointedDecl : TParser $ Binding ⊕ α := do
  LET let id <- ID
      let a <- takeMany1 (BAR *> matchDiscr)
  return .inl (id, pointedExp a)

def letrecPointedDecl : TParser $ Binding ⊕ α := do
  LET; REC
      let id <- ID
      let a <- takeMany1 (BAR *> matchDiscr)
  return .inl (id, Fix $ Fun id $ pointedExp a)

def letrecDecl : TParser $ Binding ⊕ α := do
  LET; REC
      let id <- ID
      let a <- takeMany funBinder
  EQ  let b <- parseExpr
  return .inl (id, Fix $ Fun id $ transMatch a b)

def value {α} p := show TParser $ Binding ⊕ α from (.inl ∘ ("_", ·)) <$> p

end Parsing
