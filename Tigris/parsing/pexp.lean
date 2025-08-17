import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.pexpSimple

open Expr Lexing Parser Parser.Char Pattern Associativity
namespace Parsing
variable {σ}

def opTablePrim : List (Symbol × OpEntry) :=
  [ (DOL , ⟨DOL, 1  , rightAssoc , App⟩)
  , (ATT , ⟨ATT, 1  , rightAssoc , App⟩)
  , ("=" , ⟨"=", 50 , leftAssoc  , link "eq"⟩)
  , (ADD , ⟨ADD, 65 , leftAssoc  , link "add"⟩)
  , (SUB , ⟨SUB, 65 , leftAssoc  , link "sub"⟩)
  , (MUL , ⟨MUL, 70 , leftAssoc  , link "mul"⟩)
  , (DIV , ⟨DIV, 70 , leftAssoc  , link "div"⟩)]

def opTable : OpTable := .ofList opTablePrim
def initState : PEnv := {ops := opTable, tys := ∅}

def infixlDecl : TParser σ $ Binding ⊕ α := do
  INFIXL; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.contains op then throwUnexpectedWithMessage none s!"this operator {op} may not be redefined."
    ARROW let e <- parseExpr
    modify fun (s@{ops,..}, l) =>
      let ops := ops.insert op ⟨op, i.toNat, .leftAssoc, η₂ e⟩
      ({s with ops}, l)
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def infixrDecl : TParser σ $ Binding ⊕ α := do
  INFIXR; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.contains op then throwUnexpectedWithMessage none s!"this operator {op} may not be redefined."
    ARROW let e <- parseExpr
    modify fun (s@{ops,..}, l) =>
      let ops := ops.insert op ⟨op, i.toNat, .rightAssoc, η₂ e⟩
      ({s with ops}, l)
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def letDecl : TParser σ $ Binding ⊕ α := do
  LET let id <- ID
      let a <- takeMany funBinder
  EQ  let b <- parseExpr
  return .inl (id, transMatch a b)

def letPointedDecl : TParser σ $ Binding ⊕ α := do
  LET let id <- ID
      let pre <- takeMany funBinder
      let a <- takeMany1 (BAR *> matchDiscr)
  return .inl (id, transMatch pre $ pointedExp a)

def letrecPointedDecl : TParser σ $ Binding ⊕ α := do
  LET; REC
      let id <- ID
      let pre <- takeMany funBinder
      let a <- takeMany1 (BAR *> matchDiscr)
  return .inl (id, Fix $ Fun id $ transMatch pre $ pointedExp a)

def letrecDecl : TParser σ $ Binding ⊕ α := do
  LET; REC
      let id <- ID
      let a <- takeMany funBinder
  EQ  let b <- parseExpr
  if a.isEmpty && !b matches Fun .. then
    warn "Use letdecl instead of letrec for nonrecursive definition\n"
    return .inl (id, transMatch a b)
  else return .inl (id, Fix $ Fun id $ transMatch a b)
def letPatDecl : TParser σ (Pattern × Expr) := do
  LET;
  if <- test REC then warn "found non-variable pattern on the left hand side,\nThis declaration will be treated as a letdecl\n"
  let pat <- Parsing.funBinder
  EQ; let exp <- parseExpr
  return (pat, exp)

def value {α} p := show TParser σ $ Binding ⊕ α from (.inl ∘ ("_", ·)) <$> p

end Parsing
