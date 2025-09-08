import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.pexpSimple

open Expr Lexing Parser Parser.Char Pattern Associativity
namespace Parsing
variable {σ}

def infixlDecl : TParser σ Binding := do
  INFIXL; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.find? op matches some _
    then error s!"this operator {op} may not be redefined\n"; throwUnexpected
    ARROW let e <- parseExpr
    modify fun (s@{ops,..}, l) =>
      let ops := ops.insert op ⟨op, i.toNat, .leftAssoc, η₂ e⟩
      ({s with ops}, l)
    return (s!"({op})", e)
  | _, _ => pure ("_", CUnit)

def infixrDecl : TParser σ Binding := do
  INFIXR; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    if reservedOp.find? op matches some _
    then error s!"this operator {op} may not be redefined\n"; throwUnexpected
    ARROW let e <- parseExpr
    modify fun (s@{ops,..}, l) =>
      let ops := ops.insert op ⟨op, i.toNat, .rightAssoc, η₂ e⟩
      ({s with ops}, l)
    return (s!"({op})", e)
  | _, _ => pure ("_", CUnit)

def let1Decl : TParser σ $ Binding := do
  let id <- ID; let pre <- takeMany funBinderID
  match <- test BAR with
  | true =>
    let a <- sepBy1 BAR matchDiscr
    return (id, transMatch pre $ pointedExp a)
  | false =>
    EQ; let a <- parseExpr
    return (id, transMatch pre a)

def letrec1Decl : TParser σ $ Binding := do
  let id <- ID; let pre <- takeMany funBinderID
  match <- test BAR with
  | true =>
    let a <- sepBy1 BAR matchDiscr
    return (id, Fix $ Fun id $ transMatch pre $ pointedExp a)
  | false =>
    EQ let a <- parseExpr
    if pre.isEmpty && !a matches Fun .. then
      return (id, transMatch pre a)
    else return (id, Fix $ Fun id $ transMatch pre a)

def letDeclDispatch : TParser σ $ Array Binding := do
  LET;
  match <- test REC with
  | false => sepBy1 AND let1Decl
  | true => sepBy1 AND letrec1Decl

def letPatDecl : TParser σ (Pattern × Expr) := do
  LET;
  if <- test REC then
    warn "found non-variable pattern on the left hand side,\nThis declaration will be treated as a letdecl\n"
  let pat <- Parsing.funBinder
  EQ; let exp <- parseExpr
  return (pat, exp)

def value p := show TParser σ Binding from ("_", ·) <$> p

end Parsing
