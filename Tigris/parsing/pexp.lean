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
def initState : PEnv := {ops := opTable, tys := ∅, undTy := []}

def infixlDecl : TParser σ $ Binding ⊕ α := do
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
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def infixrDecl : TParser σ $ Binding ⊕ α := do
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
    return .inl (s!"({op})", e)
  | _, _ => pure $ .inl ("_", CUnit)

def letDeclDispatch : TParser σ $ Binding ⊕ α := do
  LET; let tr <- test REC; let id <- ID; let pre <- takeMany funBinderID
  match tr with
  | false =>
    match <- test BAR with
    | true =>
      let a <- sepBy1 BAR matchDiscr
      return .inl (id, transMatch pre $ pointedExp a)
    | false =>
      EQ; let a <- parseExpr
      return .inl (id, transMatch pre a)
  | true =>
    match <- test BAR with
    | true =>
      let a <- sepBy1 BAR matchDiscr
      return .inl (id, Fix $ Fun id $ transMatch pre $ pointedExp a)
    | false =>
      EQ let a <- parseExpr
      if pre.isEmpty && !a matches Fun .. then
        warn "Use letdecl instead of letrec for nonrecursive definition\n"
        return .inl (id, transMatch pre a)
      else return .inl (id, Fix $ Fun id $ transMatch pre a)

def letPatDecl : TParser σ (Pattern × Expr) := do
  LET;
  if <- test REC then warn "found non-variable pattern on the left hand side,\nThis declaration will be treated as a letdecl\n"
  let pat <- Parsing.funBinder
  EQ; let exp <- parseExpr
  return (pat, exp)

def value {α} p := show TParser σ $ Binding ⊕ α from (.inl ∘ ("_", ·)) <$> p

end Parsing
