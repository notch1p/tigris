import Tigris.utils
import Tigris.typing.ttypes
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
  let ann? <- option? (COLON *> (PType.tyScheme))
  match <- test BAR with
  | true =>
    let a <- sepBy1 BAR matchDiscr
    let core := transMatch pre $ pointedExp a
    let rhs := match ann? with | some sch => Expr.Ascribe core (.TSch sch) | none => core
    return (id, rhs)
  | false =>
    EQ; let a <- parseExpr
    let core := transMatch pre a
    let rhs := match ann? with | some sch => Expr.Ascribe core (.TSch sch) | none => core
    return (id, rhs)

def letrec1Decl : TParser σ $ Binding := do
  let id <- ID; let pre <- takeMany funBinderID
  let ann? <- option? (COLON *> PType.tyScheme)
  match <- test BAR with
  | true =>
    let a <- sepBy1 BAR matchDiscr
    let core := Fix $ Fun id $ transMatch pre $ pointedExp a
    let rhs := match ann? with | some sch => .Ascribe core (.TSch sch) | none => core
    return (id, rhs)
  | false =>
    EQ let a <- parseExpr
    if pre.isEmpty && !a matches Fun .. then
      let core := transMatch pre a
      let rhs := match ann? with | some sch => .Ascribe core (.TSch sch) | none => core
      return (id, rhs)
    else
      let core := Fix $ Fun id $ transMatch pre a
      let rhs := match ann? with | some sch => .Ascribe core (.TSch sch) | none => core
      return (id, rhs)

def letDeclDispatch : TParser σ $ Array Binding := do
  LET;
  let bs <-
    match <- test REC with
    | false => sepBy1 AND let1Decl
    | true => sepBy1 AND letrec1Decl
  match <- option? (IN *> parseExpr) with
  | some body => return #[("_", Let bs body)]
  | none => return bs

def letPatDecl : TParser σ (Pattern × Expr) := do
  LET;
  if <- test REC then
    warn "found non-variable pattern on the left hand side,\nThis declaration will be treated as a letdecl\n"
  let pat <- Parsing.funBinder
  EQ; let exp <- parseExpr
  return (pat, exp)

def value p := show TParser σ Binding from ("_", ·) <$> p

def externDecl : TParser σ TopDecl := do
  EXTERN; let id <- ID let name <- spaces *> strLit
  COLON let sch <- PType.tyScheme
  return .extBind id name sch

partial def instanceExp (ctor : Symbol)
  : TParser σ (Array $ String × Expr) := do
  let fs <- braced do sepBy COMMA do
    let f <- ID;
    let pre <- takeMany funBinderID
    match <- test BAR with
    | true =>
      let a <- sepBy1 BAR matchDiscr
      return (f, transMatch pre $ pointedExp a)
    | false =>
      EQ; let a <- parseExpr
      return (f, transMatch pre a)
  let ({recordFields,..}, _) <- get
  let some order := recordFields.get? ctor | error s!"unknown record {ctor}\n"; throwUnexpected
  let mut mp : Std.HashMap String Expr := ∅
  for (f, e) in fs do
    if f ∈ mp then
      error s!"duplicate fields '{f}' for record {ctor} literal\n"
      throwUnexpected
    mp := mp.insert f e
  if order.any (not ∘ mp.contains) || mp.size != order.size then
    error s!"record literal does not match field set of {ctor}\n"
    throwUnexpected
  return order.foldl (init := #[]) fun a s =>
    a.push (s, mp.get! s)

open PType in
def instanceDecl : TParser σ TopDecl := do
  INSTANCE
  let (.Forall _ ctxPreds ty) <- tyScheme
  let (.TApp cname args) := ty.getRightmost | error "not a valid class" *> throwUnexpected
  EQ;
  let methods <- instanceExp cname
  return .instBind {ctxPreds, cname, args, methods}

end Parsing
