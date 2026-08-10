import Tigris.utils
import Tigris.typing.ttypes
import Tigris.parsing.pexpSimple

open Expr Lexing Parser Parser.Char Pattern Associativity
namespace Parsing
variable {σ}

def updateIfKnownD (sym : Symbol) (impl : Expr)
  : TParser σ Unit :=
  modify fun (s@{ops, ..}, l) =>
    if let some ⟨_, prec, assoc, _⟩ := ops.find? sym
    then ({s with ops := ops.insert sym ⟨sym, prec, assoc, η₂ impl⟩}, l)
    else
      let l := l ++ Logging.warn "No prior infix declaration found, using prec 50, leftAssoc.\n"
      ({s with ops := ops.insert sym ⟨sym, 50, leftAssoc, η₂ impl⟩}, l)

/-- Like updateIfKnownD but for the prefix table. -/
def updateIfKnownPre (sym : Symbol) (impl : Expr)
  : TParser σ Unit :=
  modify fun (s@{pre, ..}, l) =>
    if let some ⟨_, prec, _⟩ := pre.find? sym
    then ({s with pre := pre.insert sym ⟨sym, prec, η₁ impl⟩}, l)
    else
      let l := l ++ Logging.warn "No prior prefix declaration found, using prec 80.\n"
      ({s with pre := pre.insert sym ⟨sym, 80, η₁ impl⟩}, l)

def updateInfix (sym : Symbol) (prec : Nat) (assoc : Associativity) (impl : Expr -> Expr -> Expr)
  : TParser σ Unit :=
  modify fun (s@{ops, ..}, l) =>
    let ops := ops.insert sym ⟨sym, prec, assoc, impl⟩
    ({s with ops}, l)

def unwrapAnn : Option Scheme -> Expr -> Expr
  | some sch, core => .Ascribe core (.TSch sch)
  | none, core => core

def infixlDecl : TParser σ Binding := withExpected "infixl operator declaration" do
  let kwCol <- kwCol "infixl"
  let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trimAscii.toString
    if reservedOp.find? op matches some _
    then error s!"this operator {op} may not be redefined\n"; throwUnexpected
    if let some e <- option? $ ARROW *> withInlineBlock kwCol parseExpr then
      updateInfix op i.toNat .leftAssoc $ η₂ e
      return (s!"({op})", e)
    else
      updateInfix op i.toNat .leftAssoc $ η₂ $ Var s!"«{op}»"
      return (s!"({op})", CUnit)

  | _, _ => return ("_", CUnit)

def infixrDecl : TParser σ Binding := withExpected "infixr operator declaration" do
  let kwCol <- kwCol "infixr"
  let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trimAscii.toString
    if reservedOp.find? op matches some _
    then error s!"this operator {op} may not be redefined\n"; throwUnexpected
    if let some e <- option? $ ARROW *> withInlineBlock kwCol parseExpr then
      updateInfix op i.toNat .rightAssoc $ η₂ e
      return (s!"({op})", e)
    else
      updateInfix op i.toNat .rightAssoc $ η₂ $ Var s!"«{op}»"
      return (s!"({op})", CUnit)
  | _, _ => return ("_", CUnit)

def prefixDecl : TParser σ Binding := withExpected "prefix operator declaration" do
  let kwCol <- kwCol "prefix"
  let i <- intExp let s <- strExp
  match s, i with
  | CS op , CI i =>
    let op := op.trimAscii.toString
    if reservedOp.find? op |>.isSome
    then error s!"this operator {op} may not be redefined\n" *> throwUnexpected
    ARROW let e <- withInlineBlock kwCol parseExpr
    modify fun (s@{pre,..}, l) =>
      let pre := pre.insert op ⟨op, i.toNat, η₁ e⟩
      ({s with pre}, l)
    return (s!"(ₚ{op})", e)
  | _, _ => return ("_", CUnit)

def postfixDecl : TParser σ Binding := withExpected "postfix operator declaration" do
  let kwCol <- kwCol "postfix"
  let i <- intExp let s <- strExp
  match s, i with
  | CS op , CI i =>
    let op := op.trimAscii.toString
    if reservedOp.find? op |>.isSome
    then error s!"this operator {op} may not be redefined\n" *> throwUnexpected
    ARROW let e <- withInlineBlock kwCol parseExpr
    modify fun (s@{post,..}, l) =>
      let post := post.insert op ⟨op, i.toNat, η₁ e⟩
      ({s with post}, l)
    return (s!"({op})ₚ", e)
  | _, _ => return ("_", CUnit)

def letBody (floorCol : Nat) : Symbol -> Array Pattern -> Option Scheme -> TParser σ Binding :=
  fun id pre ann? => do
    match <- test (lookAhead BAR) with
    | true =>
      let a <- barBranches matchDiscr
      let core := transMatch pre $ pointedExp a
      return (id, unwrapAnn ann? core)
    | false =>
      let a <- eqRhs floorCol
      let core := transMatch pre a
      return (id, unwrapAnn ann? core)

def let1Common
  : (Symbol -> Array Pattern -> Option Scheme -> TParser σ Binding) -> TParser σ Binding :=
  fun kont => do
    let id <- funBinder'
    let ann := option? (COLON *> PType.tyScheme)
    match id with
    | pid@(PVar id) =>
      let pre <- takeMany funBinderID
      if pre.isEmpty then
        let pos <- getPosition
        if let some op <- option? potentialOp then
          if op ∈ ["=",":=", ":", "|"] then setPosition pos *> ann >>= kont id pre
          else
            if reservedOp.find? op |>.isSome
            then error s!"operator {op} may not be redefined\n" *> throwUnexpected
            let pre <- funBinder'
            let op' := s!"«{op}»"
            updateIfKnownD op (Var op')
            let (_, e) <- kont op' #[pid, pre] =<< ann
            return (op', e)
        else kont id pre =<< ann
      else
        kont id pre =<< ann
    | _ =>
      if let some op <- option? potentialOp' then
        if reservedOp.find? op |>.isSome
        then error s!"operator {op} may not be redefined\n" *> throwUnexpected
        let pre <- funBinder'
        let op' := s!"«{op}»"
        updateIfKnownD op (Var op')
        let (_, e) <- kont op' #[id, pre] =<< ann
        return (op', e)
      else throwUnexpected

def letrecBody (floorCol : Nat) : Symbol -> Array Pattern -> Option Scheme -> TParser σ Binding :=
  fun id pre ann? => do
    match <- test (lookAhead BAR) with
    | true =>
      let a <- barBranches matchDiscr
      let core := Fix $ Fun id $ transMatch pre $ pointedExp a
      return (id, unwrapAnn ann? core)
    | false =>
      let a <- eqRhs floorCol
      if pre.isEmpty && !a matches Fun .. then
        let core := transMatch pre a
        return (id, unwrapAnn ann? core)
      else
        let core := Fix $ Fun id $ transMatch pre a
        return (id, unwrapAnn ann? core)

/--
> Note that toplevel let has relaxed layout requirement and may not be _syntactically toplevel_
> thus the parser is heavier due to letdecl/letexp backtracking.
> Without suffering toplevel syntactic flexibility we
> provide alternative kw to avoid letdecl/letexp backtracking.
> Besides, using OCaml-style `;;/end` is much welcomed as it does the same thing.

To further address the performance issue above we fence the binding group at letCol.
Toplevel has no aligned bindings (*) and has a subsingleton indent stack `[0]`,
where crossLine may cross freely; the fence requires an inline RHS's continuation
indent pass letCol, so a following col-letCol line (another toplevel decl) is not
greedily eaten as an application argument only to backtrack for lack of an letexp body.

Meanwhile, toplevel letdecls can still be indented and parsed but then it's just
the same old situation where backtracking is unavoidable. There's a reason Haskell
prohibits it (indented toplevel must align), we just don't enforce it.

(*) because of this we permit indent-n form in the middle of a application at toplevel i.e.
```lean
(letdecl)  ...whereas...  (letexp)
let x = f                 let x = f
  a -- correct                 a -- correct
```
-/
def letDeclDispatch : TParser σ $ Array Binding := withExpected "let-declaration" do
  let letCol <- kwCol "def" <|> kwCol "let"
  let p <- test REC >>= fun | false => pure letBody | true => pure letrecBody
  let b <- withInlineBlock letCol $ sepBy1 AND $ let1Common $ p letCol

  option? (IN *> parseExpr) >>= fun -- only for REPL, avoids backtracking. not "true" letexp
  | some body => return #[("_", Let b body)]
  | none => do
    let some b' <- option? $ whereBindings whereRec | pure b
    return b' ++ b
where whereRec (whereCol : Nat) := let1Common (letrecBody whereCol)

def letPatDecl : TParser σ (Pattern × Expr) := withExpected "pattern declaration" do
  let letCol <- kwCol "def" <|> kwCol "let"
  if <- test REC then
    warn "found non-variable pattern on the left hand side,\nThis declaration will be treated as a letdecl\n"
  let pat <- Parsing.funBinder'
  EQ; let exp <- withInlineBlock letCol parseExpr
  return (pat, exp)

def value p := show TParser σ Binding from ("_", ·) <$> p

def externDecl : TParser σ TopDecl := withExpected "extern declaration" do
  EXTERN; let id <- ID let name <- spaces *> strLit
  COLON let sch <- PType.tyScheme
  return .extBind id name sch

def instanceBinder (floorCol : Nat) : TParser σ Binding := do
  let f <- ID
  let pre <- takeMany funBinderID
  match <- test (lookAhead BAR) with
  | true =>
    let a <- barBranches matchDiscr
    return (f, transMatch pre $ pointedExp a)
  | false =>
    let a <- eqRhs floorCol
    return (f, transMatch pre a)

def instanceExp (ctor : Symbol) (fs : Array Binding)
  : TParser σ (Array $ String × Expr) := withExpected "instance body" do
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
def instanceDecl : TParser σ TopDecl := withExpected "instance declaration" do
  INSTANCE; optional COLON
  let (.Forall _ ctxPreds ty) <- tyScheme
  let (cname, args) <-
    match ty.getRightmost with
    | .TApp (.TCon cname) args => pure (cname, args)
    | .TCon cname              => pure (cname, [])
    | _ => error "not a valid class" *> throwUnexpected
  let fs <- first
    [ EQ *> braced (sepBy COMMA (instanceBinder 0))
    , whereBindings instanceBinder ]
  let methods <- instanceExp cname fs
  return .instBind {ctxPreds, cname, args, methods}

end Parsing
