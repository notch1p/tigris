import Tigris.utils
import Tigris.typing.ttypes
import Tigris.parsing.ppat
import Tigris.parsing.ptype
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing
variable {σ}
def intExp      : TParser σ Expr := CI <$> (spaces *> intLit)
def strExp      : TParser σ Expr := CS <$> (spaces *> strLit)

def transMatch (pat : Array Pattern) (e : Expr) : Expr :=
  if pat.isEmpty then e else
    let (ep, pat', _) :=
      pat.foldl (init := (#[], #[], 0)) fun (ep, pat', i) s =>
        match s with
        | PVar .. | PWild => (ep, pat', i + 1)
        | p => (ep.push (Var $ hole i), pat'.push p, i + 1)

    let hd := if ep.isEmpty then e else Match ep #[(pat', e)]
    pat.size.foldRev (init := hd) fun i _ a =>
      if let PVar s := pat[i] then Fun s a
      else Fun (hole i) a

def pointedExp (discr : Array $ Array Pattern × Expr) : Expr :=
  if h : discr.size = 0 then CUnit
  else discr[0].1.size.foldRev
        (init := Match (discr[0].1.mapIdx fun i _ => Var $ hole i) discr)
        fun i _ a => Fun (hole i) a

def mkProdPat (arr : Array Symbol) : Pattern :=
  match h : arr.size with
  | 0 => PWild | 1 => PVar arr[0]
  | (_ + 2) => arr.foldr (PProd' ∘ PVar) (PVar arr[arr.size - 1]) (arr.size - 1)

def mkTupExpr (arr : Array Expr) : Expr :=
  match h : arr.size with
  | 0 => CUnit | 1 => arr[0]
  | (_ + 2) => arr.foldr Prod' arr[arr.size - 1] (arr.size - 1)

open TConst in
@[inline] def funBinder : TParser σ Pattern := spaces *> first'
  #[ patRecordTyped
   , patRecord
   , PConst <$> PInt <$> intLit
   , PConst <$> PStr <$> strLit
   , parenthesized patProd
   , parenthesized parsePattern]
  simpErrorCombine
in
@[inline] def funBinderID : TParser σ Pattern := spaces *> first'
  #[ patRecordTyped
   , patRecord
   , PConst <$> PInt <$> intLit
   , PConst <$> PStr <$> strLit
   , ID <&> fun i => if i.isUpperInit then PCtor i #[] else PVar i
   , parenthesized patProd
   , parenthesized parsePattern]
  simpErrorCombine
in
@[inline] def funBinder' : TParser σ Pattern := spaces *> first'
  #[ patRecordTyped
   , patRecord
   , PConst <$> PInt <$> intLit
   , PConst <$> PStr <$> strLit
   , parenthesized patProd
   , parsePattern]
  simpErrorCombine

def reorderRecord (ctor : Symbol) (fs : Array $ String × Expr)
  : TParser σ Expr := do
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
  return order.foldl (App · $ mp.get! ·) (.Var ctor)

def resolveBareRecord (fs : Array $ String × Expr) : TParser σ Expr := do
  let ({recordFields,..}, _) <- get
  let fids := fs.map Prod.fst
  let set : Std.HashSet String := fids.foldl .insert ∅
  letI cand := Std.HashMap.toList <| recordFields.filter fun _ order =>
    order.size == fids.size && order.all set.contains
  match cand with
  | [(ty, _)] => reorderRecord ty fs
  | [] => error "no record type matches the given field set\n" *> throwUnexpected
  | %[(ty, _) | _] => warn
    s!"ambiguous record literal (using default '{ty}'), consider adding type ascription;\n\
       as we currently do not have type-directed parsing.\n\
       candidates are {cand}\n" *> reorderRecord ty fs

mutual
partial def parseExpr : TParser σ Expr := withErrorMessage "Term" parsePratt

partial def atom : TParser σ Expr := spaces *>
  first' #[ recordExpTyped
          , ascription
          , parenthesized prodExp
          , letDispatch
          , funDispatch
          , recordExp
          , fixpointExp , condExp
          , matchExp    , intExp
          , strExp      , varExp]
         simpErrorCombine

/--
Funapp but respects crossLine called from `spaces`.

- spaces may or may not consume vspaces, depending on crossLine.
  - if it does, then cursor skips directly to
    the next token (across multiple lines), which is the original funapp behavior;
  - otherwise, spaces consumes blanks up to the first vspace, that is, the cursor
    must sit at a vspace. In this case we escape with throwUnexpected.

This makes consecutive (sequential) letexps parse correctly so that

```lean
let x = 1
let y = 2
x + y
```

is what you thought it would be instead of `let x = App 1 (let y = 2 in x + y)`.

Note: We may test `atEol` and escape directly in `atom` as well, but that is too strong
and blocks the valid form of

```lean
let x =
  atom
```

since in the case we would like to parse the atom starting at a newline.

-/
partial def appSep : TParser σ (Expr -> Expr -> Expr) := do
  spaces
  if <- atEol then throwUnexpected
  pure App

partial def ascription : TParser σ Expr := parenthesized do
  let e <- parseExpr
  COLON
  Ascribe e <$> PType.tyForall false ∅

partial def prodExp : TParser σ Expr := do
  let es <- sepBy COMMA (parsePratt 0)
  return match h : es.size with
         | 0 => CUnit
         | 1 => transShorthand es[0]
         | _ + 2 =>
           transShorthand $
            es[0:es.size - 1].foldr Prod' es[es.size - 1]

partial def varExp      : TParser σ Expr :=
  ID <&> fun
         | "true"                => CB true
         | "false"               => CB false
         | v                     => Var v

partial def appAtom     : TParser σ Expr := chainl1 primaryAtom appSep

partial def bareAtom    : TParser σ Expr := chainl1 atom appSep

partial def parsePratt (minPrec := 0) : TParser σ Expr := loop =<< appAtom where
  loop lhs := do
    let some {prec, assoc, impl, ..} <- takeInfixOp? minPrec
      | return lhs
    let nextMin := if assoc matches .leftAssoc then prec + 1 else prec
    loop =<< impl lhs <$> parsePratt nextMin

partial def atomPrefix (minPrec := 0) : TParser σ Expr := do
  let some {impl, prec,..} <- takePrefixOp? minPrec | bareAtom
  impl <$> parsePratt prec

partial def primaryAtom (minPrec := 0) : TParser σ Expr := loop =<< atomPrefix where
  loop lhs := do
    let some {impl,..} <- takePostfixOp? minPrec | return lhs
    loop $ impl lhs

partial def matchDiscr  : TParser σ $ Array Pattern × Expr := do
  let p <- sepBy1 COMMA parsePattern
  ARROW let body <- parseExpr     return (p, body)

partial def matchExp    : TParser σ Expr := do
  MATCH let e <- sepBy1 COMMA parseExpr; WITH
  let br <- barBranches matchDiscr
                                  return Match e br

/--
Local column overriding for `= <indented-rhs>` form. Applies to let/where block.

Consider (1) GHC's aligned binding and (2) Lean's indent-n form

```lean
let x = 1 -- (1) let...and... replacement
    y = 2
 in ...

let x =
  expr    -- (2) indent 2 (or n), common for big expr.
```

Tigris supports both (1) and (2) yet they do NOT mix well.
The wrapper `alignedBindings` achieves (1), requiring RHS to indent past bound symbol (GHC behavior);
Thus, to additionally parse (2), we must locally override baseline -- we determine this by checking
whether the next token (judging by how `eqRhs` is called, RHS in this case)
starts after a newline so that (1) still parses.

> Though, it is worth noting that because of this override subsequent bindings are consumed together
> as a whole under the first one (Lean behavior). Which, since (=) is simultaneously
> a kw and the eq operator, may still parse successfully but doesn't make sense
> or straight up a parse error if (:=) is used instead.

- The quoted paragraph is no longer true as the problem is solved.
  See withInlineBlock's docstring.

Note that toplevel letdecl does not even supports aligned bindings
(mandatory AND-separated) so it is not a problem there.

See also Parsing.barBranches from Tigris.lexing: same logic but specialized for Lean-style
pointed functions.

NB. crossline funapp does not work for indent-n pattern for the same reason, e.g.

```lean
let prog = f -- whether ($) or not does not matter.
  x
```

Do this instead:
```lean
let prog = f   ..or..   let prog = f
         $ x                       x
```

-/
partial def eqRhs (letCol : Nat) : TParser σ Expr :=
  EQ *> hspaces *> atEol >>=
    fun
    | true  => withInlineBlock letCol parseExpr
    | false => parseExpr

partial def let1 (letCol : Nat) : TParser σ (Symbol × Expr) := do
  let id <- ID; let pre <- takeMany funBinderID
  let ann? <- option? (COLON *> PType.tyForall false ∅)
  match <- test (lookAhead BAR) with
  | true =>
    let br <- barBranches matchDiscr
    let core := transMatch pre $ pointedExp br
    let rhs := match ann? with | some ty => Expr.Ascribe core ty
                               | none => core
    return Prod.mk id rhs
  | false =>
    let e₁ <- eqRhs letCol
    let core := transMatch pre e₁
    let rhs := match ann? with | some ty => .Ascribe core ty | none => core
    return Prod.mk id rhs

partial def letrec1 (letCol : Nat) : TParser σ (Symbol × Expr) := do
  let id <- ID; let pre <- takeMany funBinderID
  let ann? <- option? (COLON *> PType.tyForall false ∅)
  match <- test (lookAhead BAR) with
  | true =>
    let br <- barBranches matchDiscr
    let core := Fix $ Fun id $ transMatch pre $ pointedExp br
    let rhs := match ann? with | some ty => .Ascribe core ty | none => core
    return Prod.mk id rhs
  | false =>
    let e₁ <- eqRhs letCol
    if pre.isEmpty && !e₁ matches Fun .. then
      warn s!"Use let instead of letrec for nonrecursive definition of '{id}'\n"
      let core := transMatch pre e₁
      let rhs := match ann? with | some ty => .Ascribe core ty | none => core
      return Prod.mk id rhs
    else
      let core := Fix $ Fun id $ transMatch pre e₁
      let rhs := match ann? with | some ty => .Ascribe core ty | none => core
      return Prod.mk id rhs

/--
The body of a letexp, in one of the two forms:

1. prefixed by a explicit IN, or
2. a newline followed by an expression aligned to LET

Behaviors should be similar to Lean's do-notation.
-/
partial def letBodyOrIn (letCol : Nat) : TParser σ Expr :=
  (IN *> dumbspaces *> parseExpr) <|> (vspaces *> colEq letCol *> parseExpr)

partial def letDispatch : TParser σ Expr := do
  let letCol <- kwCol "let"
  match <- test REC with
  | false =>
    match <- option? funBinder with
    | some pat =>
      EQ let e₁ <- withInlineBlock letCol parseExpr
      let e₂ <- letBodyOrIn letCol
      return Match #[e₁] #[(#[pat], e₂)]
    | none =>
      -- let grp <- sepBy1 AND let1
      let grp <- alignedBindings (let1 letCol)
      let e₂ <- letBodyOrIn letCol
      return Let grp e₂
  | true =>
    match <- option? funBinder with
    | some pat =>
      EQ let e₁ <- withInlineBlock letCol parseExpr
      let e₂ <- letBodyOrIn letCol
      warn "found non-variable pattern on the left hand side,\nThis expression will be treated as a letexp\n"
      return Match #[e₁] #[(#[pat], e₂)]
    | none =>
      --let grp <- sepBy1 AND letrec1
      let grp <- alignedBindings (letrec1 letCol)
      let e₂ <- letBodyOrIn letCol
      return Let grp e₂
partial def fixpointExp : TParser σ Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funDispatch : TParser σ Expr := do
  FUN
  match <- test (lookAhead BAR) with
  | true => let args <- barBranches matchDiscr; return pointedExp args
  | false =>
    let pat <- takeMany1 funBinderID; ARROW let e <- parseExpr
    return transMatch pat e

partial def condExp     : TParser σ Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

partial def recordExp   : TParser σ Expr :=
  transShorthand <$> (resolveBareRecord =<< braced do sepBy COMMA do
    let f <- ID; EQ; let e <- parseExpr; return (f, e))

partial def recordExpTyped : TParser σ Expr := parenthesized do
  let fs <- braced $ sepBy COMMA $ ID >>= fun f =>
    option? (EQ *> parseExpr) <&> fun
                                  | some e  => (f, e)
                                  | _       => (f, Var f)
  COLON
  match <- PType.tyExp with
  | ty@(.TCon s) | ty@(.TApp (.TCon s) _) =>
    Ascribe (ty := ty) <$> reorderRecord s fs
  | ty => .Ascribe (ty := ty) <$> resolveBareRecord fs

end
end Parsing
