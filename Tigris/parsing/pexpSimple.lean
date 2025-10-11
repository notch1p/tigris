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
        | PVar _ | PWild => (ep, pat', i + 1)
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
   , PVar <$> ID
   , parenthesized patProd
   , parenthesized parsePattern]
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

partial def funapp : TParser σ Expr :=
  chainl1 atom (pure App)

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

partial def appAtom     : TParser σ Expr :=
  chainl1 atom (pure App)

partial def parsePratt (minPrec := 0) : TParser σ Expr := do
  let lhs <- appAtom
  let rec loop (lhs : Expr) : TParser σ Expr := do
    match <- takeBindingOp? minPrec with
    | none => pure lhs
    | some (_sym, {prec, assoc, impl,..}) =>
      let nextMin := if assoc matches .leftAssoc then prec + 1 else prec
      let rhs <- parsePratt nextMin
      loop $ impl lhs rhs
  loop lhs

partial def matchDiscr  : TParser σ $ Array Pattern × Expr := do
  let p <- sepBy1 COMMA parsePattern
  ARROW let body <- parseExpr     return (p, body)

partial def matchExp    : TParser σ Expr := do
  MATCH let e <- sepBy1 COMMA parseExpr; WITH
  let br <- takeMany1 (BAR *> matchDiscr)
                                  return Match e br

partial def let1 : TParser σ (Symbol × Expr) := do
  let id <- ID; let pre <- takeMany funBinderID
  let ann? <- option? (COLON *> PType.tyForall false ∅)
  match <- test BAR with
  | true =>
    let br <- sepBy1 BAR matchDiscr
    let core := transMatch pre $ pointedExp br
    let rhs := match ann? with | some ty => Expr.Ascribe core ty
                               | none => core
    return Prod.mk id rhs
  | false =>
    EQ; let e₁ <- parseExpr;
    let core := transMatch pre e₁
    let rhs := match ann? with | some ty => .Ascribe core ty | none => core
    return Prod.mk id rhs

partial def letrec1 : TParser σ (Symbol × Expr) := do
  let id <- ID; let pre <- takeMany funBinderID
  let ann? <- option? (COLON *> PType.tyForall false ∅)
  match <- test BAR with
  | true =>
    let br <- sepBy1 BAR matchDiscr
    let core := Fix $ Fun id $ transMatch pre $ pointedExp br
    let rhs := match ann? with | some ty => .Ascribe core ty | none => core
    return Prod.mk id rhs
  | false =>
    EQ; let e₁ <- parseExpr
    if pre.isEmpty && !e₁ matches Fun .. then
      warn s!"Use let instead of letrec for nonrecursive definition of '{id}'\n"
      let core := transMatch pre e₁
      let rhs := match ann? with | some ty => .Ascribe core ty | none => core
      return Prod.mk id rhs
    else 
      let core := Fix $ Fun id $ transMatch pre e₁
      let rhs := match ann? with | some ty => .Ascribe core ty | none => core
      return Prod.mk id rhs

partial def letDispatch : TParser σ Expr := do
  LET
  match <- test REC with
  | false =>
    match <- option? funBinder with
    | some pat =>
      EQ let e₁ <- parseExpr; IN let e₂ <- parseExpr
      return Match #[e₁] #[(#[pat], e₂)]
    | none =>
      let grp <- sepBy1 AND let1
      IN; let e₂ <- parseExpr
      return Let grp e₂
  | true =>
    match <- option? funBinder with
    | some pat =>
      EQ let e₁ <- parseExpr; IN let e₂ <- parseExpr
      warn "found non-variable pattern on the left hand side,\nThis expression will be treated as a letexp\n"
      return Match #[e₁] #[(#[pat], e₂)]
    | none =>
      let grp <- sepBy1 AND letrec1
      IN; let e₂ <- parseExpr
      return Let grp e₂
partial def fixpointExp : TParser σ Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funDispatch : TParser σ Expr := do
  FUN
  match <- test BAR with
  | true => let args <- sepBy1 BAR matchDiscr; return pointedExp args
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
  let fs <- braced do sepBy COMMA do
    let f <- ID; EQ; let e <- parseExpr; return (f, e)
  COLON
  match <- PType.tyExp with
  | ty@(.TCon s) | ty@(.TApp s _) =>
    Ascribe (ty := ty) <$> reorderRecord s fs
  | ty => .Ascribe (ty := ty) <$> resolveBareRecord fs

end
end Parsing
