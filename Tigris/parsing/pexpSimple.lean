import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.ppat
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing
variable {σ}
def intExp      : TParser σ Expr := CI <$> ws intLit
def strExp      : TParser σ Expr := CS <$> ws strLit

def transMatch (pat : Array Pattern) (e : Expr) : Expr :=
  if pat.isEmpty then e else
  let hd := Match (pat.mapIdx fun i _ => Var $ hole i) #[(pat, e)]
  pat.size.foldRev (init := hd) fun i _ a => Fun (hole i) a

def pointedExp (discr : Array $ Array Pattern × Expr) : Expr :=
  if h : discr.size = 0 then CUnit
  else discr[0].1.size.foldRev
        (init := Match (discr[0].1.mapIdx fun i _ => Var $ hole i) discr)
        fun i _ a => Fun (hole i) a

def warn (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.warn s)


open TConst in def funBinder : TParser σ Pattern := first'
   #[ ws $ PConst <$> PInt <$> intLit
    , ws $ PConst <$> PStr <$> strLit
    , PVar <$> ID
    , parenthesized patProd
    , parenthesized parsePattern]

mutual
partial def funapp : TParser σ Expr :=
  chainl1 atom (pure App)

partial def atom : TParser σ Expr :=
  first' $ #[ parenthesized prodExp
            , letrecExp
            , letrecPointExp
            , letrecPatExp
            , letExp
            , letPointExp
            , letPatExp
            , funPointed  , funExp
            , fixpointExp , condExp
            , matchExp    , intExp
            , strExp      , varExp]
            |>.map ws

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
  let mut lhs <- appAtom
  let rec loop (lhs : Expr) : TParser σ Expr := do
    match <- takeBindingOp? minPrec with
    | none => pure lhs
    | some (_sym, {prec, assoc, impl}) =>
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

partial def letPatExp   : TParser σ Expr := do
  LET let pat <- funBinder
  EQ  let e₁  <- parseExpr
  IN  let e₂  <- parseExpr        return Match #[e₁] #[(#[pat], e₂)]

partial def letPointExp : TParser σ Expr := do
  LET let id <- ID;
      let br <- takeMany1 (BAR *> matchDiscr)
  IN  let bd <- parseExpr
  return Let id (pointedExp br) bd

partial def letrecPointExp : TParser σ Expr := do
  LET; REC;
      let id <- ID;
      let br <- takeMany1 (BAR *> matchDiscr)
  IN  let bd <- parseExpr
  return Let id (Fix $ Fun id $ pointedExp br) bd

partial def letrecPatExp: TParser σ Expr := do
  LET; REC
      let pat <- funBinder
  EQ  let e₁  <- parseExpr
  IN  let e₂  <- parseExpr
  match pat with
  | PVar id => return Let id (Fix $ Fun id $ e₁) e₂
  | _ => warn "found non-variable pattern on the left hand side,\nThis expression will be treated as a letexp\n"
    return Match #[e₁] #[(#[pat], e₂)]

partial def letExp      : TParser σ Expr := do
  LET let id <- ID
      let pats <- takeMany funBinder
  EQ; let e₁ <- parseExpr
  IN; let e₂ <- parseExpr         return Let id (transMatch pats e₁) e₂

partial def letrecExp   : TParser σ Expr := withBacktracking do
  LET; REC
      let id <- ID
      let pats <- takeMany funBinder
  EQ  let e₁ <- parseExpr
  IN  let e₂ <- parseExpr
  if pats.isEmpty && !e₁ matches Fun .. then
    warn "Use letexp instead of letrec for nonrecursive definition\n"
    return Let id (transMatch pats e₁) e₂
  else return Let id (Fix $ Fun id $ transMatch pats e₁) e₂

partial def fixpointExp : TParser σ Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funExp      : TParser σ Expr := do
  FUN   let pat <- takeMany1 funBinder
  ARROW let e <- parseExpr
                                  return transMatch pat e

partial def funPointed  : TParser σ Expr := do
  FUN let a <- takeMany1 (BAR *> matchDiscr)
                                  return pointedExp a

partial def condExp     : TParser σ Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

partial def parseExpr : TParser σ Expr := parsePratt

end
end Parsing
