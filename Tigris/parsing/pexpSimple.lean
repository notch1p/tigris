import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.ppat
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing

def intExp      : TParser Expr := CI <$> ws intLit
def strExp      : TParser Expr := CS <$> ws strLit

def transMatch (pat : Array Pattern) (e : Expr) : Expr :=
  let hd := Match (pat.mapIdx fun i _ => Var $ hole i) #[(pat, e)]
  pat.size.foldRev (init := hd) fun i _ a => Fun (hole i) a

def pointedExp (discr : Array $ Array Pattern × Expr) : Expr :=
  if h : discr.size = 0 then CUnit
  else discr[0].1.size.foldRev
        (init := Match (discr[0].1.mapIdx fun i _ => Var $ hole i) discr)
        fun i _ a => Fun (hole i) a

open TConst in def funBinder := first'
   #[ ws $ PConst <$> PInt <$> intLit
    , ws $ PConst <$> PStr <$> strLit
    , PVar <$> ID
    , parenthesized patProd
    , parenthesized parsePattern]

mutual
partial def funapp : TParser Expr :=
  chainl1 atom (pure App)

partial def atom : TParser Expr :=
  first' $ #[ parenthesized prodExp
            , letrecExp
            , letrecPointExp
            , letrecPatExp
            , letExp
            , letPointExp
            , letPatExp
            , fixpointExp           , funExp
            , condExp               , matchExp
            , intExp                , strExp
            , varExp]
            |>.map ws

partial def prodExp : TParser Expr := do
  let es <- sepBy COMMA (parsePratt 0)
  return match h : es.size with
         | 0 => CUnit
         | 1 => transShorthand es[0]
         | _ + 2 => es[0:es.size - 1].foldr (Prod' ∘ transShorthand) es[es.size - 1]

partial def varExp      : TParser Expr :=
  ID <&> fun
         | "true"                => CB true
         | "false"               => CB false
         | v                     => Var v

partial def appAtom     : TParser Expr :=
  chainl1 atom (pure App)

partial def parsePratt (minPrec := 0) : TParser Expr := do
  let mut lhs <- appAtom
  let rec loop (lhs : Expr) : TParser Expr := do
    match <- takeBindingOp? minPrec with
    | none => pure lhs
    | some (_sym, {prec, assoc, impl}) =>
      let nextMin := if assoc matches .leftAssoc then prec + 1 else prec
      let rhs <- parsePratt nextMin
      loop $ impl lhs rhs
  loop lhs

partial def matchDiscr  : TParser $ Array Pattern × Expr := do
  let p <- sepBy1 COMMA parsePattern
  ARROW let body <- parseExpr     return (p, body)

partial def matchExp    : TParser Expr := do
  MATCH let e <- sepBy1 COMMA parseExpr; WITH
  let br <- takeMany1 (BAR *> matchDiscr)
                                  return Match e br

partial def letPatExp   : TParser Expr := do
  LET let pat <- funBinder
  EQ  let e₁  <- parseExpr
  IN  let e₂  <- parseExpr        return Match #[e₁] #[(#[pat], e₂)]

partial def letPointExp : TParser Expr := do
  LET let id <- ID;
      let br <- takeMany1 (BAR *> matchDiscr)
  IN  let bd <- parseExpr
  return Let id (pointedExp br) bd

partial def letrecPointExp : TParser Expr := do
  LET; REC; 
      let id <- ID;
      let br <- takeMany1 (BAR *> matchDiscr)
  IN  let bd <- parseExpr
  return Let id (Fix $ Fun id $ pointedExp br) bd

partial def letrecPatExp: TParser Expr := do
  LET; REC
      let pat <- funBinder
  EQ  let e₁  <- parseExpr
  IN  let e₂  <- parseExpr        return Match #[e₁] #[(#[pat], e₂)]

partial def letExp      : TParser Expr := do
  LET let id <- ID
      let pats <- takeMany funBinder
  EQ; let e₁ <- parseExpr
  IN; let e₂ <- parseExpr         return Let id (transMatch pats e₁) e₂

partial def letrecExp   : TParser Expr := withBacktracking do
  LET; REC
      let id <- ID
      let pats <- takeMany funBinder
  EQ  let e₁ <- parseExpr
  IN  let e₂ <- parseExpr         return Let id (Fix $ Fun id $ transMatch pats e₁) e₂

partial def fixpointExp : TParser Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funExp      : TParser Expr := do
  FUN   let pat <- takeMany1 funBinder
  ARROW let e <- parseExpr
                                  return transMatch pat e

partial def condExp     : TParser Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

partial def parseExpr : TParser Expr := parsePratt

end
end Parsing

