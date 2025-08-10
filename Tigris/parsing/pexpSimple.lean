import Tigris.utils
import Tigris.typing.types
import Tigris.parsing.ppat
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing

def intExp      : TParser Expr := CI <$> ws intLit
def strExp      : TParser Expr := CS <$> ws strLit

def nestMatch (pat : Array Pattern) (e : Expr) : Expr :=  -- Slow
  (·.1) <| pat.foldr (init := (e, pat.size - 1)) fun s (e, i) =>
    match s with
    | PVar s => (Fun s e, i)
    | _ =>
      (Fun (hole i) $ Match (Var $ hole i) #[(s, e)], i - 1)

open TConst in def funBinder := first'
   #[ PConst <$> PInt <$> intLit
    , PConst <$> PStr <$> strLit
    , PVar <$> ID
    , parenthesized patProd
    , parenthesized parsePattern]

mutual
partial def funapp : TParser Expr :=
  chainl1 atom (pure App)

partial def atom : TParser Expr :=
  first' $ #[ parenthesized prodExp
            , withBacktracking letrecExp
            , withBacktracking letExp
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

partial def matchDiscr  : TParser (Pattern × Expr) := do
  let p <- parsePattern
  ARROW let body <- parseExpr     return (p, body)

partial def matchExp    : TParser Expr := do
  MATCH let e <- parseExpr; WITH 
  let hd <- optional BAR *> matchDiscr
  let tl <- takeMany (BAR *> matchDiscr)
                                  return Match e (#[hd] ++ tl)

partial def letExp      : TParser Expr := do
  LET let id <- ID
      let pats <- takeMany funBinder 
  EQ; let e₁ <- parseExpr
  IN; let e₂ <- parseExpr         return Let id (nestMatch pats e₁) e₂

partial def letrecExp   : TParser Expr := withBacktracking do
  LET; REC
      let id <- ID
      let pats <- takeMany funBinder
  EQ  let e₁ <- parseExpr
  IN  let e₂ <- parseExpr         return Let id (Fix $ Fun id $ nestMatch pats e₁) e₂

partial def fixpointExp : TParser Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funExp      : TParser Expr := do
  FUN   let pat <- takeMany1 funBinder
  ARROW let e <- parseExpr
                                  return nestMatch pat e

partial def condExp     : TParser Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

partial def parseExpr : TParser Expr := parsePratt

end
end Parsing

