import Tigris.utils
import Tigris.typing.types
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing
mutual

partial def funapp : TParser Expr := 
  chainl1 atom (pure App)

partial def atom : TParser Expr :=
  first' $ #[ parenthesized prodExp 
            , letrecExp             , letExp
            , fixpointExp           , funExp
            , condExp               , matchExp
            , intExp                , strExp
            , varExp                , parenthesized opSection]
            |>.map ws

partial def prodExp : TParser Expr := do
  let es <- sepBy COMMA parseExpr
  return match h : es.size with
         | 0 => CUnit
         | 1 => es[0]
         | _ + 2 => es[0:es.size - 1].foldr Prod' es[es.size - 1]

partial def intExp      : TParser Expr := ws INT >>= pure ∘ CI

partial def strExp      : TParser Expr :=
  CS <$> (char '"' *>
            foldl .push "" (tokenFilter (· != '"'))
          <* char '"')

partial def varExp      : TParser Expr :=
  ID >>= pure ∘ fun
          | "true"                => CB true
          | "false"               => CB false
          | v                     => Var v

partial def opMatcher (arr : Array $ Nat × String) : TParser OpIndex :=
  first' $ arr.map fun (prec, s) => string s >>= pure ∘ (prec, ·)

partial def opSection   : TParser Expr := do
  let e₁ <- option? parseExpr
  let tb <- get
  let k <- opMatcher tb.keysArray
  let e₂ <- option? parseExpr
  if let some (op, _) := tb.get? k then
    match e₁, e₂ with
    | some e₁, some e₂ =>         return op e₁ e₂
    | _, some e₂ =>               return Fun "y" $ (flip op $ e₂) $ Var "y"
    | some e₁, _ =>               return Fun "x" $ op e₁ $ Var "x"
    | none, none =>               return Fun "x" $ Fun "y" $ op (Var "x") (Var "y")
  else unreachable!

partial def basePattern : TParser Pattern := do
      (kw "_" *> pure PWild) 
  <|> (parenthesized patApps)
  <|> do
        let id <- ID
        if isUpperInit id then return PCtor id #[]
        else return PVar id

partial def patApps : TParser Pattern := do
  let hd <- basePattern
  match hd with
  | PCtor n #[] =>
    PCtor n <$> takeMany basePattern
  | _ => return hd

/- Shunting-yard -/
partial def patWithOps : TParser Pattern := do
  let tb <- get
  let lhs <- patApps
  let pairs <- takeMany do
    let k <- ws $ opMatcher tb.keysArray
    let rhs <- patApps
    pure (k, rhs)

  if pairs.isEmpty then
    pure lhs
  else
    let out : List Pattern := [lhs]
    let ops : List (Nat × Associativity × String) := []

    let rec reduceWhile (out : List Pattern) (ops : List (Nat × Associativity × String))
                        (prec : Nat) (assoc : Associativity)
                        : List Pattern × List (Nat × Associativity × String) :=
      match ops with
      | [] => (out, ops)
      | (pTop, _, cTop) :: ops' =>
        let cond :=
          match assoc with
          | .leftAssoc  => decide $ prec <= pTop
          | .rightAssoc => decide $ prec <  pTop
        if cond then
          match out with
          | r :: l :: out' =>
              let pat := PCtor cTop #[l, r]
              reduceWhile (pat :: out') ops' prec assoc
          | _ => (out, ops)
        else
          (out, ops)

    let (out, ops) <- pairs.foldlM (init := (out, ops)) fun (out, ops) (k, rhs) => do
      let some (opExpr, assoc) := tb.get? k | unreachable!
      let expanded := η₂' $ opExpr (Var "_") (Var "_")
      let ctorName <-
        match expanded with
        | Var op => pure op
        | other  =>
          throwUnexpectedWithMessage none
            s!"Invalid match pattern with operator `{k.2}`:\n\
               expansion {repr other} does not reduce to a constructor."

      let prec := k.1
      let (out', ops') := reduceWhile out ops prec assoc
      return (rhs :: out', (prec, assoc, ctorName) :: ops')

    let rec reduceAll (out : List Pattern) : List (Nat × Associativity × String) -> List Pattern
      | [] => out
      | (_, _, c) :: ops' =>
        match out with
        | r :: l :: out' =>
            reduceAll (PCtor c #[l, r] :: out') ops'
        | _ => out
    let outFinal := reduceAll out ops
    match outFinal with
    | [p] => pure p
    | _   => throwUnexpectedWithMessage none "Pattern operator parsing error (stack underflow)."

partial def matchDiscr  : TParser (Pattern × Expr) := do
  let p <- patWithOps
  ARROW let body <- parseExpr     return (p, body)

partial def matchExp    : TParser Expr := do
  MATCH let e <- parseExpr; WITH 
  let hd <- optional BAR *> matchDiscr
  let tl <- takeMany (BAR *> matchDiscr)
                                  return Match e (#[hd] ++ tl)

partial def letExp      : TParser Expr := do
  LET let id <- ID
      let a <- takeMany ID
  EQ; let e₁ <- parseExpr
  IN; let e₂ <- parseExpr         return Let id (a.foldr Fun e₁) e₂

partial def letrecExp   : TParser Expr := do
  LET; REC
      let id <- ID
      let a <- takeMany ID
  EQ  let e₁ <- parseExpr
  IN  let e₂ <- parseExpr         return Let id (Fix $ Fun id $ a.foldr Fun e₁) e₂

partial def fixpointExp : TParser Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

partial def funExp      : TParser Expr := do
  FUN   let var <- takeMany1 ID
  ARROW let e <- parseExpr        return var.foldr Fun e

partial def condExp     : TParser Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

partial def parseExpr : TParser Expr := 
  buildOpParser funapp =<< get

end
end Parsing
