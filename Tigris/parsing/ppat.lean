import Tigris.utils
import Tigris.typing.types
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing
variable {σ}
mutual
partial def patAtom : TParser σ Pattern := ws $ first' (combine := simpErrorCombine) $
  #[ parenthesized patProd
   , UNDERSCORE $> PWild
   , intLit <&> (PConst ∘ .PInt)
   , (string "true") $> (PConst $ .PBool true)
   , (string "false") $> (PConst $ .PBool false)
   , strLit <&> (PConst ∘ .PStr)
   , do
       let id <- ID;
       if isUpperInit id then return PCtor id #[]
       else return PVar id
   ]

partial def patProd : TParser σ Pattern := do
  let es <- sepBy COMMA parsePattern
  return match h : es.size with
         | 0 => PConst .PUnit
         | 1 => es[0]
         | _ + 2 => es[0:es.size - 1].foldr PProd' es[es.size - 1]

partial def patApp : TParser σ Pattern := do
  let hd <- patAtom
  match hd with
  | PCtor n #[] =>
    PCtor n <$> takeMany patAtom
  | _ => return hd

partial def parsePattern (minPrec : Nat := 0) : TParser σ Pattern := do
  let lhs <- patApp
  let rec loop (lhs : Pattern) : TParser σ Pattern := do
    match <- takeBindingOp? minPrec with
    | none => pure lhs
    | some (_sym, entry) =>
      let nextMin :=
        match entry.assoc with
        | .leftAssoc  => entry.prec + 1
        | .rightAssoc => entry.prec
      let rhs <- parsePattern nextMin
      let expr' := η₂' $ entry.impl (Var "_") (Var "_")
      match expr', lhs with
      | Var "_", PCtor ctor args =>
        loop (PCtor ctor $ args.push rhs)
      | Var ctor, lhs => loop (PCtor ctor #[lhs, rhs])
      | _, _ =>
        error s!"{repr expr'} or {lhs} does not reduce to a (applicable) pattern\n"
        throwUnexpected
  loop lhs
end
end Parsing
