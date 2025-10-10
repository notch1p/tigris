import Tigris.utils
import Tigris.typing.ttypes
import Tigris.parsing.ptype
open Expr Lexing Parser Parser.Char Pattern

namespace Parsing

def reorderRecordPat (ctor : Symbol) (fs : Array $ String × Pattern) : TParser σ Pattern := do
  let ({recordFields,..}, _) <- get
  let some order := recordFields.get? ctor | error "unknown record {ty}\n"; throwUnexpected
  let mut mp : Std.HashMap String Pattern := ∅
  for (f, e) in fs do
    if f ∈ mp then
      error s!"duplicate fields '{f}' for record {ctor} pattern\n"
      throwUnexpected
    mp := mp.insert f e
  if order.any (not ∘ mp.contains) || mp.size != order.size then
    error s!"record pattern does not match field set of {ctor}\n"
    throwUnexpected
  let pats := order.map mp.get!
  return .PCtor ctor pats

def resolveBareRecordPat (fs : Array $ String × Pattern) : TParser σ Pattern := do
  let ({recordFields,..}, _) <- get
  let fids := fs.map Prod.fst
  let set : Std.HashSet String := fids.foldl .insert ∅
  letI cand := Std.HashMap.toList <| recordFields.filter fun _ order =>
    order.size == fids.size && order.all set.contains
  match cand with
  | [(ty, _)] => reorderRecordPat ty fs
  | [] => error "no record type matches the given field set\n" *> throwUnexpected
  | %[(ty, _) | _] =>
    warn s!"ambiguous record pattern (using default '{ty}'), consider adding type ascription;\n\
            as we currently do not have type-directed parsing.\n\
            candidates are {cand}\n" *> reorderRecordPat ty fs

variable {σ}
mutual
partial def patAtom : TParser σ Pattern := ws $ first' (combine := simpErrorCombine) $
  #[ patRecordTyped
   , patRecord
   , parenthesized patProd
   , UNDERSCORE $> PWild
   , intLit <&> (PConst ∘ .PInt)
   , (string "true") $> (PConst $ .PBool true)
   , (string "false") $> (PConst $ .PBool false)
   , strLit <&> (PConst ∘ .PStr)
   , do
       let id <- ID;
       if id.isUpperInit then return PCtor id #[]
       else return PVar id
   ]

partial def patProd : TParser σ Pattern := do
  let es <- sepBy COMMA parsePattern
  return match h : es.size with
         | 0 => PConst .PUnit
         | 1 => es[0]
         | _ + 2 => es[0:es.size - 1].foldr PProd' es[es.size - 1]

partial def patRecord : TParser σ Pattern := do
  resolveBareRecordPat =<< braced do sepBy COMMA do
    let f <- ID; EQ; let e <- parsePattern; return (f, e)

partial def patRecordTyped : TParser σ Pattern := do
  let ps <- braced do sepBy COMMA do
    let f <- ID; EQ; let e <- parsePattern; return (f, e)
  COLON
  match <- PType.tyExp ∅ with
  | .TCon s | .TApp s _ => reorderRecordPat s ps
  | _ => resolveBareRecordPat ps
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
