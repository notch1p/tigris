import Tigris.oldcore2.lam


/-!

- Pure computations remain as CRhs bound by let1.
- All control transfers are tail positions (CTail) and appear only as `CExpr.tail`.
- User functions (CFun) take two parameters: payload and continuation.
- Continuations are first-class only syntactically via letKont; they never escape.
- Calls are eliminated from CRhs; they are expressed as CTail.appFun or CTail.appKont.
- We keep conditionals and case splits as tail terms with CPS bodies in each branch.
- We introduce CRhs.alias and CRhs.const to faithfully represent value lets from Lambda IR.

pipeline:
  Lambda (ANF) ==CC=> Lambda (no lambdas) ==CPS=> CPS IR
-/

namespace CPS
open IR (PrimOp Const comma fmtName fmtConst fmtPrim)
export IR (Shape ShapeMap)

abbrev CName := Name
abbrev Ren := Std.HashMap CName CName

inductive CRhs where
  | prim     (op : PrimOp) (args : Array CName)
  | proj     (src : CName) (idx : Nat)
  | mkPair   (a b : CName)
  | mkConstr (tag : Name) (fields : Array CName)
  | isConstr (src : CName) (tag : Name) (arity : Nat)
  | const    (k : Const)
  | alias    (y : CName)   -- x = y
deriving Repr, Inhabited, BEq

mutual
inductive CTail where
  | appFun      (f : CName) (payload : CName) (k : CName)
  | appKont     (k : CName) (value : CName)
  | ite         (condVar : CName) (tBranch eBranch : CExpr)
  | switchConst (scrut : CName)
                (cases : Array (Const × CExpr))
                (default? : Option CExpr)
  | switchCtor  (scrut : CName)
                (cases : Array (Name × Nat × CExpr))
                (default? : Option CExpr)
  | halt        (value : CName)
  | matchFail   (pat : Array Name)
deriving Repr, Inhabited, BEq

/-- CPS expression in ANF: pure let1 / letKont / local fun groups, ending with a tail.

`let1` carries the static `Shape` of `x` -- set at IR construction time so the
SBCL backend never needs to guess. `letKont`'s param shape is implicit `.unknown`
(it's the result of a function call). -/
inductive CExpr where
  | let1    (x : CName) (sh : Shape) (rhs : CRhs) (body : CExpr)
  | letKont (kid : CName) (param : CName) (kBody : CExpr) (body : CExpr)
  | letRec  (funs : Array CFun) (body : CExpr)
  | tail    (t : CTail)
deriving Repr, Inhabited, BEq

structure CFun where
  fid          : CName
  payloadParam : CName
  /-- Shape of `payloadParam`. For closure-converted code pointers this is
  always `.pair` (payload = `⟨arg, env⟩`); for synthesized entry points
  like `__start` it may be `.unknown`. -/
  payloadShape : Shape := .pair
  kontParam    : CName  -- conventionally a function value (continuation)
  body         : CExpr
deriving Repr, Inhabited, BEq

end

structure CModule where
  funs : Array CFun
  main : CFun
deriving Repr, Inhabited

section PP open Std Format

def fmtShape : Shape -> Format
  | .unknown    => "·"
  | .pair       => "⟨,⟩"
  | .ctor t ar  => s!"«{t}/{ar}»"
  | .fn         => "fn"

def fmtCRhs : CRhs -> Format
  | .prim op args =>
    fmtPrim op ++ paren (joinSep (args.foldr (List.cons ∘ fmtName) []) comma)
  | .proj s i => fmtName s ++ sbracket (format i)
  | .mkPair a b => bracket "⟨" (fmtName a ++ comma ++ fmtName b) "⟩"
  | .mkConstr t fs =>
    fmtName t ++ bracket "⟦" (joinSep (fs.foldr (List.cons ∘ fmtName) []) comma) "⟧"
  | .isConstr s t ar =>
    "IS" <> fmtName s!"«{t}/{ar}»" <> fmtName s
  | .const k => fmtConst k
  | .alias y => fmtName y

mutual
partial def fmtCTail : CTail -> Format
  | .matchFail _ => format "MATCHFAILURE"
  | .appFun f p k =>
    fmtName f ++ paren (fmtName p ++ comma ++ fmtName k)
  | .appKont k v =>
    "APPLY" <> fmtName k ++ paren (fmtName v)
  | .ite c t e =>
    "if" <> fmtName c <> "then" ++ indentD
      (fmtCExpr t)
    <+> "else" ++ indentD
      (fmtCExpr e)
  | .switchConst s cases d? =>
    "caseᶜ" <> fmtName s <> "of" ++ indentD
      (joinSep (cases.foldr (List.cons ∘ nestD ∘ one) (defF d?)) line)
  | .switchCtor s cases d? =>
    "case" <> fmtName s <> "of" ++ indentD
      (joinSep (cases.foldr (List.cons ∘ nestD ∘ one') (defF d?)) line)
  | .halt v => "HALT" <> fmtName v
where
  one  kb  := let (k, b) := kb; (fmtConst k <> "→") <+> fmtCExpr b
  one' cab := let (c, ar, b) := cab; (s!"«{fmtName c}/{format ar}»" <> "→") <+> (fmtCExpr b)
  defF d?  := if let some b := d? then [nestD ("∅ →" <+> fmtCExpr b)] else []


partial def fmtCExpr : CExpr -> Format
  | .let1 x sh r b =>
    group $ "let"
      <> group (fmtName x <> ":" <> fmtShape sh <> "=" ++ indentD (fmtCRhs r))
        ++ "\n"
        ++ (fmtCExpr b)
  | .letKont k p kb b =>
    group $ "letκ"
      <> group (fmtName k <> fmtName p <> "=" ++ indentD (fmtCExpr kb))
    ++ "\n"
    ++ (fmtCExpr b)
  | .letRec funs b =>
    let ffmt (f : CFun) :=
      group $
        indentD ("label" <> f.fid ++ paren (fmtName f.payloadParam
                                          ++ ":" ++ fmtShape f.payloadShape
                                          ++ comma
                                          ++ fmtName f.kontParam)
                ++ ":" ++ indentD (fmtCExpr f.body))
    group $ "letω"
      <> group ((joinSep (funs.foldr (List.cons ∘ ffmt) []) line) <+> "in")
    ++ "\n"
    ++ (fmtCExpr b)
  | .tail t => fmtCTail t
end

def fmtCFun (f : CFun) : Format :=
  group $ (fmtName f.fid ++ paren (fmtName f.payloadParam
                                   ++ ":" ++ fmtShape f.payloadShape
                                   ++ comma
                                   ++ fmtName f.kontParam))
    <> "{" ++ (indentD (fmtCExpr f.body) ++ line) ++ "}"

def fmtCModule (m : CModule) : Format :=
  let fs := m.funs.foldr (List.cons ∘ fmtCFun) []
  group $ joinSep fs (line ++ line)
    ++ (if m.funs.isEmpty then .nil else line ++ line)
    ++ fmtCFun m.main

end PP

end CPS
