import Tigris.core.lam


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
deriving Repr, Inhabited, BEq

/-- CPS expression in ANF: pure let1 / letKont / local fun groups, ending with a tail. -/
inductive CExpr where
  | let1    (x : CName) (rhs : CRhs) (body : CExpr)
  | letKont (kid : CName) (param : CName) (kBody : CExpr) (body : CExpr)
  | letRec  (funs : Array CFun) (body : CExpr)
  | tail    (t : CTail)
deriving Repr, Inhabited, BEq

structure CFun where
  fid          : CName
  payloadParam : CName
  kontParam    : CName
  body         : CExpr
deriving Repr, Inhabited, BEq

end

structure CModule where
  funs : Array CFun
  main : CFun
deriving Repr, Inhabited

section PP open Std Format

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
  | .let1 x r b =>
    group $ "let"
      <> group (fmtName x <> "=" ++ indentD (fmtCRhs r))
        ++ "\n"
        ++ (fmtCExpr b)
  | .letKont k p kb b =>
    group $ "letκ"
      <> group (fmtName k <> fmtName p <> "=" ++ indentD (fmtCExpr kb))
    ++ "\n"
    ++ (fmtCExpr b)
  | .letRec funs b =>
    let ffmt
      | {fid, payloadParam, kontParam, body} =>
        group $
          indentD ("label" <> fid ++ paren (fmtName payloadParam
                                            ++ comma
                                            ++ fmtName kontParam)
                  ++ ":" ++ indentD (fmtCExpr body))
    group $ "letω"
      <> group ((joinSep (funs.foldr (List.cons ∘ ffmt) []) line) <+> "in")
    ++ "\n"
    ++ (fmtCExpr b)
  | .tail t => fmtCTail t
end

def fmtCFun : CFun -> Format
  | {fid, payloadParam, kontParam, body} =>
    group $ (fmtName fid <> paren (fmtName payloadParam
                                   ++ comma
                                   ++ fmtName kontParam))
      <> "{" ++ (indentD (fmtCExpr body) ++ line) ++ "}"

def fmtCModule : CModule -> Format
  | {funs, main} =>
    let fs := funs.foldr (List.cons ∘ fmtCFun) []
    group $ joinSep fs (line ++ line)
      ++ (if funs.isEmpty then .nil else line ++ line)
      ++ fmtCFun main

end PP

end CPS
