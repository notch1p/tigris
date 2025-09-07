import Tigris.utils

abbrev Name := String

namespace IR

inductive PrimOp where
  | add | sub | mul | div
  | eqInt | eqBool | eqStr
deriving Repr, BEq, Inhabited

inductive Const where
  | unit | int (i : Int) | bool (b : Bool) | str (s : String)
deriving Repr, BEq, Inhabited

mutual


/--
The "Lambda" language similar to that described in CWC for SML.
- Value: immediate values (lambda not yet lifted, captures free vars)
- Rhs: right-hand sides of ANF (all arguments are variables).
- Stmt: single let binding (x := rhs).
- Tail: tail positions (return, application, conditional).
- Expr: statements ending in a tail; also has letVal (Rhs) and letRec (recfun)
-/
inductive Value where
  | var    (x : Name)
  | cst    (k : Const)
  | constr (tag : Name) (fields : Array Name)
  | lam    (param : Name) (body : LExpr)   -- single-argument lambdas; multi-arg via tuples
deriving Repr, Inhabited

inductive Rhs where
  | prim     (op : PrimOp) (args : Array Name)         -- x := op(args)
  | proj     (src : Name) (idx : Nat)                  -- x := π_idx src
  | mkPair   (a b : Name)                              -- x := (a,b)
  | mkConstr (tag : Name) (fields : Array Name)        -- x := Ctag(fields)
  | isConstr (src : Name) (tag : Name) (arity : Nat)   -- x := is_Ctag[src] (boolean)
  | call     (f : Name) (arg : Name)                   -- x := f arg (direct-style call result)
deriving Repr, Inhabited

inductive Stmt where
  | let1 (x : Name) (rhs : Rhs)
deriving Repr, Inhabited

inductive Tail where
  | ret  (x : Name)                       -- return x
  | app  (f : Name) (arg : Name)          -- tail call: f arg
  | cond (condVar : Name) (tBranch eBranch : LExpr)  -- if cond then t else e
  | switchConst (scrut : Name)       -- distinguish constant switch
      (cases : Array (Const × LExpr))
      (default? : Option LExpr)
  | switchCtor (scrut : Name)
      (cases : Array (Name × Nat × LExpr))
      (default? : Option LExpr)
deriving Repr, Inhabited

inductive LExpr where
  | seq    (binds : Array Stmt) (tail : Tail)
  | letVal (x : Name) (v : Value) (body : LExpr)
  /-- Nested let Rhs bindings. -/
  | letRhs (x : Name) (rhs : Rhs) (body : LExpr)
  /--
  Recursive function bindings:
  (although only per-function recursion is supported i.e. no mutual recursion.)
  -/
  | letRec (funs : Array (Name × Name × LExpr)) (body : LExpr)

deriving Repr, Inhabited, BEq
end

attribute [inherit_doc Value] Rhs Stmt Tail LExpr

/-- A top-level function in the Lambda IR. Multiple parameters can be encoded via tuples. -/
structure LFun where
  fid    : Name
  param  : Name
  body   : LExpr
deriving Repr, Inhabited

/-- A module holds a set of functions and the designated main. -/
structure LModule where
  funs : Array LFun
  main : LFun
deriving Repr, Inhabited

/-
Pretty printer (human-readable). We keep it compact and close to a direct-style
functional syntax with explicit lets and tail positions.
-/
section PP open Std Format

@[always_inline, inline] def comma := "," ++ line
@[inline] def fmtName (s : Name) : Format := format s

def fmtConst : Const -> Format
  | .unit => "()"
  | .int i => format i
  | .bool b => format b
  | .str s => reprStr s

def fmtPrim : PrimOp -> Format
  | .add => "ADD" | .sub => "SUB" | .mul => "MUL" | .div => "DIV"
  | .eqInt => "EQⁱ" | .eqBool => "EQᵇ" | .eqStr => "EQˢ"

mutual
partial def fmtValue : Value -> Format
    | .var x       => fmtName x
    | .cst k       => fmtConst k
    | .constr t fs =>
      group $ fmtName t <> paren (joinSep (fs.foldr (List.cons ∘ fmtName) []) comma)
    | .lam p b     =>
      group $ "fun" <> fmtName p <> "↦" ++ indentD (fmtLExpr b)

partial def fmtRhs : Rhs -> Format
    | .prim op args =>
      fmtPrim op ++ paren (joinSep (args.toList.map fmtName) comma)
    | .proj src i => fmtName src ++ sbracket (format i)
    | .mkPair a b =>
      bracket "⟨" (fmtName a ++ comma ++ fmtName b) "⟩"
    | .mkConstr t fs =>
      fmtName t ++ bracket "⟦" (joinSep (fs.toList.map fmtName) comma) "⟧"
    | .isConstr s t ar =>
      "IS" <> fmtName s!"«{t}/{ar}»" <> fmtName s
    | .call f a =>
      fmtName f ++ paren (fmtName a)

partial def fmtStmt : Stmt -> Format
    | .let1 x rhs =>
      group $ fmtName x <> ":=" <+> fmtRhs rhs

partial def fmtTail : Tail -> Format
    | .ret x => "RET" <> (fmtName x)
    | .app f a =>
      fmtName f ++ paren (fmtName a) ++ "ᵀ"
    | .cond c t e =>
      "if" <> fmtName c <> "then" ++ indentD
      (fmtLExpr t) <+> "else" ++ indentD (fmtLExpr e)
    | .switchConst s cases d? =>
      "caseᶜ" <> fmtName s <> "of" ++ indentD
        (joinSep (cases.foldr (List.cons ∘ nestD ∘ one) (defF d?)) line)
    | .switchCtor s cases d? =>
      "case" <> fmtName s <> "of" ++ indentD
        (joinSep (cases.foldr (List.cons ∘ nestD ∘ one') (defF d?)) line)
where
  one kb   := let (k, b) := kb; (fmtConst k <> "→") <+> fmtLExpr b
  one' cab := let (c, ar, b) := cab; (s!"«{fmtName c}/{format ar}»" <> "→") <+> (fmtLExpr b)
  defF d?  := if let some b := d? then [nestD ("∅ →" <+> fmtLExpr b)] else []

partial def fmtLExpr : LExpr -> Format
    | .seq binds tail =>
      if binds.isEmpty then fmtTail tail
      else group $ joinSep
        (binds.foldr (List.cons ∘ nestD ∘ fmtStmt) [fmtTail tail]) "\n"
    | .letVal x v b =>
      group $ "letι"
        <> group (fmtName x <> "=" ++ indentD (fmtValue v))
          ++ "\n"
          ++ (fmtLExpr b)
    | .letRhs x r b =>
      group $ "let"
        <> group (fmtName x <> "=" ++ indentD (fmtRhs r))
          ++ "\n"
          ++ (fmtLExpr b)
    | .letRec funs b =>
      let ffmt
        | (fid, p, body) =>
          group $
            indentD ("label" <> fid ++ paren p ++ ":" ++ indentD (fmtLExpr body))
      group $ "letω"
        <> group ((joinSep (funs.foldr (List.cons ∘ ffmt) []) (line ++ line)) <+> "in")
          ++ "\n"
          ++ (fmtLExpr b)
end

def fmtFun : LFun -> Std.Format
  | {fid, param, body} =>
    group $ (fmtName fid <> paren (fmtName param))
      <> "{" ++ (indentD (fmtLExpr body) ++ line) ++ "}"

def fmtModule : LModule -> Std.Format
  | {funs, main} =>
    let fs := funs.foldr (List.cons ∘ fmtFun) []
    group $ joinSep fs (line ++ line)
      ++ (if funs.isEmpty then .nil else line ++ line)
      ++ fmtFun main
end PP

abbrev M σ := StateRefT Nat (ST σ)
abbrev Env := Std.TreeMap String Name

end IR
