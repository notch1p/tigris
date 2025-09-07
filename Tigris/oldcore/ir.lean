import Tigris.utils
namespace CPS

abbrev Name := String
abbrev Label := String

inductive Const | unit | int (_ : Int) | bool (_ : Bool) | str (_ : String)
deriving BEq, Repr, Inhabited

inductive Atom | var (x : Name) | cst (k : Const)
deriving BEq, Repr, Inhabited

inductive PrimOp where
  | add | sub | mul | div
  | eqInt | eqBool | eqStr
deriving Repr, BEq

inductive Rhs where
  | prim : PrimOp -> Array Atom -> Rhs
  | proj : Name -> Nat -> Rhs
  | mkPair (_ _ : Name)
  | mkConstr : Name -> Array Name -> Rhs
  | isConstr (src : Name) (cname : Name) (arity : Nat)
  | mkClosure (fid : Name) (env : Array Name)
deriving Repr, BEq, Inhabited

inductive Stmt where
  | let1 (x : Name) (rhs : Rhs)
deriving Repr, BEq, Inhabited
inductive Term where
  | appFun     (f : Name) (arg : Name) (k : Name)
  | appKnown   (fid : Name) (env : Array Name) (arg : Name) (k : Name)
  | ret        (k : Name) (v : Name)
  | ifGoto     (cond : Name) (thenLbl : Label) (elseLbl : Label)
               (argsThen : Array Name := #[])
               (argsElse : Array Name := #[])
  | switchCtor (scrut : Name)
               (alts : Array (Name × Nat × Label × Array Name))
               (default? : Option (Label × Array Name) := none)
  | goto       (lbl : Label) (args : Array Atom)
  | halt       (v : Name)
deriving Repr, BEq

structure Block where
  label  : Label
  params : Array Name
  body   : Array Stmt
  term   : Term
deriving Repr, BEq

structure Fun where
  fid    : Name
  params : Array Name
  blocks : Array Block
  entry  : Label
deriving Repr, BEq

structure Module where
  funs : Array Fun
  main : Fun
deriving Repr, BEq


section PP open Std Format ToFormat
@[always_inline, inline] def comma := "," ++ line
@[inline] def fmtName (s : Name) : Format := format s
def fmtConst : Const -> Format
  | .unit => "𝟙"
  | .int i => format i
  | .bool b => format b
  | .str s => reprStr s
@[inline]
def fmtAtom : Atom -> Format
  | .var x => fmtName x
  | .cst k => fmtConst k
def fmtOp : PrimOp -> Format
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .eqInt => "eqInt" | .eqBool => "eqBool" | .eqStr => "eqStr"

def fmtRhs : Rhs -> Format
  | .prim op args =>
    group $ fmtOp op <> paren (joinSep (args.foldr (List.cons ∘ fmtAtom) []) comma)
  | .proj src i =>
    group $ "π" ++ i.toSubscriptString <> fmtName src
  | .mkPair x y =>
    group $ "×" <> paren (fmtName x ++ comma ++ fmtName y)
  | .mkConstr c as =>
    group $ fmtName c <> paren (joinSep (as.foldr (List.cons ∘ fmtName) []) comma)
  | .isConstr src c a =>
    group $ "is" <> fmtName c <> (sbracket ∘ format) a <> fmtName src
  | .mkClosure fid env =>
    group $ "λ" <> fmtName fid <> sbracket (joinSep (env.foldr (List.cons ∘ fmtName) []) comma)

@[inline] def fmtStmt : Stmt -> Format
  | .let1 x rhs => group $ fmtName x <> ":=" <> fmtRhs rhs

def fmtTerm : Term -> Format
  | .appFun f a k =>
    group $ "CALL"
      <> fmtName f
      <> paren (fmtName a ++ comma ++ fmtName k)
  | .appKnown fid env a k =>
    group $ "CALLKNOWN"
      <> fmtName fid
      <> sbracket (joinSep (env.foldr (List.cons ∘ fmtName) []) comma)
      <> paren (fmtName a ++ comma ++ fmtName k)
  | .ret k v =>
    group $ "RET" <> paren (fmtName k ++ comma ++ fmtName v)
  | .ifGoto c t e argst argse =>
    group $
      "COND" <> fmtName c ++ "\n" ++ nestD (fmtName t
      <> paren (joinSep (argst.foldr (List.cons ∘ fmtName) []) comma))
      ++ "\n" ++ nestD (fmtName e
      <> paren (joinSep (argse.foldr (List.cons ∘ fmtName) []) comma))
  | .switchCtor s alts defs? =>
    let fa
      | (c, ar, l, as) =>
        group $ fmtName c <> (sbracket ∘ format) ar <> "→" <> fmtName l
             <> paren (joinSep (Array.foldr (List.cons ∘ fmtName) [] as) comma)
    let fd :=
      if let some (l, as) := defs? then
        group ("_ → " <> fmtName l <> paren (joinSep (as.foldr (List.cons ∘ fmtName) []) comma))
      else .nil
    group $ "CASE" <> fmtName s <> "OF" <+>
      (joinSep (alts.foldr (List.cons ∘ nestD ∘ fa) []) "\n") ++ "\n" ++ fd
  | .goto l as =>
    group $ "GOTO" <> fmtName l <> paren (joinSep (as.foldr (List.cons ∘ fmtAtom) []) comma)
  | .halt v => group $ "HALT" <> fmtName v

def fmtBlock : Block -> Format
  | {label, params, body, term} =>
    let hd := fmtName label <> paren (joinSep (params.foldr (List.cons ∘ fmtName) []) comma) <> ":-"
    let stmts := body.foldr (List.cons ∘ fmtStmt) [] |> (joinSep · line)
    let term := nestD $ fmtTerm term
    let content := if body.isEmpty then term else stmts <+> term
    hd <+> content

def fmtFun : Fun -> Format
  | {fid, params, blocks,..} =>
    let hd := fmtName fid <> paren (joinSep (params.foldr (List.cons ∘ fmtName) []) comma)
    let b := blocks.foldr (List.cons ∘ nestD ∘ fmtBlock) [] |> (joinSep · (line ++ line))
    hd <> "{" ++ nestD (line ++ b) <+> "}"

def fmtModule : Module -> Format
  | {funs, main} =>
    let fs := funs.foldr (List.cons ∘ fmtFun) [] |> (joinSep · (line ++ line))
    let main := fmtFun main
    group $ fs ++ (if funs.isEmpty then .nil else line ++ line) ++ main


end PP

end CPS
