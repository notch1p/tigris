import Tigris.typing.fexpr

/--
info: Lean.Compiler.LCNF.Code (pu : Lean.Compiler.LCNF.Purity) : Type
-/
#guard_msgs in
#check Lean.Compiler.LCNF.Code

/-!
# TCNF

Simliar to Lean's LCNF and GHC's STG.
We stole the trick of making the spine `Code` dependently-typed,
indexed by `Phase`, so that we can make any node phase-specific. (CC-or-not)


- Function application.

IR node                          Head  Meaning
============================================================================
`app c (env++as)` after KOC      K     direct; saturated
`app f as`, `|args| = arity[f]`  K     saturated call of a known closure
`app f as`, arity unknown        U     generic call, arg count may not match
`pap f as`, arity known          K     partial
`pap f as`, arity unknown        U     partial; unknown arity

See also
1. Maurer, Luke, et al. "Compiling without continuations." Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation. 2017.
2. Jones, Simon L. Peyton. "Implementing lazy functional languages on stock hardware: the Spineless Tagless G-machine." Journal of functional programming 2.2 (1992): 127-202.
3. Lean.Compiler.LCNF
-/

namespace TCNF

inductive Phase where
  /-- capturing `Code.fun` definitions are allowed -/
  | preCC
  /-- all functions have been lifted to top-level
  `Decl`s; the only function values are `LetValue.mkClos`
  and top-level code pointers. `Code.fun` should be eliminated -/
  | postCC
deriving DecidableEq, BEq, Hashable, Repr, Inhabited

open scoped Lean.Compiler.LCNF in
scoped macro "phase_tac" : tactic => `(tactic|purity_tac)

/-- A unique binder identifier. Uses are bare `FVarId`s; the actual name
lives on the binding site (`Param`/`LetDecl`/`FunDecl`/`Decl`) as a hint. -/
abbrev FVarId := Nat

abbrev Tag := String

inductive PrimOp where
  | add | sub | mul | div
  | eqInt | eqBool | eqStr
deriving DecidableEq, BEq, Hashable, Repr, Inhabited

/-- ANF Atoms -/
inductive Atom where
  | fvar   (fvarId : FVarId)
  | lit    (k : TConst)
  /-- A computationally-irrelevant argument (former type/dictionary slot). -/
  | erased
deriving BEq, Hashable, Repr, Inhabited

/--
  Note: not mutally recursive with `Code`
  as functions are `Code.fun`/`Code.jp` declarations, not RHS.
-/
inductive LetValue (φ : Phase) where
  | lit    (k : TConst)
  | pair   (p q : Atom)
  /-- product projection. -/
  | proj   (idx : Nat) (src : FVarId)
  /-- data-constructor / dictionary field projection.
  This is an afterthought to make codegen emit the struct accessor directly. -/
  | field  (tag : Tag) (idx : Nat) (src : FVarId)
  /-- _saturated_ data constructor. Under-applied constructors are
  eta-expanded to a `fun`/`pap` during lowering. -/
  | ctor   (tag : Tag) (args : Array Atom)
  /-- Apply a primitive operation. -/
  | prim   (op : PrimOp) (args : Array Atom)
  /-- direct call to a foreign function by its raw name; bypasses
  the clos/eval-apply convention and eta-expanded to a wrapper decl. -/
  | extern (name : String) (args : Array Atom)
  /-- N-ary application of a function value. When `head` is a known function,
  `args.size` equals its arity (a direct call); an unknown head is a
  generic eval/apply. Over-application is a chain of `app`s. -/
  | app    (head : FVarId) (args : Array Atom)
  | pap    (head : FVarId) (args : Array Atom)
  /-- ctor tag test -/
  | isCtor (src : FVarId) (tag : Tag) (arity : Nat)
  /-- explicit closure `𝐂⟦code, env⟧`. Only exists _after_ CC -/
  | mkClos (code : FVarId) (env : Array Atom) (h : φ = .postCC := by phase_tac)
deriving Inhabited, BEq, Hashable

/-- a let binding. `ty` should be monomorphic. -/
structure LetDecl (φ : Phase) where
  fvarId     : FVarId
  binderName : String
  ty         : MLType
  value      : LetValue φ
deriving Inhabited, BEq, Hashable

/-- function/join-point/alternative parameter. -/
structure Param where
  fvarId     : FVarId
  binderName : String
  ty         : MLType
deriving Repr, Inhabited, BEq, Hashable

mutual -- can't use with/computed_field in mutual block for some reason
structure FunDecl (φ : Phase) where
  fvarId     : FVarId
  binderName : String
  params     : Array Param
  ty         : MLType
  body       : Code φ

inductive Alt (φ : Phase) where
  | ctor    (tag : Tag) (params : Array Param) (k : Code φ)
  | const   (k : TConst) (code : Code φ)
  /-- fallback -/
  | default (code : Code φ)


/-- The IR spine: a sequence of binders terminated by a control-flow node.
Continuations after branches are shared _join points_ (`jp`) reached by `jmp`,
so no branch duplicates its continuation and match-failure is materialized once. -/
inductive Code (φ : Phase) where
  /-- bracketed to avoid being syntax highlighted as a keyword -/
  | «let»   (decl : LetDecl φ) (k : Code φ)
  /-- Define a possibly capturing local function. -/
  | «fun»   (decl : FunDecl φ) (k : Code φ) (h : φ = .preCC := by phase_tac)
  /-- Define a **join point**, second class. similiar to the continuation in CPS module. -/
  | jp      (decl : FunDecl φ) (k : Code φ)
  /-- jump to a join point with arguments matching its params. -/
  | jmp     (jp : FVarId) (args : Array Atom)
  /-- case analysis, including conditionals -/
  | cases   (discr : FVarId) (resultTy : MLType) (alts : Array $ Alt φ)
  | ret     (val : Atom)
  /-- `ty` is the unreachable result type. -/
  | unreach (ty : MLType)
end

deriving instance Inhabited for Code, FunDecl, Alt

@[inline] def Alt.getCode : Alt φ -> Code φ
  | .ctor _ _ k | .const _ k | .default k => k
@[inline] def Alt.getParams : Alt φ -> Array Param
  | .ctor _ ps _ => ps
  | .const .. | .default .. => #[]

namespace Code
variable {φ : Phase}
@[inline] def isFun : Code φ -> Bool := (· matches «fun» ..)
@[inline] def isJp  : Code φ -> Bool := (· matches jp ..)
@[inline] def isLet : Code φ -> Bool := (· matches «let» ..)
@[inline] def isDecl : Code φ -> Bool
  | .let .. | .fun .. | .jp .. => true
  | _ => false
end Code

/-- toplevel decl.

- program's toplevel bindings pre CC, and additionally includes
- lifted closures post CC.

Note that `params` is empty for a value/thunk. -/
structure Decl (φ : Phase) where
  /-- Global identity of this decl. Top-level names are interned to a stable
  `FVarId`; a CC-lifted function keeps the id of its original `Code.fun`. -/
  fvarId    : FVarId
  name      : String
  params    : Array Param
  ty        : MLType
  body      : Code φ
  arity     : Nat := params.size -- cache it
  recursive : Bool := false
deriving Inhabited

structure Module (φ : Phase) where
  decls : Array (Decl φ)
  main  : Decl φ
deriving Inhabited


abbrev CodePre  := Code .preCC
abbrev CodePost := Code .postCC

section Monads open MLType FExpr
structure NFState where
  nextId       : Nat := 1
  arity        : Std.HashMap FVarId Nat := ∅
  ctors        : Std.HashMap String Nat := ∅

  externs      : Std.HashMap String FVarId := ∅ -- bidirectional map
  /--
  stores actual externs. Allowing the codegen to check an fvar against it.
  -/
  externNames  : Std.HashMap FVarId String := ∅

  /- ctor field types -/
  fieldTys     : Std.HashMap String (Array MLType) := ∅
  /-- tyctor bound TVs -/
  ctorTyParams : Std.HashMap String (List TV) := ∅
  /-- datatype declarations -/
  tyDecl       : TyMap := ∅
  h : nextId >= 1 := by omega
deriving Inhabited

abbrev LowerM    := EIO String
abbrev CompilerM := StateRefT NFState LowerM -- may switch to ST, now for easier debugging

def unwrapTSch : MLType -> MLType
  | TSch (.Forall _ _ps t) => /-ps.foldr (TArr ∘ predToApp)-/ t
  | t => t

def stripTy : FExpr -> FExpr
  | FExpr.TyApp f _ | FExpr.TyLam _ f => stripTy f
  | Let bs body ty =>
    Let (bs.attach.map fun ⟨b, mem⟩ =>
          match h : b with
          | (id, sch, fe) =>
            have := prod_sizeOf_lt_snd sch fe
            have := h ▸ prod_sizeOf_lt_snd id (sch, fe)
            have := Array.sizeOf_lt_of_mem $ h ▸ mem
            (id, sch, stripTy fe))
      (stripTy body)
      (unwrapTSch ty)
  | Proj fe s id ty => Proj (stripTy fe) s id (unwrapTSch ty)
  | Fix e ty => Fix (stripTy e) (unwrapTSch ty)
  | Match ds bs res ex red =>
    Match (ds.map stripTy)
      (bs.attach.map fun ⟨b, mem⟩ =>
        match h : b with
        | (pat, e) =>
          have := h ▸ prod_sizeOf_lt_snd pat e
          have := Array.sizeOf_lt_of_mem (h ▸ mem)
          (pat, stripTy e))
      (unwrapTSch res) ex red
  | Cond c t e ty => Cond (stripTy c) (stripTy t) (stripTy e) (unwrapTSch ty)
  | Prod' p q ty => Prod' (stripTy p) (stripTy q) (unwrapTSch ty)
  | App f a ty => App (stripTy f) (stripTy a) (unwrapTSch ty)
  | Fun p pty b ty => Fun p (unwrapTSch pty) (stripTy b) (unwrapTSch ty)
  | Var x ty => Var x (unwrapTSch ty)
  | t => t

@[inline] def fresh : CompilerM Nat := modifyGet step1
where step1 : NFState -> Nat × NFState
  | s@{nextId, ..} => (nextId + 1, {s with nextId := nextId + 1, h := by omega})

@[inline] def setArity (fv : FVarId) (n : Nat) : CompilerM Unit :=
  modify fun s => {s with arity := s.arity.insert fv n}

/-- the special Id 0 is used to mark runtime pattern matching error, guaranteed by `NFState.h` -/
def matchFailFVar : FVarId := 0
def dummyTy : MLType := .TVar ⟨"_"⟩

end Monads

end TCNF

namespace TCNF.PP open Std Format
/-!
additional helpers defined in utils.lean:

fillBeside (f₁ f₂ : Std.Format) := f₁ ++ line ++ f₂
spaceBeside (f₁ f₂ : Std.Format) := f₁ ++ " " ++ f₂
infixl : 60 " <+> " => fillBeside
infixl : 60 " <> " => spaceBeside
joinSep' (arr : Array α) (sep : Format) -- same as joinSep but works with Arrays.

-/
@[always_inline, inline] def comma := "," ++ line
@[always_inline, inline] def colon := ":" ++ line
@[always_inline, inline] def semi := ";" ++ line
@[always_inline, inline] def bar := "|" ++ line
instance: ToFormat PrimOp where
  format
  | .add => "ADD" | .sub => "SUB" | .mul => "MUL" | .div => "DIV"
  | .eqInt => "EQⁱ" | .eqBool => "EQᵇ" | .eqStr => "EQˢ"

instance : ToFormat Atom where
  format
  | .fvar x => s!"#{x}"
  | .lit k => format k
  | .erased => "∅"

section variable {φ : Phase}

def fmtValue : LetValue φ -> Format
  | .lit k     => format k
  | .pair p q  => bracket "⟨" (format p ++ comma ++ format q) "⟩"
  | .proj i s    => s!"#{s}" ++ sbracket (format i)                   -- s[i]
  | .field c i s => s!"#{s}@{c}" ++ sbracket (format i)               -- s@c[i]
  | .ctor c as =>
    let as := nestD $ bracket "⟦" (joinSep' as comma) "⟧"    -- c⟦as,*⟧
    group $ c ++ as
  | .app f as =>
    let f := s!"#{f}"
    let as := paren $ nest f.length $ joinSep' as comma
    group $ f ++ as
  | .prim f as =>                                                     -- f(as,*)
    let as := paren $ nestD $ joinSep' as comma
    group $ format f ++ as
  | .extern nm as =>                                                  -- @nm(as,*)
    let as := paren $ nestD $ joinSep' as comma
    group $ ("@" ++ nm) ++ as
  | .pap f as =>                                                      -- fᵖ(as,*)
    let f := s!"#{f}ᵖ"
    let as := paren $ nest f.length $ joinSep' as comma
    group $ f ++ as
  | .isCtor s t a =>                                                  -- s is «t/a»
    fill $ nestD $ paren $ format s <+> "is" <+> s!"«{t}/{a}»"
  | .mkClos c e _ =>                                                  -- 𝐂⟦c, e,*⟧
    let fvE := if e.isEmpty then .nil else line ++ bar ++ joinSep' e comma
    let ce := nestD $ bracket "⟦" (format c ++ fvE) "⟧"
    group $ "𝐂" ++ ce

def fmtLetDecl : LetDecl φ -> Format -> Format
  | {fvarId, binderName, ty, value}, k =>
    group $ "let"
      <> fill (s!"{binderName}#{fvarId}" ++ nestD
                (line ++ ":" <> format ty <> "=" <+> fmtValue value))
      ++ semi ++ k

def fmtParam : Param -> Format
  | {fvarId, binderName, ty} =>
    fill $ binderName ++ format fvarId <> nestD (colon ++ format ty)

instance : ToFormat $ LetValue φ := ⟨fmtValue⟩
instance : ToFormat Param := ⟨fmtParam⟩
mutual

partial def fmtFunDecl (isJp : Bool) : FunDecl φ -> Format -> Format
  | {fvarId, binderName, params, ty, body}, k =>
    let kw : Format := if isJp then .text "join" else .text "let"
    let pf := if params.isEmpty then .nil else
      let pf :=  nest 1 $ paren $ align false ++ joinSep' params comma
      " " ++ pf
    group $ kw
      <> fill (s!"{binderName}#{fvarId}" ++ pf
        ++ nestD (line ++ ":" <> format ty <> "=" <+> fmtCode body))
      ++ semi ++ k
partial def fmtAlt : Alt φ -> Format
  | .ctor t params k =>
    let pf := if params.isEmpty then .nil else bracket "⟦" (joinSep' params comma) "⟧"
    group $ t ++ pf <> "=>" ++ indentD (fmtCode k)
  | .const c k =>
    group $ format c <> "=>" ++ indentD (fmtCode k)
  | .default k =>
    group $ "_" <> "=>" ++ indentD (fmtCode k)

partial def fmtCode : Code φ -> Format
  | .«let» d k => fmtLetDecl d (fmtCode k)
  | .«fun» d k _ => fmtFunDecl false d (fmtCode k)
  | .jp d k => fmtFunDecl true d (fmtCode k)
  | .jmp jp as =>
    let f := s!"jump #{jp}"
    let as := group $ paren $ nest f.length $ joinSep' as comma
    f ++ as
  | .cases discr _ alts =>
    have : ToFormat $ Alt φ := ⟨fmtAlt⟩
    group $ "case" <> s!"#{discr}" <> "of" ++ indentD (joinSep' alts semi)
  | .ret v => "ret" <> format v
  | .unreach ty => paren $ "⊥" <> colon ++ format ty

end

instance : ToFormat $ Alt φ := ⟨fmtAlt⟩
instance : ToFormat $ Code φ := ⟨fmtCode⟩

instance : ToFormat $ Decl φ where
  format
  | {fvarId, name, params, ty, body, arity, recursive} =>
    let pf := if params.isEmpty then .nil else
      let pf := nest 1 $ paren $ align false ++ joinSep' params comma
      " " ++ pf
    group $ "let" ++ (if recursive then .text " rec " else .text " ")
      ++ fill (s!"{name}#{fvarId}/{arity}" ++ pf
        ++ nestD (line ++ ":" <> format ty <> "=" <+> fmtCode body))

instance : ToFormat $ Module φ where
  format
  | {decls, main} => joinSep' decls (line ++ line) ++ line ++ line ++ format main

end
end PP
