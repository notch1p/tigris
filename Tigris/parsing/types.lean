import Parser
import PP.dependentPP

-- retired
--axiom prod_sizeOf_lt [SizeOf α] [SizeOf β] (p : α × β) : sizeOf p.1 < sizeOf p ∧ sizeOf p.2 < sizeOf p
--axiom prod_sizeOf_lt_fst [SizeOf α] [SizeOf β]
--  (a : α) (b : β) : sizeOf a < sizeOf (a, b)
--axiom prod_sizeOf_lt_snd [SizeOf α] [SizeOf β]
--  (a : α) (b : β) : sizeOf b < sizeOf (a, b)

theorem prod_sizeOf_lt_fst [SizeOf α] [SizeOf β] (a : α) (b : β)
  : sizeOf a < sizeOf (a, b) := Prod.mk.sizeOf_spec a b ▸ by omega
theorem prod_sizeOf_lt_snd [SizeOf α] [SizeOf β] (a : α) (b : β)
  : sizeOf b < sizeOf (a, b) := Prod.mk.sizeOf_spec a b ▸ by omega
attribute [simp, grind] prod_sizeOf_lt_fst prod_sizeOf_lt_snd

@[inline, reducible] def Function.on (g : β -> β -> γ) (f : α -> β)
  : α -> α -> γ := fun x y => g (f x) (f y)

abbrev Symbol := String

namespace Logging open PrettyPrint Text
def blue s := (show SString from ⟨s, [], .blue, .defaultColor⟩).render
def cyan s := (show SString from ⟨s, [], .green, .defaultColor⟩).render
def magenta s := (show SString from ⟨s, [], .magenta, .defaultColor⟩).render
def note s := "[NOTE] " ++ s
def info s := "[INFO] " ++ s
def warn s := "[WARN] " ++ s
def error s := "[ERROR] " ++ s
end Logging

inductive TConst where
  | PUnit
  | PInt (i : Int)
  | PBool (b : Bool)
  | PStr (s : String)
deriving Inhabited, Repr, BEq, Hashable

instance : ToString TConst where
  toString
  | .PUnit => toString ()
  | .PInt i => toString i
  | .PBool b => toString b
  | .PStr s => reprStr s

def TConst.render
  | PUnit => Logging.cyan $ toString ()
  | PInt i | PBool i => Logging.cyan $ toString i
  | PStr s => Logging.cyan $ reprStr s

inductive Pattern where
  | PVar (x : Symbol)
  | PWild
  | PConst (p : TConst)
  | PProd' (p₁ : Pattern) (p₂ : Pattern)
  | PCtor (name : String) (args : Array Pattern)
deriving Inhabited, Repr

def Pattern.beq : Pattern -> Pattern -> Bool
  | PCtor c₁ _, PCtor c₂ _ => c₁ == c₂
  | PConst p₁, PConst p₂ => p₁ == p₂
  | PProd' p₁ p₂, PProd' p₁' p₂' => p₁.beq p₁' && p₂.beq p₂'
  | _, PWild => true
  | _, PVar _ => true
  | _, _ => false

instance : BEq Pattern := ⟨Pattern.beq⟩

def Pattern.toStr : Pattern -> String
  | PVar x => toString x
  | PWild  => "_"
  | PConst p => toString p
  | PProd' p₁ p₂ => toString (toStr p₁, toStr p₂)
  | PCtor n args => args.foldl (fun a s => a ++ " " ++ paren (prodOrApp? s) (toStr s)) n where
  paren b s := bif b then s!"({s})" else s
  prodOrApp? | PProd' .. => true
             | PCtor _ args => if args.isEmpty then false else true
             | _ => false
open Pattern.toStr in
def Pattern.render : Pattern -> String
  | PVar x => toString x
  | PWild => "_"
  | PConst p => p.render
  | PProd' p₁ p₂ => toString (render p₁, render p₂)
  | PCtor n args => args.foldl (fun a s => a ++ " " ++ paren (prodOrApp? s) (render s)) $ Logging.blue n

instance : ToString Pattern := ⟨Pattern.toStr⟩
/-- Kind is a lattice.
- `type` denotes the single base sort `Type 0`
- `karr` denotes `(· -> ·)` for universe
- `kvar` denotes metavariables
-/
inductive Kind where
  | type
  | karr : Kind -> Kind -> Kind
  | kvar : Nat -> Kind
deriving Repr, BEq, Ord, Inhabited, Hashable

instance : OfNat Kind n where
  ofNat := n.fold (fun _ _ => Kind.karr .type) .type

@[inline] def Kind.isArr : Kind -> Bool
  | .karr .. => true | _ => false
def Kind.toStr : Kind -> String
  | .type        => "Type"
  | .karr a b    =>
    (if a.isArr then s!"({a.toStr})" else a.toStr) ++ " → " ++ b.toStr
  | .kvar n      => s!"?k.{n}"
instance : ToString Kind := ⟨Kind.toStr⟩

/-- Arity = number of left-spine arrows. `Kind.arity Type = 0`,
    `Kind.arity (Type → Type) = 1`, `Kind.arity (Type → Type → Type) = 2`. -/
@[inline] def Kind.arity : Kind -> Nat
  | .karr _ b => 1 + arity b
  | _         => 0

/-- Kind substitution. -/
abbrev KSubst := Std.TreeMap Nat Kind

def Kind.apply (s : KSubst) : Kind -> Kind
  | .type     => .type
  | .karr a b => .karr (apply s a) (apply s b)
  | .kvar n   => s.getD n (.kvar n)

def Kind.fv : Kind -> Std.TreeSet Nat
  | .type     => ∅
  | .karr a b => fv a ∪ fv b
  | .kvar n   => {n}

@[inline] def KSubst.compose (s₂ s₁ : KSubst) : KSubst :=
  if s₁.isEmpty then s₂ else
    s₁.foldl (init := s₂) fun acc k v => acc.insert k (Kind.apply s₂ v)

infixl: 65 " ∪ₖ " => KSubst.compose

/-- Bind kind metavar `n := k` with an occurs check. -/
private def bindKV (n : Nat) (k : Kind) : Except String KSubst :=
  if k == .kvar n then pure ∅
  else if n ∈ Kind.fv k then throw s!"infinite kind: ?k.{n} occurs in {k}"
  else pure (Std.TreeMap.empty.insert n k)

/-- First-order unification on kinds; identical in structure to MLType
unification but on the kind lattice. -/
partial def Kind.unify : Kind -> Kind -> Except String KSubst
  | .type, .type => pure ∅
  | .karr a₁ b₁, .karr a₂ b₂ => do
    let s₁ <- unify a₁ a₂
    let s₂ <- unify (apply s₁ b₁) (apply s₁ b₂)
    return s₂ ∪ₖ s₁
  | .kvar n, k | k, .kvar n => bindKV n k
  | k₁, k₂ => throw s!"cannot unify kinds {k₁} with {k₂}"

inductive TV where
  | mkTV : String -> TV deriving Repr, Ord, Hashable

def TV.elimStr | (mkTV s) => s
instance : BEq TV := ⟨fun (.mkTV s) (.mkTV s') => s == s'⟩
instance : ToString TV := ⟨fun (.mkTV s) => s⟩
instance : ReflBEq TV := ⟨by simp[(· == ·)]⟩
def TV.renderFmt : TV -> Std.Format
  | mkTV s => Logging.cyan s
def TV.toStr : TV -> String | mkTV s => s
instance : Std.ToFormat TV := ⟨TV.renderFmt⟩

mutual
inductive MLType where
  | TVar  : TV -> MLType
  | TCon  : String -> MLType
  | TArr  : MLType -> MLType -> MLType
  | TProd : MLType -> MLType -> MLType
  | TApp  : MLType -> List MLType -> MLType
  | TyLam : TV -> MLType -> MLType
  /-- essentially a `TForall`. but more convenient -/
  | TSch  : Scheme -> MLType -- only allow rank-1 for now.
deriving Repr, BEq, Ord, Inhabited, Hashable

structure Pred where
  cls  : String
  args : List MLType := []
deriving BEq, Inhabited, Repr, Ord, Hashable

inductive Scheme where
  | Forall : List TV -> List Pred -> MLType -> Scheme deriving Repr, BEq, Ord
end

def MLType.getRightmost : MLType -> MLType
  | TArr _ t₂ => getRightmost t₂
  | t => t

def MLType.decomposeArr : MLType -> (List MLType × MLType)
  | .TArr a b =>
    let (as, r) := decomposeArr b
    (a :: as, r)
  | t => ([], t)
def MLType.decomposeArr' : MLType -> (List MLType × MLType)
  | .TSch (.Forall _ _ps t) =>
    /-let (as, r) := -/ decomposeArr' t
    --(ps.map (fun {cls, args} => TApp cls args) ++ as, r)
  | .TArr a b =>
    let (as, r) := decomposeArr' b
    (a :: as, r)
  | t => ([], t)
inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (ae : Array $ Symbol × Expr) (e₂ : Expr)
  | Fix (e : Expr)     | Fixcomb (e : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
  | Match (aginst : Array Expr) (discr : Array (Array Pattern × Expr))
  | Ascribe (e : Expr) (ty : MLType)
deriving Repr, Nonempty

inductive TExpr where
  | CI     (i : Int)                                    (ty : MLType)
  | CS     (s : String)                                 (ty : MLType)
  | CB     (b : Bool)                                   (ty : MLType)
  | CUnit                                               (ty : MLType)
  | Var    (x : Symbol)                                 (ty : MLType)
  | Fun    (param : Symbol) (paramTy : MLType)
           (body : TExpr) (ty : MLType)
  | Fixcomb (e : TExpr)                                 (ty : MLType)
  | Fix    (e : TExpr)                                  (ty : MLType)
  | App    (f : TExpr) (a : TExpr)                      (ty : MLType)
  | Let    (binds : Array (Symbol × Scheme × TExpr))
           (body : TExpr) (ty : MLType)
  | Cond   (c : TExpr) (t : TExpr) (e : TExpr)          (ty : MLType)
  | Prod'  (l : TExpr) (r : TExpr)                      (ty : MLType)
  | Match  (scrutinees : Array TExpr)
           (branches   : Array (Array Pattern × TExpr))
           (resTy      : MLType)
           (counterexample : Option (List Pattern))
           (redundantRows  : Array Nat)
  | Ascribe (e : TExpr)                                 (ty : MLType)
deriving Inhabited, Repr


instance : Inhabited Expr := ⟨Expr.CUnit⟩
-- instance : ToString Expr := ⟨Expr.toStr⟩

inductive Associativity | leftAssoc | rightAssoc deriving Ord, Repr, Inhabited

instance : ToString Associativity where
  toString
  | .leftAssoc => "left"
  | .rightAssoc => "right"
abbrev Binding := Symbol × Expr
abbrev BindingT := Symbol × Scheme × TExpr
abbrev PBinding := Pattern × Expr

structure BinaryEntry where
  sym   : Symbol
  prec  : Nat
  assoc : Associativity
  impl  : Expr -> Expr -> Expr

structure UnaryEntry where
  sym : Symbol
  prec : Nat
  impl : Expr -> Expr

abbrev BinaryTable := Lean.Data.Trie BinaryEntry
abbrev PrefixTable := Lean.Data.Trie UnaryEntry
abbrev PostfixTable := Lean.Data.Trie UnaryEntry
/-- `Bool` indicates forward referencing. -/
abbrev TyArity := Lean.Data.Trie (Kind × Bool)

open Lean.Data.Trie in
def Lean.Data.Trie.ofList (arr : List (String × α)) : Trie α :=
  arr.foldl (fun a s => insert a s.1 s.2) ∅
in
def Lean.Data.Trie.findD (t : Trie α) (s : String) (dflt : α) : α := t.find? s |>.getD dflt
in
attribute [inline] ofList findD

abbrev tabWidth : Nat := 2
structure PEnv where
  ops   : BinaryTable
  pre   : PrefixTable := ∅
  post  : PostfixTable := ∅
  tys   : TyArity
  undTy : List Symbol -- undefined types (used in mutual rectypes definition)
  recordFields : Std.HashMap Symbol (Array Symbol) := {}
  indentStack  : List Nat := [0]
  lastEol : Nat := 0

--abbrev TParser := SimpleParserT Substring.Raw Char $ StateRefT String $ StateT PEnv $ ST α
abbrev TParser σ := SimpleParserT Substring.Raw Char
                  $ StateRefT (PEnv × String) (ST σ)

def warn (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.warn s)
def error (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.error s)

structure TyDecl where
  tycon : String
  param : Array (String × Kind)
  ctors : Array $ Symbol × List (Symbol × MLType) × Nat
  cls?  : Bool := false -- class?
deriving Repr

structure InstanceDecl where
  ctxPreds : List Pred
  cname    : String
  args     : List MLType
  methods  : Array (String × Expr)
deriving Repr
inductive TopDecl
  | idBind   : Array Binding -> TopDecl
  | patBind  : PBinding -> TopDecl
  | tyBind   : TyDecl -> TopDecl
  | extBind  : Symbol -> String -> Scheme -> TopDecl
  | instBind : InstanceDecl -> TopDecl
deriving Repr

inductive TopDeclT
  | idBind : Array BindingT -> TopDeclT
  | patBind : Pattern × Scheme × TExpr -> TopDeclT
  | tyBind : TyDecl -> TopDeclT
deriving Repr

def TExpr.getTy : TExpr -> MLType
  | .CI _ ty | .CS _ ty | .CB _ ty | .CUnit ty
  | .Var _ ty
  | .Fixcomb _ ty | .Fix _ ty
  | .App _ _ ty
  | .Cond _ _ _ ty | .Prod' _ _ ty
  | .Match _ _ ty .. | .Ascribe _ ty | .Let _ _ ty
  | .Fun _ _ _ ty => ty

structure MethodInfo where
  mname : Symbol
  mty   : MLType
  idx   : Nat
deriving Repr

/--
Assumptions:
  - class decl is desugared into a type decl
  - with same name, same ctor name.
-/
structure ClassInfo where
  cname    : Symbol -- cname == ctorName, assumed
  ctorName : Symbol
  params   : Array (String × Kind) -- class param names + their kinds
  methods  : Array MethodInfo
  -- maybe superclass?? not considered now.
deriving Repr

structure InstanceInfo where
  iname   : String
  cls     : String
  args    : List MLType
  ctx     : List Pred
deriving Repr
