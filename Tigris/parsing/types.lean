import Parser
import PP.dependentPP

theorem prod_sizeOf_lt_fst [SizeOf α] [SizeOf β] (a : α) (b : β)
  : sizeOf a < sizeOf (a, b) := Prod.mk.sizeOf_spec a b ▸ by omega
theorem prod_sizeOf_lt_snd [SizeOf α] [SizeOf β] (a : α) (b : β)
  : sizeOf b < sizeOf (a, b) := Prod.mk.sizeOf_spec a b ▸ by omega
attribute [simp, grind <-] prod_sizeOf_lt_fst prod_sizeOf_lt_snd

@[inline, reducible] def Function.on (g : β -> β -> γ) (f : α -> β)
  : α -> α -> γ := fun x y => g (f x) (f y)
@[inline, reducible] def Function.on'
  (g : β -> γ -> τ) (f : α -> β) (f' : δ -> γ)
  : α -> δ -> τ := fun x y => g (f x) (f' y)
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

open Std.ToFormat in
instance : Std.ToFormat TConst where
  format
  | .PUnit => format ()
  | .PInt i => format i
  | .PBool b => format b
  | .PStr s => repr s

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
with @[computed_field]
  vars : Pattern -> Array String
  | .PVar x       => #[x]
  | .PWild        => #[]
  | .PConst _     => #[]
  | .PProd' p q   => vars p ++ vars q
  | .PCtor _ args => args.flatMap vars
deriving Inhabited, Repr

def Pattern.beq : Pattern -> Pattern -> Bool
  | PCtor c₁ _, PCtor c₂ _ => c₁ == c₂
  | PConst p₁, PConst p₂ => p₁ == p₂
  | PProd' p₁ p₂, PProd' p₁' p₂' => p₁.beq p₁' && p₂.beq p₂'
  | _, PWild => true
  | _, PVar .. => true
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


/-- Kind is a lattice.
- `type` denotes the single base sort `Type 0`
- `karr` denotes `(· -> ·)` for universe
- `kvar` denotes metavariables
-/
inductive Kind where
  | type
  | karr : Kind -> Kind -> Kind
  | kvar : Nat -> Kind
with
  @[computed_field] arity : Kind -> Nat
    | .karr _ b => 1 + arity b
    | _         => 0
  @[computed_field] isArr : Kind -> Bool
    | .karr .. => true | _ => false
deriving Repr, BEq, Ord, Inhabited, Hashable

instance : OfNat Kind n where
  ofNat := n.fold (fun _ _ => Kind.karr .type) .type

def Kind.toStr : Kind -> String
  | .type        => "Type"
  | .karr a b    =>
    (if a.isArr then s!"({a.toStr})" else a.toStr) ++ " → " ++ b.toStr
  | .kvar n      => s!"?k.{n}"
instance : ToString Kind := ⟨Kind.toStr⟩

@[inline] def kindOfParams (ps : Array (TV × Kind)) : Kind :=
  ps.foldr (Kind.karr ∘ Prod.snd) .type

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

/--
Proper type variables. previously we used string equality and pattern matching
the prefixes to distinguish tv and its kind (metavariables/skolems/instance-renamed).
Which is sloppy and rough.

a unique Nat per kind to prevent collide.
-/
inductive TV where
  | mv    : Nat -> (userNamed? : Option String := none) -> TV  -- metavariables
  | sk    : Nat -> TV                                  -- skolems
  | inst  : Nat -> Nat -> TV                           -- used by resolution/quantifier index
  | named : String -> TV                               -- user-supplied tvs from parser

def TV.hashTV : TV -> UInt64
  | TV.mv v _ => mixHash 0 (hash v)
  | TV.sk v => mixHash 1 (hash v)
  | TV.inst v v' => mixHash (mixHash 2 (hash v)) (hash v')
  | TV.named a => mixHash 3 (hash a)
def TV.ord : TV -> TV -> Ordering
  | mv a _, mv b _ => compare a b |>.then Ordering.eq
  | mv .., _ => Ordering.lt
  | _, mv .. => Ordering.gt
  | sk a, sk b => (compare a b).then Ordering.eq
  | sk _, _ => Ordering.lt
  | _, sk _ => Ordering.gt
  | inst v₁ v₂, inst v₁' v₂' => compare v₁ v₁' |>.then
                              $ compare v₂ v₂' |>.then Ordering.eq
  | inst .., _ => Ordering.lt
  | _, inst .. => Ordering.gt
  | named a, named b => compare a b |>.then Ordering.eq
def TV.beq : TV -> TV -> Bool
  | .mv v _, .mv v' _ | .sk v, .sk v' => v == v'
  | .inst v₁ v₂, .inst v₁' v₂' => v₁ == v₁' && v₂ == v₂'
  | .named s, .named s' => s == s'
  | _, _ => false

instance : BEq TV := ⟨TV.beq⟩
instance : Hashable TV := ⟨TV.hashTV⟩
instance : Ord TV := ⟨TV.ord⟩
instance : ReflBEq TV where rfl {tv} := by cases tv <;> simp [BEq.beq, TV.beq]
def TV.toStr : TV -> String
  | .mv n _    => s!"?m.{n}"
  | .sk n      => s!"?sk.{n}"
  | .inst n i  => s!"?inst.{n}.{i}"
  | .named s   => s

def TV.elimStr := TV.toStr
instance : ToString TV := ⟨TV.toStr⟩
instance : Repr TV := ⟨fun t _ => t.toStr⟩
def TV.renderFmt : TV -> Std.Format
  | tv => tv.toStr
instance : Std.ToFormat TV := ⟨TV.renderFmt⟩

def TV.tv? : TV -> Bool
  | .mv .. => true
  | _ => false

/-- every named TV must be freshened before any code that needs this runs -/
def TV.id : TV -> Nat
  | .mv n _ | .sk n | .inst n _ => n
  | .named _ => unreachable!

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

inductive Scheme where
  | Forall : List TV -> List Pred -> MLType -> Scheme

structure Pred where
  cls  : String
  args : List MLType := []
end
deriving instance Repr, BEq, Ord for Scheme
deriving instance Repr, BEq, Ord, Inhabited, Hashable for MLType
deriving instance BEq, Inhabited, Repr, Ord, Hashable for Pred

def MLType.getRightmost : MLType -> MLType
  | TArr _ t₂ => getRightmost t₂
  | t => t
def MLType.decomposeArr : MLType -> (List MLType × MLType)
  | .TSch (.Forall _ _ps t) => decomposeArr t
  | .TArr a b =>
    let (as, r) := decomposeArr b
    (a :: as, r)
  | t => ([], t)

instance : ToString Pattern := ⟨Pattern.toStr⟩

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
/-- Value is true when the entry comes from a real
declaration rather than a mutual-block forward reference.

Previously we stored tyctor's arity here and use that information to direct
tyapp parsing. Now tyapp is dumb (a/b-type just like Haskell2010report)
and arity (kind) checking is done by typechecker. -/
abbrev TyNames := Lean.Data.Trie Bool

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
  tys   : TyNames
  undTy : List Symbol -- undefined types (used in mutual rectypes definition)
  recordFields : Std.HashMap Symbol (Array Symbol) := {}
  indentStack  : List Nat := [0]
  lastEol : Nat := 0
  /-- counter for kvar  -/
  nxtK   : Nat := 0
instance : EmptyCollection PEnv := ⟨{}, {}, {}, {}, {}, {}, {}, 0, 0⟩
--abbrev TParser := SimpleParserT Substring.Raw Char $ StateRefT String $ StateT PEnv $ ST α
abbrev TParser σ := SimpleParserT String.Slice Char
                  $ StateRefT (PEnv × String) (ST σ)

def warn (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.warn s)
def error (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.error s)

structure TyDecl where
  tycon : String
  /-- binder TVs with their declared kinds, must be freshed before use -/
  param : Array (TV × Kind)
  ctors : Array $ Symbol × List (Symbol × MLType) × Nat
  cls?  : Bool := false -- class?
  /--
    RHS when this is a type abbreviation. we match
    against this first when dealing with TyDecl
    so as to avoid a separate abbreviation encoding.
  -/
  rhs   : Option MLType := none
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
  params   : Array (TV × Kind) -- class param binders + their kinds
  methods  : Array MethodInfo
  -- maybe superclass?? not considered now.
deriving Repr

structure InstanceInfo where
  iname   : String
  cls     : String
  args    : List MLType
  ctx     : List Pred
deriving Repr
