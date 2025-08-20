import Parser
import PP.dependentPP

axiom prod_sizeOf_lt [SizeOf α] [SizeOf β] (p : α × β) : sizeOf p.1 < sizeOf p ∧ sizeOf p.2 < sizeOf p

abbrev Symbol := String

namespace Logging open PrettyPrint Text
def blue s := (show SString from ⟨s, [], .blue, .defaultColor⟩).render
def cyan s := (show SString from ⟨s, [], .green, .defaultColor⟩).render
def magenta s := (show SString from ⟨s, [], .magenta, .defaultColor⟩).render
def note s := (show SString from ⟨"[NOTE] ", [.bold], .cyan, .defaultColor⟩).render ++ s
def info s := (show SString from ⟨"[INFO] ", [.bold], .blue, .defaultColor⟩).render ++ s
def warn s := (show SString from ⟨"[WARN] ", [.bold], .yellow, .defaultColor⟩).render ++ s
def error s := (show SString from ⟨"[ERROR] ", [.bold], .red, .defaultColor⟩).render ++ s
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
  | PCtor n args => args.foldl (fun a s => a ++ " " ++ paren (prod? s) (toStr s)) n where
  paren b s := bif b then s!"({s})" else s
  prod? | PProd' .. => true | _ => false
open Pattern.toStr in
def Pattern.render : Pattern -> String
  | PVar x => toString x
  | PWild => "_"
  | PConst p => p.render
  | PProd' p₁ p₂ => toString (render p₁, render p₂)
  | PCtor n args => args.foldl (fun a s => a ++ " " ++ paren (prod? s) (render s)) $ Logging.blue n


instance : ToString Pattern := ⟨Pattern.toStr⟩

inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (a : Symbol) (e₁ e₂ : Expr)
  | Fix (e : Expr)     | Fixcomb (e : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
  | Match (aginst : Array Expr) (discr : Array (Array Pattern × Expr))
deriving Repr, Nonempty

instance : Inhabited Expr := ⟨Expr.CUnit⟩
-- instance : ToString Expr := ⟨Expr.toStr⟩

inductive Associativity | leftAssoc | rightAssoc deriving Ord, Repr, Inhabited

instance : ToString Associativity where
  toString
  | .leftAssoc => "left"
  | .rightAssoc => "right"
abbrev Binding := Symbol × Expr

structure OpEntry where
  sym : Symbol
  prec : Nat
  assoc : Associativity
  impl : Expr -> Expr -> Expr

instance : ToString OpEntry := ⟨fun {prec, assoc,..} => toString (prec, assoc)⟩
instance : Repr OpEntry := ⟨fun {prec, assoc,..} _ => toString (prec, assoc)⟩

abbrev OpTable := Lean.Data.Trie OpEntry
abbrev TyArity := Lean.Data.Trie Nat

open Lean.Data.Trie in
def Lean.Data.Trie.ofList (arr : List (String × α)) : Trie α :=
  arr.foldl (fun a s => insert a s.1 s.2) ∅
in
def Lean.Data.Trie.findD (t : Trie α) (s : String) (dflt : α) : α := t.find? s |>.getD dflt
in
attribute [inline] ofList findD

structure PEnv where
  ops : OpTable
  tys : TyArity
  undTy : List Symbol

--abbrev TParser := SimpleParserT Substring Char $ StateRefT String $ StateT PEnv $ ST α
abbrev TParser σ := SimpleParserT Substring Char
                  $ StateRefT (PEnv × String) (ST σ)
