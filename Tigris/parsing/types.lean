import Parser

axiom prod_sizeOf_lt [SizeOf α] [SizeOf β] (p : α × β) : sizeOf p.1 < sizeOf p ∧ sizeOf p.2 < sizeOf p

abbrev Symbol := String

inductive TConst where
  | PUnit
  | PInt (i : Int)
  | PBool (b : Bool)
  | PStr (s : String)
deriving Inhabited, Repr, BEq

instance : ToString TConst where
  toString
  | .PUnit => toString ()
  | .PInt i => toString i
  | .PBool b => toString b
  | .PStr s => reprStr s

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

def Pattern.toStr
  | PVar x => toString x
  | PWild  => "_"
  | PConst p => toString p
  | PProd' p₁ p₂ => toString (toStr p₁, toStr p₂)
  | PCtor n args => args.foldl (fun a s => a ++ " " ++ toStr s) n

instance : ToString Pattern := ⟨Pattern.toStr⟩

inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (a : Symbol) (e₁ e₂ : Expr)
  | Fix (e : Expr)     | Fixcomb (e : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
  | Match (aginst : Array Expr) (discr : Array (Array Pattern × Expr))
deriving Repr, Nonempty

--def Expr.toStr
--  | CI i | CS i | CB i => toString i | CUnit => toString ()
--  | App e₁ e₂ => 
--    s!"(App ({toStr e₁}) ({toStr e₂})"
--  | Let a e₁ e₂ => s!"(Let ({a}) ({toStr e₁}) ({toStr e₂}))"
--  | Cond e₁ e₂ e₃ => s!"(Ite ({toStr e₁}) ({toStr e₂}) ({toStr e₃})"
--  | Fix e => s!"(Fixpoint ({toStr e}))"
--  | Fixcomb e => s!"(Fixcomb ({toStr e}))"
--  | Var s => s!"(Var {s})" | Fun a e => s!"(Fun ({a}) ({toStr e}))"
--  | Prod' e₁ e₂ => toString (toStr e₁, toStr e₂)
--  | Match e d =>
--    have h : ∀ b ∈ d, sizeOf b < sizeOf d := λ _ a => Array.sizeOf_lt_of_mem a
--    let ls : String := d.attach.foldl (init := s!"({toStr e})") fun a s =>
--      let e' := Subtype.val s
--      let p := Subtype.property s
--      have : sizeOf (Prod.snd $ Subtype.val s) < 1 + sizeOf e + sizeOf d := by
--        have h₁ := Nat.lt_trans (prod_sizeOf_lt (Subtype.val s)).2 $ h (Subtype.val s) p
--        omega
--      s!"({a},{toString (Prod.fst e')},{toStr (Prod.snd e')})"
--    s!"Match {ls}"

instance : Inhabited Expr := ⟨Expr.CUnit⟩
-- instance : ToString Expr := ⟨Expr.toStr⟩

inductive Associativity | leftAssoc | rightAssoc deriving Ord, Repr, Inhabited

instance : ToString Associativity where
  toString
  | .leftAssoc => "left"
  | .rightAssoc => "right"
abbrev Binding := Symbol × Expr

structure OpEntry where
  prec : Nat
  assoc : Associativity
  impl : Expr -> Expr -> Expr

instance : ToString OpEntry := ⟨fun {prec, assoc,..} => toString (prec, assoc)⟩

abbrev OpTable := Std.HashMap String OpEntry
abbrev TyArity := Std.HashMap String Nat

structure PEnv where
  ops : OpTable
  tys : TyArity

/--(ℕ × String) ↦ ε × Associativity-/
abbrev TParser := SimpleParserT Substring Char $ StateM $ PEnv

