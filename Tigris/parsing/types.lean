import Parser

abbrev Symbol := String

inductive Pattern where
  | PVar (x : Symbol)
  | PWild
  | PCtor (name : String) (args : Array Pattern)
  deriving Repr, BEq, Inhabited

inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (a : Symbol) (e₁ e₂ : Expr)
  | Fix (e : Expr)     | Fixcomb (e : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
  | Match (aginst : Expr) (discr : Array (Pattern × Expr))

deriving Repr, BEq, Nonempty
instance : Inhabited Expr := ⟨Expr.CUnit⟩

abbrev Binding := Symbol × Expr

inductive Associativity | leftAssoc | rightAssoc deriving Ord, Repr

instance : ToString Associativity where
  toString
  | .leftAssoc => "left"
  | .rightAssoc => "right"

abbrev OpIndex := Nat × String
instance opIndexOrd : Ord OpIndex where
  compare 
  | (n, a), (n', a') => 
    let n := compare n' n; let a := compare a a'
    if a matches .eq then .eq else n.then a

/--(ℕ × String) ↦ ε × Associativity-/
abbrev OpTable α := Std.TreeMap OpIndex ((α -> α -> α) × Associativity) opIndexOrd.compare
abbrev TParser := SimpleParserT Substring Char $ StateM $ OpTable Expr

