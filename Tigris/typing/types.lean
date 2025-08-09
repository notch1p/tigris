import Tigris.utils

inductive TV where
  | mkTV : String -> TV deriving Repr, BEq, Ord, Hashable
instance : ToString TV := ⟨fun | .mkTV s => s⟩

inductive MLType where
  | TVar : TV -> MLType
  | TCon : String -> MLType
  | TArr : MLType -> MLType -> MLType
  | TProd : MLType -> MLType -> MLType
  | TApp : String -> List MLType -> MLType
deriving Repr, BEq, Ord, Inhabited

structure TyDecl where
  tycon : String
  param : Array String
  ctors : Array $ Symbol × List MLType
deriving Repr

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd

def MLType.toStr : MLType -> String
  | TVar a => toString a 
  | TCon a => a
  | a ->' b =>
    paren (arr? a) (toStr a) ++ " → " ++ toStr b
  | a ×'' b => paren (prod? a) (toStr a) ++ " × " ++ toStr b
  | TApp s [] => s | TApp s (l :: ls) =>
    ls.foldl (init := s!"{s} {l.toStr}") fun a s =>
      s!"{a} {s.toStr}"
where
  paren b s := bif b then s!"({s})" else s
  arr? | MLType.TArr _ _ => true | _ => false
  prod? | MLType.TProd _ _ => true | _ => false

instance : ToString MLType := ⟨MLType.toStr⟩

inductive Scheme where
  | Forall : List TV -> MLType -> Scheme deriving Repr, BEq, Ord

instance : ToString Scheme where
  toString
  | .Forall [] t => toString t
  | .Forall ts t => s!"∀ {ts.mapReduce! toString (· ++ " " ++ ·)}. {toString t}"

instance : Inhabited Scheme where
  default := .Forall [] (MLType.TCon "False")
namespace MLType open TV Expr

def ctorScheme (tycon : String) (tparams : List TV) (fields : List MLType) : Scheme :=
  .Forall tparams
  $ fields.foldr TArr
  $ TApp tycon 
  $ tparams.map (TVar ·)

inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | WrongCardinal (n : Nat)
  | NoMatch (e : Expr) (arr : Array $ Pattern × Expr)
  | Duplicates (t : TV) (T : MLType) deriving Repr

instance : ToString TypingError where
  toString
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .Undefined s   => s!"Variable\n  {s}\nis not in scope.\n\
                         Note: use letrec or fixcomb if this is a recursive definition"
  | .WrongCardinal n => s!"Incorrect cardinality. Expected {n}"
  | .NoMatch e arr =>
    s!"The expression\n  {repr e}\ncannot be matched against any of the patterns: {repr $ arr.map (·.1)}\n\
       This is likely because this pattern matching is non-exhaustive (No exhaustion check is performed.)"
  | .Duplicates (mkTV a) b =>
    s!"\
    Unbounded fixpoint constructor does not exist in a strongly normalized system.\n\
    Note: unifying {a} and {b} results in μ{a}. {b}, which isn't allowed.\n\
    Note: recursion is supported primitively via letrec \n\
    Note: or unsafely via fixpoint combinator `rec`"

end MLType

abbrev Env := Std.HashMap String Scheme
abbrev Infer σ := StateRefT Nat $ EST MLType.TypingError σ
abbrev Subst := Std.HashMap TV MLType
instance : ToString Env where
  toString e := e.toList.foldl (init := "") fun a (v, t) => s!"{v} : {t} " ++ a
