import Tigris.utils

inductive TV where
  | mkTV : String -> TV deriving Repr, BEq, Ord, Hashable
instance : ToString TV := ⟨fun | .mkTV s => s⟩
def TV.render | mkTV s => Logging.cyan s

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

def dummyTyDecl : TyDecl := ⟨"__dummy", #[], #[]⟩

instance : Inhabited TyDecl := ⟨dummyTyDecl⟩

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd

def MLType.toStr : MLType -> String
  | TVar a => toString a
  | TCon a => a
  | a ->' b =>
    paren (arr? a) (toStr a) ++ " -> " ++ toStr b
  | a ×'' b => paren (prod? a) (toStr a) ++ " × " ++ toStr b
  | TApp s [] => s
  | TApp s (l :: ls) =>
    let hd := if l matches TArr .. then s!"({toStr l})" else toStr l
    ls.foldl (init := s!"{s} {hd}") fun a s =>
      if s matches TArr .. then s!"{a} ({s.toStr})"
      else s!"{a} {s.toStr}"
where
  paren b s := bif b then s!"({s})" else s
  arr? | MLType.TArr _ _ => true | _ => false
  prod? | MLType.TProd _ _ => true | _ => false

open MLType.toStr in
def MLType.render : MLType -> String
  | TVar a => a.render
  | TCon a => Logging.magenta a
  | a ->' b =>
    paren (arr? a) (render a) ++ " → " ++ render b
  | a ×'' b => paren (prod? a) (render a) ++ " × " ++ render b
  | TApp s [] => Logging.magenta s
  | TApp s (l :: ls) =>
    let hd := if l matches TArr .. then s!"({render l})" else render l
    ls.foldl (init := s!"{Logging.magenta s} {hd}") fun a s =>
      if s matches TArr .. then s!"{a} ({s.render})"
      else s!"{a} {s.render}"

instance : ToString MLType := ⟨MLType.toStr⟩

inductive Scheme where
  | Forall : List TV -> MLType -> Scheme deriving Repr, BEq, Ord
def Scheme.render : Scheme -> String
  | Forall [] t => t.render
  | Forall (t :: ts) t' =>
    s!"∀ {ts.foldl (· ++ " " ++ ·.render) t.render}. {t'.render}"

instance : ToString Scheme where
  toString
  | .Forall [] t => toString t
  | .Forall (t :: ts) t' =>
    s!"∀ {ts.foldl (· ++ " " ++ toString ·) (toString t)}. {t'}"

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
  | NoMatch (e : Array Expr) (v : String) (arr : Array $ Array Pattern × Expr)
  | InvalidPat (msg : String)
  | Duplicates (t : TV) (T : MLType) deriving Repr
open Logging
instance : ToString TypingError where
  toString
  | .InvalidPat s  => error s!"Invalid Pattern: {s}"
  | .NoUnify t₁ t₂ => error s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .Undefined s   => error s!"Symbol\n  {s}\nis not in scope.\n" ++
                      note "use letrec or fixcomb if this is a recursive definition"
  | .WrongCardinal n => error s!"Incorrect cardinality. Expected {n}"
  | .NoMatch e v arr =>
    error s!"The expression(s)\n  {repr e} \n==ₑ {v}\ncannot be matched against any of the patterns: {toString $ arr.map (·.1)}."
  | .Duplicates (mkTV a) b =>
    error "Unbounded fixpoint constructor does not exist in a strongly normalized system.\n" ++
    note s!"unifying {a} and {b} results in μ{a}. {b}, which isn't allowed.\n" ++
    note "recursion is supported primitively via letrec or unsafely via fixpoint combinator `rec`"

end MLType

structure Env where
  E : Std.HashMap String Scheme
  tyDecl : Std.HashMap String TyDecl
deriving Repr

instance : EmptyCollection Env := ⟨∅, ∅⟩
abbrev Logger := String -- This is NOT how one should do logging.
                        -- but Lean doesn't really have a WriterT or MonadWriter
                        -- Lake has something similar, but that's in the build system.
abbrev Infer σ := StateRefT (Nat × Logger) $ EST MLType.TypingError σ
abbrev Subst := Std.HashMap TV MLType
