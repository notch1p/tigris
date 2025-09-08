import Tigris.utils

def dummyTyDecl : TyDecl := ⟨"__dummy", #[], #[]⟩

instance : Inhabited TyDecl := ⟨dummyTyDecl⟩

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd

def MLType.toStr : MLType -> String
  | TVar a => toString a
  | TCon a => a
  | a ->' b =>
    paren (arr? a) (toStr a) ++ " → " ++ toStr b
  | a ×'' b => paren (prod? a) (toStr a) ++ " × " ++ toStr b
  | TApp s [] => s
  | TApp s (l :: ls) =>
    let hd := paren (arr? l || prod? l) $ toStr l
    ls.foldl (init := s!"{s} {hd}") fun a s =>
      a ++ " " ++ paren (arr? l || prod? l) (toStr s)
where
  paren b s := bif b then s!"({s})" else s
  arr? | MLType.TArr _ _ => true | _ => false
  prod? | MLType.TProd _ _ => true | _ => false

open Std.Format Std.ToFormat in open Logging (magenta) in
def MLType.renderFmt : MLType -> Std.Format
  | TVar a => format a
  | TCon a => magenta a
  | a ->' b => nestD $ group $ paren? (arr? a) (renderFmt a) <> "→" <+> renderFmt b
  | a ×'' b => nestD $ group $ paren? (prod? a) (renderFmt a) <> "×" <+> renderFmt b
  | TApp s ls => nestD $ group $ joinSep (text (magenta s) :: ls.map fun s => parenthesize s (renderFmt s)) line
where
  paren? b s := bif b then paren s else s
  arr? | MLType.TArr _ _ => true | _ => false
  prod? | MLType.TProd _ _ => true | _ => false
  parenthesize s := paren? (arr? s || prod? s)

instance : ToString MLType := ⟨MLType.toStr⟩
instance : Std.ToFormat MLType := ⟨MLType.renderFmt⟩

open Std.Format Std.ToFormat in @[always_inline, inline]
def Scheme.renderFmt : Scheme -> Std.Format
  | Forall _ t' => format t'

instance : ToString Scheme where
  toString
  | .Forall [] t => toString t
  | .Forall (t :: ts) t' =>
    s!"∀ {ts.foldl (· ++ " " ++ toString ·) (toString t)}. {t'}"

instance : Std.ToFormat Scheme := ⟨Scheme.renderFmt⟩
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
  | .InvalidPat s  => s!"Invalid Pattern: {s}"
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .Undefined s   => s!"Symbol\n  {s}\nis not in scope.\n" ++
                      note "use letrec or fixcomb if this is a recursive definition"
  | .WrongCardinal n => error s!"Incorrect cardinality. Expected {n}"
  | .NoMatch e v arr =>
    let arr := arr.map $ Array.map Pattern.render ∘ Prod.fst
    s!"The expression(s)\n  {repr e} \n==ₑ {v}\ncannot be matched against any of the patterns: {toString arr}."
  | .Duplicates (mkTV a) b =>
    "Unbounded fixpoint constructor does not exist in a strongly normalized system.\n" ++
    note s!"unifying {a} and {b} results in μ{a}. {b}, which isn't allowed.\n" ++
    note "recursion is supported primitively via letrec or unsafely via fixpoint combinator `rec`"

@[inline] abbrev tInt := TCon "Int"
@[inline] abbrev tBool := TCon "Bool"
@[inline] abbrev tString := TCon "String"
@[inline] abbrev tEmpty := TCon "Empty"
@[inline] abbrev tUnit := TCon "Unit"
end MLType

abbrev TyMap := Std.HashMap String TyDecl
abbrev SchemeMap := Std.TreeMap String Scheme

structure Env where
  E : SchemeMap
  tyDecl : TyMap
deriving Repr

instance : EmptyCollection Env := ⟨∅, ∅⟩
abbrev Logger := String -- This is NOT how one should do logging.
                        -- but Lean doesn't really have a WriterT or MonadWriter
                        -- Lake has something similar, but that's in the build system.
abbrev Infer σ := StateRefT (Nat × Logger) $ EST MLType.TypingError σ
abbrev Subst := Std.TreeMap TV MLType


class Rewritable (α : Type) where
  apply : Subst -> α -> α
  fv    : α -> Std.HashSet TV

namespace Rewritable open MLType

def diff [BEq α] [Hashable α] (s₁ s₂ : Std.HashSet α) :=
  s₂.fold (fun a s => if s ∈ s₁ then s₁.erase s else a) s₁
instance [BEq α] [Hashable α] : SDiff (Std.HashSet α) := ⟨diff⟩

def applyT : Subst -> MLType -> MLType
  | _, s@(TCon _) => s
  | s, t@(TVar a) => s.getD a t
  | s, t₁ ×'' t₂ => applyT s t₁ ×'' applyT s t₂
  | s, t₁ ->' t₂ => applyT s t₁ ->' applyT s t₂
  | s, TApp h as => TApp h (as.map (applyT s))

def fvT : MLType -> Std.HashSet TV
  | TCon _ => ∅ | TVar a => {a}
  | t₁ ->' t₂ | t₁ ×'' t₂ => fvT t₁ ∪ fvT t₂
  | TApp _ as => as.foldl (init := ∅) fun a t => a ∪ fvT t

instance : Rewritable MLType := ⟨applyT, fvT⟩
instance : Rewritable Scheme where
  apply s | .Forall as t =>
            .Forall as $ apply (s.eraseMany as) t
  fv      | .Forall as t => fv t \ Std.HashSet.ofList as
instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr ((· ∪ ·) ∘ fv) ∅
instance : Rewritable Env where
  apply s e := {e with E := e.E.map fun _ v => apply s v}
  fv      e := fv e.E.values
end Rewritable
