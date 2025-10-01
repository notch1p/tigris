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
  | TApp s [] | KApp (.mkTV s) [] => s
  | TApp s (l :: ls) | KApp s (l :: ls) =>
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
  | TApp s ls | KApp (.mkTV s) ls => nestD $ group $ joinSep (text (magenta s) :: ls.map fun s => parenthesize s (renderFmt s)) line
where
  paren? b s := bif b then paren s else s
  arr? | MLType.TArr _ _ => true | _ => false
  prod? | MLType.TProd _ _ => true | _ => false
  parenthesize s := paren? (arr? s || prod? s)

instance : ToString MLType := ⟨MLType.toStr⟩
instance : Std.ToFormat MLType := ⟨MLType.renderFmt⟩

instance : ToString Pred where
  toString
  | {cls, args} => cls ++ args.foldl (· ++ " " ++ toString ·) ""
instance : Std.ToFormat Pred where
  format
  | {cls, args} =>
    Logging.magenta cls ++ args.foldl (· ++ " " ++ MLType.renderFmt ·) ""

open Std.Format Std.ToFormat in
def Scheme.renderFmt : Scheme -> Std.Format
  | Forall _ [] t' => format t'
  | Forall _ pred t' => format pred <> format t'
def Pred.unary (c : String) (a : MLType) : Pred := ⟨c, [a]⟩
def Pred.mapArgs (f : MLType -> MLType) : Pred -> Pred
  | {cls, args} => {cls, args := args.map f}
def Scheme.body : Scheme -> MLType
  | .Forall _ _ t => t
def Scheme.ctx : Scheme -> List Pred
  | .Forall _ ps _ => ps

attribute [inline] Scheme.renderFmt Pred.unary Scheme.body Scheme.ctx

instance : ToString Scheme where
  toString
  | .Forall [] [] t => toString t
  | .Forall [] pred t => toString pred ++ " " ++ toString t
  | .Forall (t :: ts) pred t' =>
    s!"∀ {ts.foldl (· ++ " " ++ toString ·) (toString t)}, {toString pred}. {t'}"

instance : Std.ToFormat Scheme := ⟨Scheme.renderFmt⟩
instance : Inhabited Scheme where
  default := .Forall [] [] (MLType.TCon "False")
namespace MLType open TV Expr

def ctorScheme (tycon : String) (tparams : List TV) (fields : List MLType) : Scheme :=
  .Forall tparams []
  $ fields.foldr TArr
  $ TApp tycon
  $ tparams.map (TVar ·)

inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | WrongCardinal (n : Nat)
  | NoMatch (e : Array Expr) (v : String) (arr : Array $ Array Pattern × Expr)
  | InvalidPat (msg : String)
  | Interrupted
  | Ambiguous (msg : String)
  | Impossible (s : String)
  | Duplicates (t : TV) (T : MLType) deriving Repr
open Logging
instance : ToString TypingError where
  toString
  | .Ambiguous msg => s!"Ambiguous constraint set: {msg}"
  | .Impossible s => s!"Impossible: {s}"
  | .Interrupted   => s!"Interrupted."
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

@[inline, match_pattern] abbrev tInt := TCon "Int"
@[inline, match_pattern] abbrev tBool := TCon "Bool"
@[inline, match_pattern] abbrev tString := TCon "String"
@[inline, match_pattern] abbrev tEmpty := TCon "Empty"
@[inline, match_pattern] abbrev tUnit := TCon "Unit"
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

instance [BEq α] [Hashable α] : SDiff (Std.HashSet α) := ⟨fun s₁ s₂ => s₂.fold .erase s₁⟩

partial def applyT : Subst -> MLType -> MLType
  | _, s@(TCon _) => s
  | s, t@(TVar a) => s.getD a t
  | s, t₁ ×'' t₂ => applyT s t₁ ×'' applyT s t₂
  | s, t₁ ->' t₂ => applyT s t₁ ->' applyT s t₂
  | s, TApp h as => TApp h (as.map (applyT s))
  | s, KApp v as =>
    let v' := applyT s $ TVar v
    let as := as.map (applyT s)
    match v' with
    | TVar v => KApp v as
    | TApp h [] | TCon h => TApp h as
    | _ => KApp v as

def fvT : MLType -> Std.HashSet TV
  | TCon _ => ∅ | TVar a => {a}
  | t₁ ->' t₂ | t₁ ×'' t₂ => fvT t₁ ∪ fvT t₂
  | TApp _ as => as.foldl (· ∪ fvT ·) ∅
  | KApp v as => {v} ∪ as.foldl (· ∪ fvT ·) ∅
instance : Rewritable MLType := ⟨applyT, fvT⟩

def fvP : Pred -> Std.HashSet TV
  | {args,..} => args.foldl (· ∪ fvT ·) ∅
instance : Rewritable Pred := ⟨(Pred.mapArgs $ apply ·), fvP⟩

instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr ((· ∪ ·) ∘ fv) ∅

instance : Rewritable Scheme where
  apply s | .Forall as ps t =>
            let s := s.eraseMany as
            .Forall as (ps.map (apply s)) (apply s t)
  fv | .Forall as ps t => (fv ps ∪ fv t) \ Std.HashSet.ofList as
instance : Rewritable Env where
  apply s e := {e with E := e.E.map fun _ v => apply s v}
  fv      e := fv e.E.values
end Rewritable

namespace MLType open Rewritable
@[inline] def merge (s₁ s₂ : Subst) :=
  s₂.foldl (init := s₁) fun acc k v =>
    acc.insert k (apply s₁ v)
infixl : 65 " ∪' " => merge

def gensym (n : Nat) : String :=
  let (q, r) := (n / 25, n % 25)
  let s := Char.ofNat $ r + 0x03b1
  if q == 0 then s.toString
  else s.toString ++ q.toSubscriptString

def normalize : Scheme -> Scheme
  | .Forall _ ps body =>
    let rec fv
      | TVar a => [a] | TCon _ => []
      | a ->' b | a ×'' b => fv a ++ fv b
      | TApp _ as => as.flatMap fv
      | KApp v as => v :: as.flatMap fv
    let ts := (List.rmDup $ fv body ++ ps.flatMap (·.args.flatMap fv));
    let ord := ts.zip $ ts.foldrIdx (fun i _ a => .mkTV (gensym i) :: a) []
    let rename a := ord.lookup a |>.getD a
    let rec normtype
      | a ->' b => normtype a ->' normtype b
      | a ×'' b => normtype a ×'' normtype b
      | TVar a  => TVar $ rename a
      | TApp h as => TApp h $ as.map normtype
      | KApp h as => KApp (rename h) $ as.map normtype
      | t => t
    let ps := ps.map fun {cls, args} => {cls, args := args.map normtype}
  .Forall (ord.map Prod.snd) ps (normtype body)

def isRecRhs : Expr -> Bool
  | .Fix _ | .Fixcomb _ => true
  | _ => false

def curry : MLType -> MLType
  | t₁ ->' t₂ =>
    go t₁ |>.foldr (· ->' ·) t₂
  | t => t
where
  go | t₃ ×'' t₄ => go t₃ ++ go t₄ | t => [t]

local instance : CoeHead String TV := ⟨.mkTV⟩
local instance : CoeTail TV MLType := ⟨TVar⟩

abbrev dE : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] [] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__eq" , .Forall ["α"] [.unary "Eq" "α"] $ "α" ×'' "α" ->' tBool)
  , ("not"  , .Forall []    [] $ tBool ->' tBool)
  , ("elim" , .Forall ["α"] [] $ tEmpty ->' "a")
  , ("id"   , .Forall ["α"] [] $ "α" ->' "α")
  , ("succ" , .Forall []    [] $ tInt ->' tInt)]

def mkCurriedE (e : List (String × Scheme)) : Env :=
  ⟨ .ofList $
      e.foldl (init := []) fun a p@(sym, .Forall c ps ty) =>
        if sym.startsWith "__"
        then p :: (sym.drop 2, .Forall c ps $ curry ty) :: a
        else p :: a
  , ∅⟩

abbrev defaultE : Env := mkCurriedE dE

end MLType
