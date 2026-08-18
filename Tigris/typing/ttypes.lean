import Tigris.utils

def dummyTyDecl : TyDecl := ⟨"__dummy", #[], #[], false, none⟩

instance : Inhabited TyDecl := ⟨dummyTyDecl⟩

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd

def paren b s := bif b then s!"({s})" else s
def paren? b s := bif b then Std.Format.paren s else s
def arr? | _ ->' _ => true | _ => false
def prod? | _ ×'' _ => true | _ => false
def app? | MLType.TApp .. => true | _ => false
def lam? | MLType.TyLam .. => true | _ => false
def sch? | MLType.TSch .. => true | _ => false
def parenthesize s := paren? (arr? s || prod? s || app? s || lam? s || sch? s)
open Std.Format Std.ToFormat in

mutual
def MLType.toStr : MLType -> String
  | .TVar a => toString a
  | .TCon a => a
  | a ->' b => paren (arr? a || sch? a || lam? a) (MLType.toStr a) ++ " → " ++ MLType.toStr b
  | a ×'' b => paren (prod? a || arr? a || sch? a || lam? a) (MLType.toStr a) ++ " × " ++ MLType.toStr b
  | .TApp h [] => MLType.toStr h
  | .TApp h (l :: ls) =>
    let hd := paren (arr? l || prod? l || app? l || lam? l || sch? l) $ MLType.toStr l
    let hStr := paren (arr? h || prod? h || lam? h || sch? h) (MLType.toStr h)
    ls.foldl (init := s!"{hStr} {hd}") fun a s =>
      a ++ " " ++ paren (arr? s || prod? s || app? s || lam? s || sch? s) (MLType.toStr s)
  | .TyLam x body =>
    "Λ" ++ toString x ++ ". " ++ MLType.toStr body
  | .TSch sch => sch.toStr

def MLType.renderFmt : MLType -> Std.Format
  | .TCon a
  | .TVar a => format a
  | a ->' b => group $ paren? (arr? a || sch? a || lam? a) (MLType.renderFmt a) <> "→" ++ indentD (MLType.renderFmt b)
  | a ×'' b => group $ paren? (prod? a || arr? a || sch? a || lam? a) (MLType.renderFmt a) <> "×" ++ indentD (MLType.renderFmt b)
  | .TApp h [] => MLType.renderFmt h
  | .TApp h ls =>
    let hFmt := paren? (arr? h || prod? h || lam? h || sch? h) (MLType.renderFmt h)
    group $ hFmt ++ indentD (joinSep (ls.map fun s => parenthesize s (MLType.renderFmt s)) line)
  | .TyLam x body =>
    nestD $ group $ "Λ" ++ format x ++ "." <+> MLType.renderFmt body
  | .TSch sch => sch.renderFmt
def Pred.toStr : Pred -> String
  | {cls, args} => cls ++ args.foldl (init := "") fun a t => a ++ " "
      ++ paren (arr? t || prod? t || app? t || lam? t || sch? t) (MLType.toStr t)
def Pred.renderFmt : Pred -> Std.Format
  | {cls, args} => cls <> joinSep (args.map fun t => parenthesize t$ MLType.renderFmt t) " "

def Scheme.renderFmt : Scheme -> Std.Format
  | .Forall [] [] t => group $ t.renderFmt
  | .Forall [] pred t => group $ sbracket (joinSep (pred.map Pred.renderFmt) ("," ++ line)) <> t.renderFmt
  | .Forall tv pred t =>
    let preds := if pred.isEmpty then .nil else .text " " ++ sbracket (joinSep (pred.map Pred.renderFmt) ("," ++ line))
    group $ "∀" ++ (joinSep tv " ") ++ preds ++ "," ++ indentD t.renderFmt
def Scheme.toStr : Scheme -> String
  | .Forall [] [] t => t.toStr
  | .Forall [] pred t => pretty (width := 0xFFFF) (sbracket (joinSep (pred.map Pred.toStr) ", ")) ++ " " ++ t.toStr
  | .Forall (t :: ts) pred t' =>
    let preds := if pred.isEmpty then "" else " " ++ toString (pred.map Pred.toStr)
    s!"∀{ts.foldl (· ++ " " ++ toString ·) (toString t)}{preds}, {t'.toStr}"
end

def Pred.unary (c : String) (a : MLType) : Pred := ⟨c, [a]⟩
def Pred.mapArgs (f : MLType -> MLType) : Pred -> Pred
  | {cls, args} => {cls, args := args.map f}
def Scheme.body : Scheme -> MLType
  | .Forall _ _ t => t
def Scheme.ctx : Scheme -> List Pred
  | .Forall _ ps _ => ps

instance : ToString MLType := ⟨MLType.toStr⟩
instance : Std.ToFormat MLType := ⟨MLType.renderFmt⟩

instance : ToString Pred := ⟨Pred.toStr⟩
instance : Std.ToFormat Pred := ⟨Pred.renderFmt⟩

attribute [inline] Scheme.renderFmt Pred.unary Scheme.body Scheme.ctx

instance : ToString Scheme := ⟨Scheme.toStr⟩
instance : Std.ToFormat Scheme := ⟨Scheme.renderFmt⟩
instance : Inhabited Scheme where
  default := .Forall [] [] (MLType.TCon "False")
namespace MLType open TV Expr

def peel : MLType -> MLType × List MLType
  | TApp h as => (h, as)
  | t         => (t, [])

def unary := (TApp · []) ∘ TCon

def ctorScheme (tycon : String) (tparams : List TV) (fields : List (String × MLType)) : Scheme :=
  .Forall tparams []
  $ fields.foldr (TArr ∘ Prod.snd)
  $ TApp (TCon tycon)
  $ tparams.map TVar

inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | NoSynthesize (s : String)
  | WrongCardinal (n : Nat)
  | NoMatch (e : Array Expr) (v : String) (arr : Array $ Array Pattern × Expr)
  | NoMatchL (v : String) (pat : Array String) -- for LExpr interpreter
  | InvalidPat (msg : String)
  | Lowlevel (msg : String)
  | Interrupted
  | NoRankN
  | Ambiguous (msg : String)
  | Impossible (s : String)
  | Duplicates (t : TV) (T : MLType)
  | KindMismatch (k₁ k₂ : Kind)
deriving Repr
open Logging

instance : ToString TypingError where
  toString
  | .Ambiguous msg => s!"Ambiguous: {msg}"
  | .Lowlevel msg => s!"Low-level error: {msg}"
  | .Impossible s => s!"Impossible: {s}"
  | .Interrupted   => s!"Interrupted."
  | .InvalidPat s  => s!"Invalid Pattern: {s}"
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .KindMismatch k₁ k₂ => s!"Kind mismatch: {k₁} vs {k₂}."
  | .NoSynthesize s => s!"failed to synthesize {s}"
  | .Undefined s   => s!"Symbol\n  {s}\nis not in scope."
  | .WrongCardinal n => error s!"Incorrect cardinality. Expected {n}"
  | .NoRankN => s!"Rank-n types must have empty predicate contexts."
  | .NoMatchL v pat =>
    s!"The ctor/constant {v} cannot be matched against\nany of the patterns: {pat}."
  | .NoMatch e v arr =>
    let arr := arr.map $ Array.map Pattern.toStr ∘ Prod.fst
    s!"The expression(s)\n  {repr e} \n==ₑ {v}\ncannot be matched against any of the patterns: {toString arr}."
  | .Duplicates a b =>
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
abbrev ClassMap := Std.HashMap String ClassInfo
abbrev InstanceMap := Std.HashMap String $ Array InstanceInfo

structure Env where
  E : SchemeMap
  tyDecl : TyMap
  clsInfo : ClassMap
  instInfo : InstanceMap
  /--
    type synonyms. In practice, we pass the lookup function (view) `(synTy[·]?)` instead.
  -/
  synTy : Std.HashMap String (List TV × MLType) := ∅
  /-- global tv counter. not used directly but to seed CState's counter, then FState's -/
  nextTV : Nat := 0
deriving Repr

instance : EmptyCollection Env := ⟨∅, ∅, ∅, ∅, ∅, 0⟩
abbrev Logger := String -- This is NOT how one should do logging.
                        -- but Lean doesn't really have a WriterT or MonadWriter
                        -- Lake has something similar, but that's in the build system.
abbrev Subst := Std.TreeMap TV MLType


class Rewritable (α : Type) where
  apply : Subst -> α -> α
  fv    : α -> Std.TreeSet TV

namespace Rewritable open MLType
instance [Ord α] : Union (Std.TreeSet α) := ⟨.merge⟩
instance [Ord α] : SDiff (Std.TreeSet α) := ⟨fun s₁ s₂ => s₂.foldl .erase s₁⟩
instance [BEq α] [Hashable α] : SDiff (Std.HashSet α) := ⟨fun s₁ s₂ => s₂.fold .erase s₁⟩

mutual
/-- use MLType.mkApp instead -/
partial def mkAppT : MLType -> List MLType -> MLType
  | t, [] => t
  | TApp h as₀, as => mkAppT h (as₀ ++ as)
  | TyLam x body, arg :: rest => mkAppT (applyT (Std.TreeMap.insert ∅ x arg) body) rest
  | h, as => TApp h as

partial def applyT : Subst -> MLType -> MLType
  | _, s@(TCon _) => s
  | s, t@(TVar a) => s.getD a t
  | s, t₁ ×'' t₂ => applyT s t₁ ×'' applyT s t₂
  | s, t₁ ->' t₂ => applyT s t₁ ->' applyT s t₂
  | s, TApp h as =>
    -- Substitution may turn the head into a `TyLam`/`TApp`;
    -- so we go through `mkAppT` to β-reduce again.
    mkAppT (applyT s h) (as.map (applyT s))
  | s, TyLam x body =>
    -- shadowing erases x from the substitution.
    TyLam x (applyT (s.erase x) body)
  | s, TSch sch => TSch (applyS s sch)

partial def fvT : MLType -> Std.TreeSet TV
  | TCon _ => ∅ | TVar (.sk _) => ∅ | TVar a => {a}
  | t₁ ->' t₂ | t₁ ×'' t₂ => fvT t₁ ∪ fvT t₂
  | TApp h as => fvT h ∪ as.foldl (· ∪ fvT ·) ∅
  | TyLam x body => (fvT body).erase x
  | TSch sch => fvS sch

partial def applyP : Subst -> Pred -> Pred := (Pred.mapArgs $ applyT ·)
partial def fvP : Pred -> Std.TreeSet TV
  | {args,..} => args.foldl (· ∪ fvT ·) ∅

partial def fvS : Scheme -> Std.TreeSet TV
  | .Forall tvs ps t =>
    let inner := ps.foldr (fvP · ∪ ·) ∅ ∪ fvT t
    tvs.foldl .erase inner
partial def applyS : Subst -> Scheme -> Scheme
  | s, .Forall tvs ps t =>
    let s := s.eraseMany tvs
    .Forall tvs (ps.map (applyP s)) (applyT s t)
end

namespace MLType

mutual
/--
Expand synonym applications. Works a bit like funapp lowering:
full applications simply subst; partial applications eta-expands w/ TyLam.
-/
partial def expandT (syn : String -> Option (List TV × MLType)) : MLType -> MLType
  | a ->' b => expandT syn a ->' expandT syn b
  | a ×'' b => expandT syn a ×'' expandT syn b
  | TCon S =>
    match syn S with
    | some (ps, rhs) => ps.foldr MLType.TyLam $ expandT syn rhs
    | none => TCon S
  | TApp (TCon S) as =>
    match syn S with
    | none => mkAppT (expandT syn (TCon S)) (as.map (expandT syn))
    | some (ps, rhs) =>
      let asl := as.length; let psl := ps.length
      if asl >= psl then
        let (used, rest) := as.splitAt psl
        let sub := List.foldl2 Std.TreeMap.insert ∅ ps used
        rest.foldl (mkAppT · [expandT syn ·]) $ expandT syn $ applyT sub rhs
      else
        let sub := List.foldl2 Std.TreeMap.insert ∅ ps as
        ps.drop asl |>.foldr MLType.TyLam $ expandT syn $ applyT sub rhs
  | TApp h as => mkAppT (expandT syn h) (as.map (expandT syn))
  | TyLam x body => TyLam x (expandT syn body)
  | TSch sch => TSch (expandS syn sch)
  | t => t -- TVar

partial def expandP (syn : String -> Option (List TV × MLType)) : Pred -> Pred := Pred.mapArgs (expandT syn)
partial def expandS (syn : String -> Option (List TV × MLType)) : Scheme -> Scheme
  | .Forall tvs ps t => .Forall tvs (ps.map (expandP syn)) (expandT syn t)
end
end MLType

instance : Rewritable MLType := ⟨applyT, fvT⟩
instance : Rewritable Pred := ⟨applyP, fvP⟩
instance : Rewritable Scheme := ⟨applyS, fvS⟩

/-- Use this instead of MkAppT -/
@[inline] def _root_.MLType.mkApp := mkAppT

instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr (fv · ∪ ·) ∅
instance [Rewritable α] : Rewritable (Array α) where
  apply := Array.map ∘ apply
  fv    := Array.foldr (fv · ∪ ·) ∅
instance : Rewritable Env where
  apply s e := {e with E := e.E.map fun _ v => apply s v}
  fv      e := fv e.E.values
end Rewritable
namespace MLType open Rewritable
@[inline] def merge (s₁ s₂ : Subst) :=
  if s₁.isEmpty then s₂ else
    s₂.foldl (init := s₁) fun acc k v =>
      acc.insert k (apply s₁ v)
infixl : 65 " ∪' " => merge
def gensym (n : Nat) : String :=
  let (q, r) := (n / 25, n % 25)
  let s := Char.ofNat $ r + 0x03b1
  if q == 0 then s.toString
  else s.toString ++ q.toSubscriptString

mutual
partial def unSkolem : MLType -> MLType
  | .TVar (.sk n) => .TVar (.mv n) -- the exact inverse of rigidSub
  | .TVar v => .TVar v
  | .TCon h => .TCon h
  | a ->' b => unSkolem a ->' unSkolem b
  | a ×'' b => unSkolem a ×'' unSkolem b
  | .TApp h as => mkApp (unSkolem h) (as.map unSkolem)
  | .TyLam x body => .TyLam x (unSkolem body)
  | .TSch sch => .TSch (unSkolemS sch)
partial def unSkolemP (p : Pred) : Pred := p.mapArgs unSkolem
partial def unSkolemS : Scheme -> Scheme
  | .Forall vs ps t => .Forall vs (ps.map unSkolemP) (unSkolem t)
end
def isRecRhs : Expr -> Bool
  | .Fix _ | .Fixcomb _ => true
  | _ => false

def curry : MLType -> MLType
  | t₁ ->' t₂ =>
    go t₁ |>.foldr (· ->' ·) t₂
  | t => t
where
  go | t₃ ×'' t₄ => go t₃ ++ go t₄ | t => [t]

local instance : CoeHead String TV := ⟨.named⟩
local instance : CoeTail TV MLType := ⟨TVar⟩

abbrev dE : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] [] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__eq" , .Forall ["α"] [.unary "Eq" "α"] $ "α" ×'' "α" ->' tBool)
  , ("not"  , .Forall []    [] $ tBool ->' tBool)
  , ("elim" , .Forall ["α"] [] $ tEmpty ->' "α")
  , ("id"   , .Forall ["α"] [] $ "α" ->' "α")
  , ("succ" , .Forall []    [] $ tInt ->' tInt)]

abbrev dE' : List (String × Scheme) :=
  [ ("__add", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__eqInt", .Forall [] [] $ tInt ->' tInt ->' tBool)
  , ("__eqBool", .Forall [] [] $ tBool ->' tBool ->' tBool)
  , ("__eqString", .Forall [] [] $ tString ->' tString ->' tBool)
  ]

def mkCurriedE (e : List (String × Scheme)) : Env :=
  ⟨ .ofList $
      e.foldl (init := []) fun a p@(sym, .Forall c ps ty) =>
        if sym.startsWith "__"
        then p :: (sym.drop 2 |>.toString, .Forall c ps $ curry ty) :: a
        else p :: a
  , ∅, ∅, ∅, ∅, 0⟩ -- TODO: modify clsInfo and instInfo


abbrev defaultE : Env := mkCurriedE dE
abbrev defaultE' : Env := mkCurriedE dE'

def containsTSch : MLType -> Bool
  | .TSch _ => true
  | a ->' b | a ×'' b => containsTSch a || containsTSch b
  | .TApp h as =>
    containsTSch h
    || as.attach.any fun a =>
        have := List.sizeOf_lt_of_mem a.property
        containsTSch a.val
  | .TyLam _ body => containsTSch body
  | _ => false

/-- check for predicates in nested foralls. we don't handle those yet -/
def badTSch : MLType -> Bool
  | .TSch (.Forall _ ps _) => !ps.isEmpty
  | a ->' b | a ×'' b => badTSch a || badTSch b
  | .TApp h xs => badTSch h || xs.attach.any fun ⟨x, _⟩ => badTSch x
  | .TyLam _ body => badTSch body
  | _ => false

def validateNoRankN : Scheme -> Except TypingError Unit
  | .Forall _ ps t =>
    if badTSch t || ps.any (List.any (p := badTSch) ∘ Pred.args) then
      throw .NoRankN
    else return ()

end MLType
