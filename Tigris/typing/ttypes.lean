import Tigris.utils

def dummyTyDecl : TyDecl := ⟨"__dummy", #[], #[], false⟩

instance : Inhabited TyDecl := ⟨dummyTyDecl⟩

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd

def paren b s := bif b then s!"({s})" else s
def paren? b s := bif b then Std.Format.paren s else s
def arr? | _ ->' _ => true | _ => false
def prod? | _ ×'' _ => true | _ => false
def parenthesize s := paren? (arr? s || prod? s)
open Std.Format Std.ToFormat in open Logging (magenta) in
mutual
def MLType.toStr : MLType -> String
  | .TVar a => toString a
  | .TCon a => a
  | a ->' b =>
    paren (arr? a) (MLType.toStr a) ++ " → " ++ MLType.toStr b
  | a ×'' b => paren (prod? a) (MLType.toStr a) ++ " × " ++ MLType.toStr b
  | .TApp s [] | .KApp (.mkTV s) [] => s
  | .TApp s (l :: ls) | .KApp s (l :: ls) =>
    let hd := paren (arr? l || prod? l) $ MLType.toStr l
    ls.foldl (init := s!"{s} {hd}") fun a s =>
      a ++ " " ++ paren (arr? l || prod? l) (MLType.toStr s)
  | .TSch sch => sch.toStr

def MLType.renderFmt : MLType -> Std.Format
  | .TVar a => format a
  | .TCon a => magenta a
  | a ->' b => nestD $ group $ paren? (arr? a) (MLType.renderFmt a) <> "→" <+> MLType.renderFmt b
  | a ×'' b => nestD $ group $ paren? (prod? a) (MLType.renderFmt a) <> "×" <+> MLType.renderFmt b
  | .TApp s ls | .KApp (.mkTV s) ls =>
    nestD $ group
    $ joinSep (text (magenta s) :: ls.map fun s => parenthesize s (MLType.renderFmt s)) line
  | .TSch sch => sch.renderFmt

def Pred.toStr : Pred -> String
  | {cls, args} => cls ++ args.foldl (· ++ " " ++ MLType.toStr ·) ""
def Pred.renderFmt : Pred -> Std.Format
  | {cls, args} =>
    Logging.magenta cls ++ args.foldl (· ++ " " ++ MLType.renderFmt ·) ""

def Scheme.renderFmt : Scheme -> Std.Format
  | .Forall _ [] t' => t'.renderFmt
  | .Forall _ pred t' => toString (pred.map Pred.renderFmt) <> t'.renderFmt
def Scheme.toStr : Scheme -> String
  | .Forall [] [] t => t.toStr
  | .Forall [] pred t => toString (pred.map Pred.renderFmt) ++ " " ++ t.toStr
  | .Forall (t :: ts) pred t' =>
    let preds := if pred.isEmpty then "" else " " ++ toString (pred.map Pred.toStr)
    s!"∀ {ts.foldl (· ++ " " ++ toString ·) (toString t)}{preds}, {t'.toStr}"
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

def ctorScheme (tycon : String) (tparams : List TV) (fields : List (String × MLType)) : Scheme :=
  .Forall tparams []
  $ fields.foldr (TArr ∘ Prod.snd)
  $ TApp tycon
  $ tparams.map TVar


inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | NoSynthesize (s : String)
  | WrongCardinal (n : Nat)
  | NoMatch (e : Array Expr) (v : String) (arr : Array $ Array Pattern × Expr)
  | InvalidPat (msg : String)
  | Interrupted
  | NoRankN
  | Ambiguous (msg : String)
  | Impossible (s : String)
  | Duplicates (t : TV) (T : MLType) deriving Repr
open Logging
instance : ToString TypingError where
  toString
  | .Ambiguous msg => s!"Ambiguous: {msg}"
  | .Impossible s => s!"Impossible: {s}"
  | .Interrupted   => s!"Interrupted."
  | .InvalidPat s  => s!"Invalid Pattern: {s}"
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .NoSynthesize s => s!"failed to synthesize {s}"
  | .Undefined s   => s!"Symbol\n  {s}\nis not in scope."
  | .WrongCardinal n => error s!"Incorrect cardinality. Expected {n}"
  | .NoRankN => s!"Rank-n types are not supported yet."
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
abbrev ClassMap := Std.HashMap String ClassInfo
abbrev InstanceMap := Std.HashMap String $ Array InstanceInfo

structure Env where
  E : SchemeMap
  tyDecl : TyMap
  clsInfo : ClassMap
  instInfo : InstanceMap
deriving Repr

instance : EmptyCollection Env := ⟨∅, ∅, ∅, ∅⟩
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

mutual
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
  | s, TSch sch => TSch (applyS s sch)

partial def fvT : MLType -> Std.HashSet TV
  | TCon _ => ∅ | TVar a => {a}
  | t₁ ->' t₂ | t₁ ×'' t₂ => fvT t₁ ∪ fvT t₂
  | TApp _ as => as.foldl (· ∪ fvT ·) ∅
  | KApp v as => {v} ∪ as.foldl (· ∪ fvT ·) ∅
  | TSch sch => fvS sch

partial def applyP : Subst -> Pred -> Pred := (Pred.mapArgs $ applyT ·)
partial def fvP : Pred -> Std.HashSet TV
  | {args,..} => args.foldl (· ∪ fvT ·) ∅

partial def fvS : Scheme -> Std.HashSet TV
  | .Forall tvs ps t =>
    let inner := ps.foldr (fvP · ∪ ·) ∅ ∪ fvT t
    tvs.foldl .erase inner
partial def applyS : Subst -> Scheme -> Scheme
  | s, .Forall tvs ps t =>
    let s := s.eraseMany tvs
    .Forall tvs (ps.map (applyP s)) (applyT s t)
end

instance : Rewritable MLType := ⟨applyT, fvT⟩
instance : Rewritable Pred := ⟨applyP, fvP⟩
instance : Rewritable Scheme := ⟨applyS, fvS⟩

instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr (fv · ∪ ·) ∅
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

partial def normalize : Scheme -> Scheme
  | .Forall _ ps body =>
    let ts := fv ps ∪ fv body |>.toList
    let ord := ts.mapIdx (fun i tv => (tv, TV.mkTV (gensym i)))
    let rename a := ord.lookup a |>.getD a
    let rec normtype (blocked : Std.HashSet TV)
      | a ->' b | a ×'' b => normtype blocked a ->' normtype blocked b
      | .TVar a => .TVar $ if a ∈ blocked then a else rename a
      | .TApp h as => .TApp h $ as.map $ normtype blocked
      | .KApp v as =>
        let v := if v ∈ blocked then v else rename v
        .KApp v $ as.map $ normtype blocked
      | .TSch $ .Forall tvs ps ty =>
        let blocked := blocked.insertMany tvs
        let ps := ps.map fun p => p.mapArgs $ normtype blocked
        .TSch $ .Forall tvs ps $ normtype blocked ty
      | t => t

    let ps := ps.map fun p => p.mapArgs $ normtype ∅
  .Forall (ord.map Prod.snd) ps (normtype ∅ body)

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

abbrev dE' : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] [] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    [] $ tInt ×'' tInt ->' tInt)
  , ("__eqInt", .Forall [] [] $ tInt ->' tInt ->' tBool)
  , ("__eqBool", .Forall [] [] $ tBool ->' tBool ->' tBool)
  , ("__eqString", .Forall [] [] $ tString ->' tString ->' tBool)
--  , ("__eq" , .Forall ["α"] [.unary "Eq" "α"] $ "α" ×'' "α" ->' tBool)
  , ("elim" , .Forall ["α"] [] $ tEmpty ->' "a")
  , ("succ" , .Forall []    [] $ tInt ->' tInt)]

def mkCurriedE (e : List (String × Scheme)) : Env :=
  ⟨ .ofList $
      e.foldl (init := []) fun a p@(sym, .Forall c ps ty) =>
        if sym.startsWith "__"
        then p :: (sym.drop 2, .Forall c ps $ curry ty) :: a
        else p :: a
  , ∅, ∅, ∅⟩ -- TODO: modify clsInfo and instInfo


abbrev defaultE : Env := mkCurriedE dE
abbrev defaultE' : Env := mkCurriedE dE'

def containsTSch : MLType -> Bool
  | .TSch _ => true
  | a ->' b | a ×'' b => containsTSch a || containsTSch b
  | .TApp _ as | .KApp _ as => as.attach.any fun a =>
    have := List.sizeOf_lt_of_mem a.property
    containsTSch a.val
  | _ => false

def validateNoRankN : Scheme -> Except TypingError Unit
  | .Forall _ ps t =>
    if t.containsTSch || ps.any (List.any (p := containsTSch) ∘ Pred.args) then
      throw .NoRankN
    else return ()

end MLType
