import Tigris.typing.types
import Tigris.parsing.types

namespace MLType open Expr TV TypingError Pattern

def curry : MLType -> MLType
  | t₁ ->' t₂ =>
    go t₁ |>.foldr (· ->' ·) t₂
  | t => t
where
  go | t₃ ×'' t₄ => go t₃ ++ go t₄ | t => [t]

local instance : CoeHead String TV := ⟨mkTV⟩
local instance : CoeTail TV MLType := ⟨TVar⟩

@[inline] abbrev tInt := TCon "Int"
@[inline] abbrev tBool := TCon "Bool"
@[inline] abbrev tString := TCon "String"
@[inline] abbrev tUnit := TCon "Unit"

abbrev dE : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__eq" , .Forall ["α"] $ "α" ×'' "α" ->' tBool)
  , ("not"  , .Forall []    $ tBool ->' tBool)
  , ("id"   , .Forall ["α"] $ "α" ->' "α")
  , ("succ" , .Forall []    $ tInt ->' tInt)]

variable {σ : Type}

abbrev defaultE : Env := .ofList $
  dE.foldl (init := []) fun a p@(sym, .Forall c ty) =>
    if sym.startsWith "__"
    then p :: (sym.drop 2, .Forall c $ curry ty) :: a
    else p :: a

class Rewritable (α : Type) where
  apply : Subst -> α -> α
  fv    : α -> Std.HashSet TV
open Rewritable

namespace Rewritables

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
            .Forall as $ apply (as.foldr (fun a s => s.erase a) s) t
  fv      | .Forall as t => fv t \ Std.HashSet.ofList as
instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr ((· ∪ ·) ∘ fv) ∅
instance : Rewritable Env where
  apply s e := e.map fun _ v => apply s v
  fv      e := fv e.values
end Rewritables

def gensym (n : Nat) : String :=
  let (q, r) := (n / 26, n % 26)
  let s := s!"'{Char.ofNat $ r + 97}"
  if q == 0 then s
  else q.toSubDigits.foldl (fun a s => a.push s) s
def normalize : Scheme -> Scheme
  | .Forall _ body =>
    let rec fv 
      | TVar a => [a] | TCon _ => []
      | a ->' b | a ×'' b => fv a ++ fv b
      | TApp _ as => as.flatMap fv
    let ts := (List.rmDup $ fv body);
    let ord := ts.zip $ ts.foldrIdx (fun i _ a => mkTV (gensym i) :: a) []
    let rec normtype
      | a ->' b => normtype a ->' normtype b
      | a ×'' b => normtype a ×'' normtype b
      | TVar a  => match ord.lookup a with
                   | some x => TVar x
                   | none => panic! "some variable is undefined"
      | TApp h as => TApp h $ as.map normtype
      | t => t
  .Forall (List.map Prod.snd ord) (normtype body)
def merge (s₁ s₂ : Subst) := s₁ ∪ s₂.map fun _ v => apply s₁ v
infixl : 65 " ∪' " => merge

def bindTV (a : TV) (t : MLType) : Infer σ Subst :=
  if t == TVar a then pure ∅
  else if a ∈ fv t then throw $ Duplicates a t
  else pure {(a, t)}

partial def unify : MLType -> MLType -> Infer σ Subst
  | l₁ ×'' r₁, l₂ ×'' r₂
  | l₁ ->' r₁, l₂ ->' r₂    => do
    let s₁ <- unify l₁ l₂
    let s₂ <- unify (apply s₁ r₁) (apply s₁ r₂)
    return s₂ ∪' s₁
  | TVar a, t | t, TVar a   => bindTV a t
  | t₁@(TApp h₁ as₁), t₂@(TApp h₂ as₂) =>
    if h₁ != h₂ || as₁.length != as₂.length then
      throw $ NoUnify t₁ t₂
    else
      let rec go (s : Subst)
        | [], [] => pure s
        | x :: xs, y :: ys => do
          let s' <- unify (apply s x) (apply s y)
          go (s' ∪' s) xs ys
        | _, _ => unreachable!
      go ∅ as₁ as₂
  | t@(TCon a), t'@(TCon b) => if a == b then pure ∅ else throw $ NoUnify t t'
  | t₁, t₂                  => throw $ NoUnify t₁ t₂

@[inline] def fresh : Infer σ MLType :=
  modifyGet fun s => (TVar $ mkTV s!"?m{s}", s + 1)

def instantiate : Scheme -> Infer σ MLType
  | .Forall as t => do
    let as' <- as.mapM fun _ => fresh
    let s := as.zip as' |> Std.HashMap.ofList
    return apply s t

def generalize (E : Env) (t : MLType) : Scheme :=
  let as := fv t \ fv E |>.toList
  .Forall as t

def lookupEnv (s : String) (E : Env) : Infer σ (Subst × MLType) :=
  match E.get? s with
  | none => throw $ Undefined s
  | some s => instantiate s >>= fun t => pure (∅ , t)
infix :50 " ∈ₑ " => lookupEnv

@[inline] def peelArrows (t : MLType) : Array MLType × MLType :=
  go #[] t where
  go acc
  | TArr a b => go (acc.push a) b
  | t => (acc, t)

def checkPat (E : Env) (expected : MLType) : Pattern -> Infer σ (Subst × Env)
  | PWild => return (∅, E)
  | PConst $ .PInt  _ => unify tInt    expected <&> apply1
  | PConst $ .PBool _ => unify tBool   expected <&> apply1
  | PConst $ .PStr  _ => unify tString expected <&> apply1
  | PConst $ .PUnit   => unify tUnit   expected <&> apply1

  | PVar x => return (∅, E.insert x (.Forall [] expected))

  | PProd' p₁ p₂ => do
    let tv <- fresh
    let tv' <- fresh
    let s₀ <- unify (tv ×'' tv') expected
    let (E, tv, tv') := (apply s₀ E, apply s₀ tv, apply s₀ tv')
    let (s₁, E) <- checkPat E tv p₁
    let E := apply s₁ E
    let tv' := apply s₁ tv'
    let (s₂, E) <- checkPat E tv' p₂
    return (s₂ ∪' s₁ ∪' s₀, E)

  | PCtor cname args => do
    -- lookup ctor type
    let (_, ctorTy) <- cname ∈ₑ E
    let (argTys, resTy) := peelArrows ctorTy
    if h : argTys.size = args.size then
      let s₁ <- unify resTy expected
      args.size.foldM (init := (s₁, apply s₁ E)) fun i _ (s, e) => do
        let ti := apply s (argTys[i])
        let (si, Ei) <- checkPat e ti (args[i])
        return (si ∪' s, Ei)
    else throw $ InvalidPat s!"expected {argTys.size} binder but received {args.size}"
where
  @[macro_inline] apply1 s := (s, apply s E)

mutual
/--
  perform exactly 1 step of sequential inferrence in CPS style.
  Sequential inferrence is manually unwinded in
  `infer` e.g. `If` `Fix` branch.
  It is done this way so that Lean doesn't complain about termination problem.
    (it can get complicated as `infer1` is mutually recursive with `infer`)
  - returns a continuation and a modified substitution map.
-/
partial def infer1 (E : Env) : (Subst × (MLType -> MLType)) -> Expr -> Infer σ (Subst × (MLType -> MLType))
  | (s, contT), e => do
    let (s', t) <- infer (apply s E) e
    return (s' ∪' s, contT ∘ (t ->' ·))
partial def infer (E : Env) : Expr -> Infer σ (Subst × MLType)
  | Var x => x ∈ₑ E

  | Fun x e => do
    let tv       <- fresh
    let E'       := E.insert x (.Forall [] tv)
    let (s₁, t₁) <- infer E' e
    pure (s₁, apply s₁ tv ->' t₁)

  | Fixcomb e => do
    let tv <- fresh
    let tv' <- fresh
    let (s₁, cont) <- infer1 E (∅, id) e
    let s₂ <- unify (apply s₁ (cont tv')) ((tv ->' tv) ->' tv)
    pure (s₂ ∪' s₁, apply s₂ tv')

  | Fix (Fun fname fbody) => do
    let tv <- fresh
    let E' := E.insert fname (.Forall [] tv)
    let (s₁, t₁) <- infer E' fbody
    let s₂ <- unify (apply s₁ tv) t₁
    let s := s₂ ∪' s₁
    pure (s₂ ∪' s₁, apply s tv)
  | Fix e => do
    let (s₁, t₁) <- infer E e
    pure (s₁, t₁)

  | App e₁ e₂ => do
    let tv       <- fresh
    let (s₁, t₁) <- infer E e₁
    let (s₂, t₂) <- infer (apply s₁ E) e₂
    let s₃       <- unify (apply s₂ t₁) (t₂ ->' tv)
    pure (s₃ ∪' s₂ ∪' s₁, apply s₃ tv)

  | Let x e₁ e₂ => do
    let (s₁, t₁) <- infer E e₁
    let E'       := apply s₁ E
    let t'       := generalize E' t₁
    let (s₂, t₂) <- infer (E'.insert x t') e₂
    pure (s₂ ∪' s₁, t₂)

  | Cond c t e => do
    let tv         <- fresh
    let tv'        <- fresh
    let iter1      <- infer1 E (∅, id) c
    let iter2      <- infer1 E iter1 t
    let (s₁, cont) <- infer1 E iter2 e
    let s₂         <- unify (apply s₁ (cont tv')) (tBool ->' tv ->' tv ->' tv)
    pure (s₂ ∪' s₁, apply s₂ tv')

  | Prod' e₁ e₂ => do
    let (s₁, t₁) <- infer E e₁
    let (s₂, t₂) <- infer (apply s₁ E) e₂
    pure (s₂ ∪' s₁, (apply s₂ t₁) ×'' t₂)

  | Match e discr => do
    let (s₀, te) <- infer E e
    let (s, t) <- discr.foldlM (init := (s₀, none)) fun (s, tRes) (p, body) => do
      let E' := apply s E
      let te' := apply s te
      let (sp, Ep) <- checkPat E' te' p
      let (sb, tb) <- infer Ep body
      let s' := sb ∪' sp ∪' s
      let tb' := apply s' tb
      match tRes with
      | none => return (s', tb')
      | some tres =>
        unify tres tb' <&> (· ∪' s', tRes)
    return (s, t.get!)

  | CB _ => pure (∅, tBool)   | CI _  => pure (∅, tInt)
  | CS _ => pure (∅, tString) | CUnit => pure (∅, tUnit)
end

def closed : Std.HashMap TV MLType × MLType -> Scheme
  | (sub, ty) =>
    generalize ∅ (apply sub ty) |> normalize

def runInfer1 (e : Expr) (E : Env) : Except TypingError Scheme :=
  match runEST fun _ => infer E e |>.run' 0 with
  | .error e => throw e
  | .ok  res => pure $ closed res

def inferToplevel (b : Array Binding) (E : Env) : Except TypingError Env :=
  b.foldlM (init := E) fun E (id, expr) => runInfer1 expr E <&> E.insert id

end MLType

