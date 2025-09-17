import Tigris.typing.tsyntax
import Tigris.parsing.types
import Tigris.typing.exhaust
import PP.dependentPP

@[inline] def compRM (f : α -> β -> γ) (g : γ -> δ) : α -> β -> δ
  | x, y => g $ f x y

namespace MLType open Expr TV TypingError Pattern Rewritable

def curry : MLType -> MLType
  | t₁ ->' t₂ =>
    go t₁ |>.foldr (· ->' ·) t₂
  | t => t
where
  go | t₃ ×'' t₄ => go t₃ ++ go t₄ | t => [t]

local instance : CoeHead String TV := ⟨mkTV⟩
local instance : CoeTail TV MLType := ⟨TVar⟩

abbrev dE : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__eq" , .Forall ["α"] $ "α" ×'' "α" ->' tBool)
  , ("not"  , .Forall []    $ tBool ->' tBool)
  , ("elim" , .Forall ["α"] $ tEmpty ->' "a")
  , ("id"   , .Forall ["α"] $ "α" ->' "α")
  , ("succ" , .Forall []    $ tInt ->' tInt)]

variable {σ : Type}

abbrev defaultE : Env := ⟨.ofList $
  dE.foldl (init := []) fun a p@(sym, .Forall c ty) =>
    if sym.startsWith "__"
    then p :: (sym.drop 2, .Forall c $ curry ty) :: a
    else p :: a
    , ∅⟩

def gensym (n : Nat) : String :=
  let (q, r) := (n / 25, n % 25)
  let s := Char.ofNat $ r + 0x03b1
  if q == 0 then s.toString
  else s.toString ++ q.toSubscriptString

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
@[inline] def merge (s₁ s₂ : Subst) :=
  s₂.foldl (init := s₁) fun acc k v =>
    acc.insert k (apply s₁ v)
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
  | t@(TApp h₁ []), t'@(TCon s) | t@(TCon s), t'@(TApp h₁ []) =>
    if h₁ == s then pure ∅ else throw $ NoUnify t t'
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
  | t@(TCon a), t'@(TCon b) =>
    if a == b then pure ∅ else throw $ NoUnify t t'
  | t₁, t₂                  => throw $ NoUnify t₁ t₂

@[inline] def fresh : Infer σ MLType :=
  modifyGet fun (s, l) => (TVar $ mkTV s!"?m{s}", s + 1, l)

def instantiate : Scheme -> Infer σ MLType
  | .Forall as t => do
    let as' <- as.mapM fun _ => fresh
    let s := as.zip as' |> .ofList
    return apply s t

def generalize (E : Env) (t : MLType) : Scheme :=
  let as := fv t \ fv E |>.toList
  .Forall as t

def lookupEnv (s : String) (E : Env) : Infer σ (Subst × MLType) :=
  match E.E.get? s with
  | none => throw $ Undefined s
  | some s => instantiate s >>= fun t => pure (∅ , t)
infix :50 " ∈ₑ " => lookupEnv

@[inline] def peelArrows (t : MLType) : Array MLType × MLType :=
  go #[] t where
  go acc
  | TArr a b => go (acc.push a) b
  | t => (acc, t)

def checkPat1 (E : Env) (expected : MLType) (acc : Array MLType) : Pattern -> Infer σ (Array MLType × Subst × Env)
  | PWild => return (acc, ∅, E)
  | PConst $ .PInt  _ => unify tInt    expected <&> apply1 acc
  | PConst $ .PBool _ => unify tBool   expected <&> apply1 acc
  | PConst $ .PStr  _ => unify tString expected <&> apply1 acc
  | PConst $ .PUnit   => unify tUnit   expected <&> apply1 acc

  | PVar x => return (acc.push expected, ∅, {E with E := E.1.insert x (.Forall [] expected)})

  | PProd' p₁ p₂ => do
    let tv <- fresh
    let tv' <- fresh
    let s₀ <- unify (tv ×'' tv') expected
    let (E, tv, tv') := (apply s₀ E, apply s₀ tv, apply s₀ tv')
    let (acc, s₁, E) <- checkPat1 E tv acc p₁
    let E := apply s₁ E
    let tv' := apply s₁ tv'
    let (acc, s₂, E) <- checkPat1 E tv' acc p₂
    return (acc, s₂ ∪' s₁ ∪' s₀, E)

  | PCtor cname args => do
    -- lookup ctor type
    let (_, ctorTy) <- cname ∈ₑ E
    let (argTys, resTy) := peelArrows ctorTy
    if h : argTys.size = args.size then
      let s₁ <- unify resTy expected
      args.size.foldM (init := (acc, s₁, apply s₁ E)) fun i _ (acc, s, e) => do
        let ti := apply s (argTys[i])
        let (acc, si, Ei) <- checkPat1 e ti acc (args[i])
        return (acc, si ∪' s, Ei)
    else throw $ InvalidPat s!"expected {argTys.size} binder but received {args.size}"
where
  @[macro_inline] apply1 acc s := (acc, s, apply s E)

def checkPat (E : Env) (expected : Array MLType) (ps : Array Pattern) : Infer σ (Subst × Env) := do
  if h : ps.size ≠ expected.size then
    throw $ InvalidPat s!"expected {expected.size} pattern but received {ps.size}"
  else
    ps.size.foldM (init := (∅, E)) fun i h (s, E) => do
    let ti := apply s expected[i]
    let (_, si, Ei) <- checkPat1 E ti #[] ps[i]
    return (si ∪' s, Ei)

def metavariable? : MLType -> Bool
  | TVar (.mkTV s) => if s.startsWith "?" then true else false
  | _ => false

def isRecRhs : Expr -> Bool
  | .Fix _ | .Fixcomb _ => true
  | _ => false

private def splitLetGroupRec
  (ae : Array (Symbol × Expr))
  : Array (Symbol × Expr) × Array (Symbol × Expr) :=
  ae.foldl (init := (#[], #[])) fun (recs, nonrecs) b =>
    if isRecRhs b.2 then (recs.push b, nonrecs) else (recs, nonrecs.push b)

/-
  TYPED INFERENCE (Expr -> TExpr)
-/
mutual
partial def inferTLetGroup
  (E : Env)
  (ae : Array (Symbol × Expr))
  (body : Expr)
  : Infer σ (Array (Symbol × Scheme × TExpr) × Subst × MLType × TExpr) := do
  let (recBinds, nonrecBinds) := ae.partition $ isRecRhs ∘ Prod.snd

  let (Eassume, tvs) <-
    recBinds.size.foldM (init := (E, #[])) fun i _ (acc, tvs) => do
      let tv <- fresh
      let (n, _) := recBinds[i]
      return ({acc with E := acc.E.insert n (.Forall [] tv)}, tvs.push tv)

  let mut sRec : Subst := ∅
  let mut tvsRec' := tvs
  let mut typedRec : Array (Symbol × TExpr) := #[]
  for (x, rhs) in recBinds, tv in tvs do
    let Ei := apply sRec Eassume
    let (si, ti, tri) <- inferT Ei rhs
    let tvi := apply si tv
    let su <- unify tvi ti
    let si' := su ∪' si
    sRec := si' ∪' sRec
    tvsRec' := tvsRec'.map (apply si')
    typedRec := typedRec.push (x, apply sRec tri)

  let EgenRec := apply sRec E
  let mut bindsRec : Array (Symbol × Scheme × TExpr) := #[]
  for (x, tr) in typedRec, tv in tvsRec' do
    let sc := generalize EgenRec tv |> normalize
    bindsRec := bindsRec.push (x, sc, tr)

  let {E := Emap, tyDecl} := EgenRec
  let EafterRec : Env :=
    ⟨bindsRec.foldl (init := Emap) (fun m (x, sc, _) => m.insert x sc), tyDecl⟩

  let mut sNon : Subst := ∅
  let mut EN : Env := EafterRec
  let mut bindsNon : Array (Symbol × Scheme × TExpr) := #[]
  for (x, rhs) in nonrecBinds do
    let (si, ti, tri) <- inferT (apply sNon EN) rhs
    sNon := si ∪' sNon
    let EN' := apply sNon EN
    let ty := apply sNon ti
    let te := apply sNon tri
    let sc := generalize EN' ty |> normalize
    bindsNon := bindsNon.push (x, sc, te)
    EN := { EN' with E := EN'.E.insert x sc }

  let (sb, tb, tBody) <- inferT EN body
  let S := sb ∪' sNon ∪' sRec

--  let lookupBind (name : Symbol) : (Symbol × Scheme × TExpr) :=
--    match bindsRec.findSome? (fun tup@(n, _, _) => if n == name then some tup else none) with
--    | some (n, sc, te) => (n, sc, apply S te)
--    | none   => Option.get! $
--      bindsNon.findSome? fun (n, sc, te) => if n == name then some (n, sc, apply S te) else none

--  let bindsOrdered := ae.map (fun (n, _) => lookupBind n)

  let tBody := apply S tBody
  return ( bindsRec ++ bindsNon |>.map fun (n, sc, te) => (n, sc, apply S te)
         , S
         , apply S tb
         , tBody)

partial def inferTExprs (E : Env) (es : Array Expr) : Infer σ (Subst × Array MLType × Array TExpr) :=
  es.foldlM (init := (∅, #[], #[])) fun (s, ts, tes) e => do
    let (si, ti, te) <- inferT (apply s E) e
    let s := si ∪' s
    pure (s, ts.push (apply s ti), tes.push (apply s te))

partial def inferT (E : Env) : Expr -> Infer σ (Subst × MLType × TExpr)
  | Var x => do
    let (_, t) <- x ∈ₑ E
    pure (∅, t, .Var x t)

  | Ascribe e ty => do
    let (s₁, t₁, te) <- inferT E e
    let s₂ <- unify (apply s₁ t₁) ty
    let ty' := apply s₂ ty
    pure (s₂ ∪' s₁, ty', .Ascribe (apply (s₂ ∪' s₁) te) ty')

  | Fun x e => do
    let tv <- fresh
    let {E, tyDecl} := E
    let (s₁, t₁, te) <- inferT ⟨E.insert x (.Forall [] tv), tyDecl⟩ e
    let argTy := apply s₁ tv
    let funTy := argTy ->' t₁
    pure (s₁, funTy, .Fun x argTy te funTy)

  | Fixcomb e => do
    let tv  <- fresh
    let (s₁, t₁, te) <- inferT E e
    let s₂ <- unify t₁ (tv ->' tv)
    let S := s₂ ∪' s₁
    pure (S, apply S tv, .Fixcomb (apply S te) (apply S tv))

  | Fix (Fun fname fbody) => do
    let tv <- fresh
    let {E, tyDecl} := E
    let (s₁, t₁, tBody) <- inferT ⟨E.insert fname (.Forall [] tv), tyDecl⟩ fbody
    let s₂ <- unify (apply s₁ tv) t₁
    let S := s₂ ∪' s₁
    let argTy := apply S tv
    let resTy := apply S t₁
    let funTy := argTy ->' resTy
    let tFun := .Fun fname argTy (apply S tBody) funTy
    pure (S, argTy, .Fix tFun argTy)

  | Fix fe => do
    let (s₁, t₁, te) <- inferT E fe
    pure (s₁, t₁, .Fix te t₁)

  | App e₁ e₂ => do
    let tv <- fresh
    let (s₁, t₁, tE₁) <- inferT E e₁
    let (s₂, t₂, tE₂) <- inferT (apply s₁ E) e₂
    let s₃ <- unify (apply s₂ t₁) (t₂ ->' tv)
    let resTy := apply s₃ tv
    let S := s₃ ∪' s₂ ∪' s₁
    pure (S, resTy, .App (apply S tE₁) (apply S tE₂) resTy)

  | Let ae e₂ => do
    let (binds, s, tb, tBody) <- inferTLetGroup E ae e₂
    pure (s, tb, .Let binds tBody tb)

  | Cond c t e => do
    let (s₁, tc, tC) <- inferT E c
    let sBool <- unify (apply s₁ tc) tBool
    let S1 := sBool ∪' s₁
    let (s₂, tt, tT) <- inferT (apply S1 E) t
    let (s₃, te, tE) <- inferT (apply (s₂ ∪' S1) E) e
    let sRes <- unify (apply s₃ tt) te
    let S := sRes ∪' s₃ ∪' s₂ ∪' S1
    let rty := apply S tt
    pure (S, rty, .Cond (apply S tC) (apply S tT) (apply S tE) rty)

  | Prod' e₁ e₂ => do
    let (s₁, t₁, tE₁) <- inferT E e₁
    let (s₂, t₂, tE₂) <- inferT (apply s₁ E) e₂
    let S := s₂ ∪' s₁
    let ty := (apply s₂ t₁) ×'' t₂
    pure (S, ty, .Prod' (apply S tE₁) (apply S tE₂) ty)

  | Match es discr => do
    let (s₀, te, tScrs) <- inferTExprs E es
    let (s, res?, exp, tRows) <-
      discr.foldlM (init := (s₀, none, te, #[])) fun (s, res?, _, tRows) (ps, body) => do
        let Eb := apply s E
        let expected := te.map (apply s)
        let (spat, Eext) <- checkPat Eb expected ps
        let (sbody, tbody, tBody) <- inferT (apply spat Eext) body
        let Sb := sbody ∪' spat ∪' s
        let tbody := apply Sb tbody
        let tBody := apply Sb tBody
        if let some rt := res? then
          let Sunify <- unify (apply Sb rt) tbody
          let s' := Sunify ∪' Sb
          let rt' := apply s' rt
          pure (s', some rt', expected, tRows.push (ps, tBody))
        else
          pure (Sb, some tbody, expected, tRows.push (ps, tBody))

    -- Exhaustiveness and redundancy info
    let exp' := exp.map (apply s)
    let (ex, mat, tyCols) := Exhaustive.exhaustWitness E exp' discr
    let red :=
      if let some _ := ex then #[] else
        Exhaustive.redundantRows E tyCols mat

    -- Logging as before
    let msg :=
      if let some ex := ex then
        Logging.warn
          s!"Partial pattern matching, an unmatched candidate is\
             \n  {ex.map (·.render)}\n"
      else
        if red.isEmpty then "" else
          letI br := red.foldl (init := "") fun a i =>
            s!"{a}\n  {i + 1})  {discr[i]!.1.map (·.render)}"
          Logging.warn s!"Found redundant alternatives at{br}\n"
    modify fun (n, l) => (n, l ++ msg)
    let tRows :=
      if red.isEmpty then tRows else
        Prod.fst $ tRows.size.fold (init := (#[], red, 0)) fun i _ (acc, red, idx) =>
          if red.binSearchContains i (fun m n => m < n) idx
          then (acc, red, idx + 1) else (acc.push tRows[i], red, idx)
    let retTy := res?.get!
    let tScrs' := tScrs.map (apply s)
    pure (s, retTy, .Match tScrs' tRows retTy ex red)

  | CB b => pure (∅, tBool, .CB b tBool)
  | CI i => pure (∅, tInt,  .CI i tInt)
  | CS s => pure (∅, tString, .CS s tString)
  | CUnit => pure (∅, tUnit, .CUnit tUnit)
end

-- Normal Algorithm W
mutual
partial def inferLetGroup
  (E : Env)
  (ae : Array (Symbol × Expr))
  (body : Expr) : Infer σ (Array (Symbol × Scheme) × Subst × MLType) := do

  let (recBinds, nonrecBinds) := ae.partition $ isRecRhs ∘ Prod.snd
  let (Eassume, tvs) <-
    recBinds.size.foldM (init := (E, #[])) fun i _ (acc, tvs) => do
      let tv <- fresh
      let (n, _) := recBinds[i]
      return ({acc with E := acc.E.insert n (.Forall [] tv)}, tvs.push tv)

  let mut sRec : Subst := ∅
  let mut tvsRec' := tvs
  for (x, rhs) in recBinds, tv in tvs do
    let Ei := apply sRec Eassume
    let (si, ti) <- infer Ei rhs
    let tvi := apply si tv
    let su <- unify tvi ti
    let si' := su ∪' si
    sRec := si' ∪' sRec
    tvsRec' := tvsRec'.map (apply si')

  let EgenRec := apply sRec E
  let mut Ecur := EgenRec
  let mut schemesRec : Array (Symbol × Scheme) := #[]
  for (x, _) in recBinds, tv in tvsRec' do
    let sch := generalize EgenRec tv
    Ecur := {Ecur with E := Ecur.E.insert x sch}
    schemesRec := schemesRec.push (x, sch)

  let mut sNon : Subst := ∅
  let mut schemesNon : Array (Symbol × Scheme) := #[]
  for (x, rhs) in nonrecBinds do
    let (si, ti) <- infer (apply sNon Ecur) rhs
    sNon := si ∪' sNon
    let E' := apply sNon Ecur
    let ty := apply sNon ti
    let sch := generalize E' ty
    schemesNon := schemesNon.push (x, sch)
    Ecur := {E' with E := E'.E.insert x sch}

--  let lookupSch (name : Symbol) : (Symbol × Scheme) :=
--    match
--      schemesRec.findSome? fun tup@(n, _) => 
--        if n == name then some tup else none 
--    with
--    | some b => b
--    | none   => Option.get! $
--      schemesNon.findSome? (fun tup@(n, _) => if n == name then some tup else none)

--  let schemesOrdered := ae.map fun (n, _) => lookupSch n

  let (sb, tb) <- infer Ecur body
  pure (schemesNon ++ schemesRec, sb ∪' sNon ∪' sRec, tb)

/-- Infer a vector of expressions left-to-right, composing substitutions. -/
partial def inferExprs (E : Env) (es : Array Expr) : Infer σ (Subst × Array MLType) :=
  es.foldlM (init := (∅, #[])) fun (s, ts) i => do
    let E := apply s E
    let (si, ti) <- infer E i
    let s := si ∪' s
    return (si ∪' s, ts.push $ apply s ti)
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

  | Ascribe e ty => do
    let (s₁, t₁) <- infer E e
    let s₂ <- unify (apply s₁ t₁) ty
    pure (s₂ ∪' s₁, apply s₂ ty)

  | Fun x e => do
    let tv          <- fresh
    let {E, tyDecl} := E
    let (s₁, t₁)    <- infer ⟨E.insert x (.Forall [] tv), tyDecl⟩ e
    pure (s₁, apply s₁ tv ->' t₁)

  | Fixcomb e => do
    let tv         <- fresh
    let tv'        <- fresh
    let (s₁, cont) <- infer1 E (∅, id) e
    let s₂         <- unify (apply s₁ (cont tv')) ((tv ->' tv) ->' tv)
    pure (s₂ ∪' s₁, apply s₂ tv')

  | Fix (Fun fname fbody) => do
    let tv          <- fresh
    let {E, tyDecl} := E
    let (s₁, t₁)    <- infer ⟨E.insert fname (.Forall [] tv), tyDecl⟩ fbody
    let s₂          <- unify (apply s₁ tv) t₁
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

  | Let ae e₂ => Prod.snd <$> inferLetGroup E ae e₂

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

  | Match es discr => do
    let (s₀, te) <- inferExprs E es
    let (s, res?, exp) <- discr.foldlM (init := (s₀, none, te)) fun (s, res?, _) (ps, body) => do
      let Eb := apply s E
      let expected := te.map (apply s)
      let (spat, Eext) <- checkPat Eb expected ps
      let (sbody, tbody) <- infer (apply spat Eext) body
      let Sb := sbody ∪' spat ∪' s
      let tbody := apply Sb tbody
      if let some rt := res? then
        let Sunify <- unify (apply Sb rt) tbody
        let s := Sunify ∪' Sb
        return (s, some $ apply s rt, expected)
      else return (Sb, tbody, expected)

    letI exp := exp.map $ apply s
    let (ex, mat, ty) := Exhaustive.exhaustWitness E exp discr
    let msg :=
      if let some ex := ex then
        Logging.warn
          s!"Partial pattern matching, an unmatched candidate is\
             \n  {ex.map (·.render)}\n"
      else -- we only perform redundant check if case analysis is exhaustive
        let red := Exhaustive.redundantRows E ty mat
        if red.isEmpty then "" else
          letI br := red.foldl (init := "") fun a i =>
            s!"{a}\n  {i + 1})  {discr[i]!.1.map (·.render)}"
          Logging.warn s!"Found redundant alternatives at{br}\n"
    modify fun (n, l) => (n, l ++ msg)

    pure (s, res?.get!)

  | CB _ => pure (∅, tBool)   | CI _  => pure (∅, tInt)
  | CS _ => pure (∅, tString) | CUnit => pure (∅, tUnit)
end

def closed : Subst × MLType -> Scheme
  | (sub, ty) => generalize ∅ (apply sub ty) |> normalize

def runInfer1 (e : Expr) (E : Env) : Except TypingError $ Scheme × Logger :=
  match runEST fun _ => infer E e |>.run (0, "") with
  | .error e => throw e
  | .ok  (res, _, log) => pure (closed res, log)

def runInferT1 (e : Expr) (E : Env) : Except TypingError (TExpr × Scheme × Logger) :=
  match runEST fun _ => inferT E e |>.run (0, "") with
  | .error err => throw err
  | .ok ((sub, ty, te), _, log) =>
      let sch := closed (sub, ty)
      let te := apply sub te
      pure (te, sch, log)

def inferGroupT
  (b : Array Binding) (E : Env) (L : Logger)
  : Except TypingError (TopDeclT × Env × Logger) := do
  let ((ES, _, _), _, l) <- runEST fun _ => inferTLetGroup E b CUnit |>.run (0, "")
  let (E, ES) :=
    let ⟨E, T⟩ := E
    Prod.map (Env.mk · T) id $
      ES.foldl (init := (E, #[])) fun (E, ES) (id, s, te) =>
        let s := normalize s
        (E.insert id s, ES.push (id, s, te))
  return (TopDeclT.idBind ES, E, L ++ l)

def inferGroup
  (b : Array Binding) (E : Env) (L : Logger)
  : Except TypingError (Array (Symbol × Scheme) × Env × Logger) := do
  let ((ES, _, _), _, l) <- runEST fun _ => inferLetGroup E b CUnit |>.run (0, "")
  let (E, ES) :=
    let ⟨E, T⟩ := E
    Prod.map (Env.mk · T) id $
      ES.foldl (init := (E, #[])) fun (E, ES) (id, s) =>
        let s := normalize s
        (E.insert id s, ES.push (id, s))
  return (ES, E, L ++ l)

def inferToplevel (b : Array TopDecl) (E : Env) : Except TypingError (Env × Logger) :=
  b.foldlM (init := (E, "")) fun (E, L) b =>
    match b with
    | .extBind s _ sch => pure
      ({E with E := E.E.insert s sch}, L)
    | .idBind group => inferGroup group E L <&> Prod.snd
    | .tyBind ty@{ctors, tycon, param} =>
      return (· , L) <| ctors.foldl (init := E) fun {E, tyDecl} (cname, fields, _) =>
        letI s := ctorScheme tycon (param.foldr (List.cons ∘ mkTV) []) fields
        ⟨E.insert cname s, tyDecl.insert tycon ty⟩
    | .patBind (pat, expr) => do
      let (.Forall _ te, l₁) <- runInfer1 expr E

      let ((_, _, E), _, l₂) <- runEST fun _ => checkPat1 E te #[] pat |>.run (nat_lit 0, "")
      -- toplevel binding can never be redundant
      let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
      let l₃ :=
        if let some ex := ex then
          Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map Pattern.render} are ignored\n"
        else ""
      return (E, l₁ ++ l₂ ++ l₃)

def inferToplevelT (b : Array TopDecl) (E : Env) : Except TypingError (Array TopDeclT × Env × Logger) :=
  b.foldlM (init := (#[], E, "")) fun (acc, E, L) b => do
    match b with
    | .extBind s n sch@(.Forall _ t) => pure $
      (acc.push (.idBind #[(s, sch,TExpr.Var n t)]) ,{E with E := E.E.insert s sch}, L)
    | .idBind group =>
      let (a, E, l) <- inferGroupT group E L
      return (acc.push a, E, l)
    | .tyBind ty@{ctors, tycon, param} =>
      return (acc.push (.tyBind ty), ·, L) <| ctors.foldl (init := E) fun {E, tyDecl} (cname, fields, _) =>
        letI s := ctorScheme tycon (param.foldr (List.cons ∘ mkTV) []) fields
        ⟨E.insert cname s, tyDecl.insert tycon ty⟩
    | .patBind (pat, expr) => do
      let (e,.Forall _ te, l₁) <- runInferT1 expr E

      let ((_, _, E), _, l₂) <- runEST fun _ => checkPat1 E te #[] pat |>.run (nat_lit 0, "")
      -- toplevel binding can never be redundant
      let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
      let l₃ :=
        if let some ex := ex then
          Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map Pattern.render} are ignored\n"
        else ""
      return (acc.push $ .patBind (pat, e), E, l₁ ++ l₂ ++ l₃)

end MLType
