import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.constraint
import Tigris.typing.resolve
import Tigris.typing.kinds

def MLType.isTApp : MLType -> Bool
  | .TApp .. => true | _ => false

inductive FExpr where
  | CI     (i : Int)    (ty : MLType)
  | CS     (s : String) (ty : MLType)
  | CB     (b : Bool)   (ty : MLType)
  | CUnit               (ty : MLType)
  | Var    (x : String) (ty : MLType)                 -- monomorphic view at site
  | Fun    (param : String) (paramTy : MLType)
           (body : FExpr) (ty : MLType)               -- paramTy -> body.ty = ty
  | App    (f : FExpr) (a : FExpr) (ty : MLType)      -- result type after application
  | TyLam  (a : TV) (body : FExpr)                    -- type abstraction
  | TyApp  (f : FExpr) (arg : MLType)                 -- type application
  | Let    (binds : Array (String × Scheme × FExpr))  -- each binding elaborated & wrapped
           (body : FExpr) (ty : MLType)
  | Prod'  (l r : FExpr) (ty : MLType)
  | Cond   (c t e : FExpr) (ty : MLType)
  | Match  (discr : Array FExpr)
           (branches   : Array (Array Pattern × FExpr))
           (resTy      : MLType)
           (counterexample : Option (List Pattern))
           (redundantRows  : Array Nat)
  | Fix    (e : FExpr) (ty : MLType)                  -- rec tag
  | Proj   (src : FExpr) (mname : String)
           (idx : Nat) (ty : MLType)                  -- field projection
with @[computed_field]
  getTy : FExpr -> MLType
  | .CI _ ty | .CS _ ty | .CB _ ty | .CUnit ty
  | .Var _ ty | .Fun _ _ _ ty | .App _ _ ty
  | .Let _ _ ty | .Prod' _ _ ty | .Cond _ _ _ ty
  | .Match _ _ ty _ _ | .Fix _ ty | .Proj _ _ _ ty => ty
  | .TyLam _ f
  | .TyApp f _ => f.getTy
    -- TyApp currently doesn't carry result type.
    -- f.getTy should NOT yield a arrow type as polys are erased after instantiation
deriving Repr, Inhabited

namespace SysF open MLType TExpr Rewritable
open Resolve (resolvePred)

abbrev FEnv := Std.TreeMap String Scheme
abbrev DictScope := List (Pred × String)  -- predicate template + dict variable name

structure DictEntry where
  name   : String
  /-- gensym counter -/
  idx    : Nat
  scheme : Scheme
  fe     : FExpr

structure FState where
  log    : Logger := ""
  memo   : Std.HashMap Pred DictEntry := ∅
  gensym : Nat := 0
  /-- nesting depth of withMemoScope where only the outermost scope resets the
  memo and places the synthesized dictionary bindings -/
  memoDepth : Nat := 0
  ke     : KindEnv := ∅
deriving Inhabited

abbrev F := EStateM TypingError FState
abbrev Blocked := Std.HashSet String

@[inline] def logAppend (s : String) : F Unit :=
  modify fun st => {st with log := st.log ++ s}

@[inline] def freshIdx (pfx : String) : F (String × Nat) :=
  modifyGet fun st => ((pfx ++ toString st.gensym, st.gensym), {st with gensym := st.gensym + 1})

@[inline] def fresh (pfx := "_rd") : F String := Prod.fst <$> freshIdx pfx

@[inline] def memoLookup (p : Pred) : F (Option DictEntry) := get <&> (·.memo[p]?)

@[inline] def memoInsert (p : Pred) (entry : DictEntry) : F Unit :=
  modify fun st => {st with memo := st.memo.insert p entry}

instance : MonadLift (Except TypingError) F where
  monadLift
  | .error e => throw e
  | .ok res => return res

namespace Helper

@[inline] def dictTypeOfPred : Pred -> MLType
  | {cls, args,..} => MLType.mkApp (TCon cls) args

@[inline] def monoOfTSch : MLType -> MLType
  | .TSch (.Forall _ _ t) => t
  | t => t

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e
@[inline] def mkApp (f a : FExpr) : FExpr :=
  -- decomposeArr peels a leading TSch and the arrow spine, so a rank-n head
  -- yields the codomain instead of the whole scheme
  .App f a $ Prod.snd $ decomposeArr f.getTy

def eqSkolem : MLType -> MLType -> Bool := go.on ηNF
where
  go : MLType -> MLType -> Bool
    | .TVar (.sk n), .TVar (.mv m) | .TVar (.mv m), .TVar (.sk n) => n == m
    | .TVar v, .TVar w => v == w
    | .TApp h₁ as₁, .TApp h₂ as₂ =>
      if go h₁ h₂ then
        List.all2 (fun ⟨t, _⟩ ⟨t', _⟩ => go t t')
          as₁.attach
          as₂.attach
      else false
    | .TyLam x b₁, .TyLam y b₂ => x == y && go b₁ b₂
    | t₁ ->' t₂, u₁ ->' u₂ | t₁ ×'' t₂, u₁ ×'' u₂ => go t₁ u₁ && go t₂ u₂
    | .TCon a, .TCon b => a == b
    | _, _ => false
  termination_by t₁ t₂ => (t₁, t₂)

def predEqSkolem (templ goal : Pred) : Bool :=
  templ.cls == goal.cls && List.all2 eqSkolem templ.args goal.args

-- linear search, scope is usually tiny.
def lookupDictVar (scope : DictScope) (goal : Pred) : Option (String × MLType) :=
  go scope where
  go
  | [] => none
  | (templ, v) :: xs =>
    if predEqSkolem templ goal /- || predEqGoal templ goal -/ then some (v, dictTypeOfPred templ)
    else go xs

@[inline] def isGroundPred : Pred -> Bool := Std.TreeSet.isEmpty ∘ fv

@[inline] def patOfIdx (ctor : Symbol) (idx : Nat) (sz : Nat) : Pattern :=
  .PCtor ctor $ Array.replicate sz .PWild |>.set! idx (.PVar s!"m_{ctor}_{idx}")

def mvs (p : Pred) : (List TV × List TV) :=
  let vs := fv p
  vs.foldl
    (fun (mv, iv) tv =>
      match tv with
      | .mv .. => (tv :: mv, iv)
      | .inst .. => (mv, tv :: iv)
      | _ => (mv, iv))
    ([], [])

def stuckMessage (p : Pred) (method : String) : TypingError :=
  match mvs p with
  | ([], []) => .NoSynthesize s!"{p}: missing in-scope instance for method {method}\n"
  | (mvs, []) =>
    .Ambiguous
      s!"{p}: typeclass elaboration is stuck because of metavariable(s)\n  \
         {toString mvs}\n\
         induced by a call to {method}. Consider adding type ascriptions.\n"
  | (mvs, ivs) =>
    .Ambiguous
      s!"{p}: cannot deduce because of metavariable(s)\n  \
         {toString ivs} {if mvs.isEmpty then "" else toString mvs}\n\
         induced by a call to {method} though this ambiguity\n\
         may be introduced at the definition of class {p.cls}"

def peelFun (acc : List (String × MLType)) : FExpr -> List (String × MLType) × FExpr
  | .Fun p pty b _ => peelFun ((p, pty) :: acc) b
  | t => (acc.reverse, t)

def peelTyLam (acc : List String) : FExpr -> List String × FExpr
  | .TyLam p b => peelTyLam (TV.toStr p :: acc) b
  | t => (acc.reverse, t)
def peelSch1 : MLType -> Option (List TV × List Pred × MLType)
  | .TSch (.Forall vs ps t) => some (vs, ps, t)
  | _ => none

def peelTyLamTV (acc : List TV) : FExpr -> List TV × FExpr
  | .TyLam a b => peelTyLamTV (a :: acc) b
  | t => (acc.reverse, t)

def stripDupLeadingTyLams (qs : List TV) (core : FExpr) : FExpr :=
  let (tvs, body) := peelTyLamTV [] core
  if tvs == qs then body else core

def pvs : Pattern -> Array String
  | .PVar x => #[x] | .PWild => #[]
  | .PConst _ => #[] | .PProd' p q => pvs p ++ pvs q
  | .PCtor _ args => args.flatMap pvs

def wrapExtracted (sch : Scheme) (e : FExpr) : FExpr :=
  match sch with
  | .Forall _ _ b =>
    match peelSch1 b with
    | some (innerTVs, innerPs, _) =>
      if innerPs.isEmpty then wrapTyLams innerTVs e
      else e
    | none => e
local infixr:80 " <;> " => Nat.lt_trans
def mapTypes (f : MLType -> MLType) (g : Scheme -> Scheme := id) : FExpr -> FExpr
  | .CI i ty              => .CI i (f ty)
  | .CS s ty              => .CS s (f ty)
  | .CB b ty              => .CB b (f ty)
  | .Proj src m i ty      => .Proj (mapTypes f g src) m i (f ty)
  | .CUnit ty             => .CUnit (f ty)
  | .Var x ty             => .Var x (f ty)
  | .Fun p pTy b ty       => .Fun p (f pTy) (mapTypes f g b) (f ty)
  | .App fn arg ty        => .App (mapTypes f g fn) (mapTypes f g arg) (f ty)
  | .TyLam a b            => .TyLam a (mapTypes f g b)
  | .TyApp fe targ        => .TyApp (mapTypes f g fe) (f targ)
  | .Let binds body ty    =>
    let binds := binds.attach.map fun ⟨(x, sch, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd sch rhs
          <;> prod_sizeOf_lt_snd x (sch, rhs)
          <;> Array.sizeOf_lt_of_mem h
      (x, g sch, mapTypes f g rhs)
    .Let binds (mapTypes f g body) (f ty)
  | .Prod' l r ty         => .Prod' (mapTypes f g l) (mapTypes f g r) (f ty)
  | .Cond c t e ty        => .Cond (mapTypes f g c) (mapTypes f g t) (mapTypes f g e) (f ty)
  | .Match scr br ty ex rd =>
    let scr := scr.map (mapTypes f g)
    let br  := br.attach.map fun ⟨(ps, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd ps rhs
          <;> Array.sizeOf_lt_of_mem h
      (ps, mapTypes f g rhs)
    .Match scr br (f ty) ex rd
  | .Fix e ty             => .Fix (mapTypes f g e) (f ty)
termination_by fe => fe

partial def βReduce : FExpr -> FExpr
  | .TyApp f targ =>
    match βReduce f with
    | .TyLam a body =>
      let sub := {(a, targ)}
      βReduce (mapTypes (apply sub) (apply sub) body)
    | f => .TyApp f targ
  | .TyLam a b => .TyLam a (βReduce b)
  | .Proj src m i ty =>
    match βReduce src with
    | .TyApp s _ => βReduce (.Proj s m i ty)
    | .TyLam a s => βReduce (.TyLam a (.Proj s m i ty))
    | src => .Proj src m i ty
  | .App f a ty =>
    .App (βReduce f) (βReduce a) ty
  | .Fun p pTy b ty =>
    .Fun p pTy (βReduce b) ty
  | .Let bs body ty =>
    let bs := bs.map (fun (x, sch, rhs) => (x, sch, βReduce rhs))
    .Let bs (βReduce body) ty
  | .Prod' l r ty =>
    .Prod' (βReduce l) (βReduce r) ty
  | .Cond c t e ty =>
    .Cond (βReduce c) (βReduce t) (βReduce e) ty
  | .Match scr br ty ex rd =>
    let scr := scr.map βReduce
    let br  := br.map fun (ps, rhs) => (ps, βReduce rhs)
    .Match scr br ty ex rd
  | .Fix e ty =>
    .Fix (βReduce e) ty
  | e => e

def fvF : FExpr -> Std.TreeSet String
  | .CI _ _ | .CB _ _ | .CS _ _ | .CUnit _ => ∅
  | .Var x _ => {x}
  | .Fun p _ b _ => (fvF b).erase p
  | .App f a _ => fvF f ∪ fvF a
  | .TyLam _ b => fvF b
  | .TyApp f _ => fvF f
  | .Proj src _ _ _ => fvF src
  | .Let binds body _ =>
    let fvBinds := binds.attach.foldl (init := ∅) fun acc ⟨(x, sch, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd sch rhs
          <;> prod_sizeOf_lt_snd x (sch, rhs)
          <;> Array.sizeOf_lt_of_mem h
      acc ∪ fvF rhs
    fvBinds ∪ binds.foldl (·.erase ·.1) (fvF body)
  | .Prod' l r _ => fvF l ∪ fvF r
  | .Cond c t e _ => fvF c ∪ fvF t ∪ fvF e
  | .Match scr br _ _ _ =>
    let fvScr := scr.foldl (· ∪ fvF ·) ∅
    let fvBr  := br.attach.foldl (init := ∅) fun acc ⟨(ps, rhs), h⟩ =>
      have := prod_sizeOf_lt_snd ps rhs
          <;> Array.sizeOf_lt_of_mem h
      let bound := ps.flatMap pvs
      acc ∪ bound.foldl .erase (fvF rhs) -- .eraseMany bound
    fvScr ∪ fvBr
  | .Fix e _ => fvF e
termination_by fe => fe

partial def ηReduce : FExpr -> FExpr
  | .Fun p pTy b ty =>
    let b := ηReduce b
    if pTy.isTApp then
      if p ∉ fvF b then b
      else
        match b with
        | .App f (.Var x _) _ =>
          if x == p && p ∉ fvF f then
            ηReduce f
          else .Fun p pTy b ty
        | _ => .Fun p pTy b ty
    else
      .Fun p pTy b ty
  | .App f a ty        => .App (ηReduce f) (ηReduce a) ty
  | .TyLam a b         => .TyLam a (ηReduce b)
  | .TyApp f targ      => .TyApp (ηReduce f) targ
  | .Proj src m i ty   => .Proj (ηReduce src) m i ty
  | .Let bs body ty    =>
    let bs := bs.map fun (x, sch, rhs) => (x, sch, ηReduce rhs)
    .Let bs (ηReduce body) ty
  | .Prod' l r ty      => .Prod' (ηReduce l) (ηReduce r) ty
  | .Cond c t e ty     => .Cond (ηReduce c) (ηReduce t) (ηReduce e) ty
  | .Match scr br ty ex rd =>
    let scr := scr.map ηReduce
    let br  := br.map fun (ps, rhs) => (ps, ηReduce rhs)
    .Match scr br ty ex rd
  | .Fix e ty          => .Fix (ηReduce e) ty
  | other              => other

end Helper

def withMemoScope (act : F FExpr) : F FExpr := do
  let (memo, outer) <- modifyGet fun st@{memo, memoDepth,..} =>
    let outer := memoDepth == 0
    ((memo, outer), {st with memo := cond outer ∅ memo, memoDepth := memoDepth + 1})
  let r <- try act finally modify fun st' => {st' with memoDepth := st'.memoDepth - 1}
  if outer then
    -- nested scopes shared the memo. we place every synthesized dictionary
    -- once, at here. then restore the pre-scope memo.
    let {memo,..} <- modifyGet fun st' => (st', {st' with memo})
    let binds := memo.valuesArray.qsort (Nat.ble.on DictEntry.idx)
              |>.map fun d => (d.name, d.scheme, d.fe)
    if binds.isEmpty then pure r else pure $ place binds r
  else pure r
where place binds
  | .TyLam a b => .TyLam a (place binds b)
  | .Fix (.Fun self selfTy funChain _) fixTy =>
    let (params, core) := Helper.peelFun [] funChain
    let core := .Let binds core core.getTy
    let rebuilt := params.foldr (fun (n, ty) acc => .Fun n ty acc (ty ->' acc.getTy)) core
    let newSelfFun := .Fun self selfTy rebuilt (selfTy ->' rebuilt.getTy)
    .Fix newSelfFun fixTy
  | other => .Let binds other other.getTy

open Rewritable (apply applyS applyT applyP)
/--
stable renaming of MVs are now done before pretty-printer instead of at
normalization. Previsouly the raw ?mNs and greek renamed TVs are tangled up, now
internally it should be raw.

DeepSeek V4:
Now it's also scope aware: a binder displays with
its source name when that name is not taken in the enclosing scope, otherwise
GHC-style with a numeric subscript; binders without a source name fall back
to greek.
-/
structure RenameState where
  nxt      : Nat := 0
  /-- displayed binder names currently in scope -/
  taken    : Std.HashSet String := ∅
  /-- per-source-name subscript counter -/
  suffixes : Std.HashMap String Nat := ∅
  /-- every renamed binder's display name, for reuse at later occurrences
  (non-scoped: the scheme pass's renaming must match the term pass's) -/
  renamed  : Std.HashMap TV String := ∅

/-- the source name if free in the enclosing scope, else name + subscript -/
def freshDisplayName (st : RenameState) (tv : TV) (s : String) : RenameState × String :=
  if s ∈ st.taken then
    let k := st.suffixes.getD s 0 + 1
    let s' := s ++ k.toSubscriptString
    ({st with suffixes := st.suffixes.insert s k, taken := st.taken.insert s',
              renamed := st.renamed.insert tv s'}, s')
  else
    ({st with taken := st.taken.insert s, renamed := st.renamed.insert tv s}, s)

/-- the greek fallback for binders without a source name -/
def freshGreekName (st : RenameState) (tv : TV) : RenameState × TV :=
  let tv' := .named (gensym st.nxt)
  ({st with nxt := st.nxt + 1, taken := st.taken.insert tv'.toStr,
            renamed := st.renamed.insert tv tv'.toStr}, tv')

/-- rename binders with the display policy (user name when free, subscripted
when shadowed, greek otherwise), extending the subst -/
def renameBinders (stref : ST.Ref σ RenameState) (sub : Subst) (tvs : List TV)
  : ST σ (Subst × List TV) :=
  tvs.foldlM (init := (sub, [])) fun (sub, acc) tv => do
    let st <- stref.get
    match st.renamed[tv]? with
    | some s' => return (sub.insert tv (.TVar (.named s')), .named s' :: acc)
    | none =>
      match tv with
      | .mv _ (some s) =>
        let (st, s') := freshDisplayName st tv s
        stref.set st
        return (sub.insert tv (.TVar (.named s')), .named s' :: acc)
      | .mv _ none =>
        let (st, tv') := freshGreekName st tv
        stref.set st
        return (sub.insert tv (.TVar tv'), tv' :: acc)
      | _ => return (sub, tv :: acc)

mutual
/-- display-rename a type: substitutes via the subst and renames every forall
binder it meets, at any depth (nested rank-n foralls included) -/
partial def renameT (stref : ST.Ref σ RenameState) (sub : Subst) : MLType -> ST σ (Subst × MLType)
  | .TVar v => return (sub, apply sub (.TVar v))
  | t@(.TCon _) => return (sub, t)
  | a ->' b => do
    let (sub, a') <- renameT stref sub a
    let (sub, b') <- renameT stref sub b
    return (sub, a' ->' b')
  | a ×'' b => do
    let (sub, a') <- renameT stref sub a
    let (sub, b') <- renameT stref sub b
    return (sub, a' ×'' b')
  | .TApp h as => do
    let (sub, h') <- renameT stref sub h
    let (sub, as') <- as.foldlM (init := (sub, [])) fun (sub, acc) a => do
      let (sub, a') <- renameT stref sub a
      return (sub, a' :: acc)
    return (sub, .mkApp h' as'.reverse)
  | .TyLam x body => do
    let (sub', xs) <- renameBinders stref sub [x]
    let x' := xs.getD 0 x
    let (_, body') <- renameT stref sub' body
    return (sub, .TyLam x' body')
  | .TSch (.Forall tvs ps t) => do
    let (sub', tvs') <- renameBinders stref sub tvs
    let (sub', ps') <- ps.foldlM (init := (sub', [])) fun (sub, acc) p => do
      let (sub, p') <- renameP stref sub p
      return (sub, p' :: acc)
    let (_, t') <- renameT stref sub' t
    return (sub, .TSch (.Forall tvs'.reverse ps'.reverse t'))

partial def renameP (stref : ST.Ref σ RenameState) (sub : Subst) : Pred -> ST σ (Subst × Pred)
  | {cls, args} => do
    let (sub, args') <- args.foldlM (init := (sub, [])) fun (sub, acc) a => do
      let (sub, a') <- renameT stref sub a
      return (sub, a' :: acc)
    return (sub, Pred.mk cls args'.reverse)
end

def renameMVSchFrom (st : RenameState) (s : Scheme) : Scheme × Subst × RenameState :=
  runST fun σ => do
    let stref : ST.Ref σ RenameState <- ST.mkRef st
    let (sub, t) <- renameT stref ∅ (.TSch s)
    let sch := match t with | .TSch sch => sch | _ => unreachable!
    let st' <- stref.get
    return (sch, sub, st')

def renameMVSch (s : Scheme) : Scheme × Subst :=
  let (s, sub, _) := renameMVSchFrom {} s
  (s, sub)

partial def applyFE (st₀ : RenameState) (sub : Subst) (fe : FExpr) : FExpr :=
  runST fun σ => do
    let stref : ST.Ref σ RenameState <- ST.mkRef st₀
    go stref sub fe
where
  renT {σ} (stref : ST.Ref σ RenameState) (sub : Subst) (ty : MLType) : ST σ MLType := Prod.snd <$> renameT stref sub ty
  go {σ} (stref : ST.Ref σ RenameState) (sub : Subst) : FExpr -> ST σ FExpr
  | .CI i ty => .CI i <$> renT stref sub ty
  | .CS s ty => .CS s <$> renT stref sub ty
  | .CB b ty => .CB b <$> renT stref sub ty
  | .CUnit ty => .CUnit <$> renT stref sub ty
  | .Var x ty => .Var x <$> renT stref sub ty
  | .Fun p pTy body ty => .Fun p <$> renT stref sub pTy <*> go stref sub body <*> renT stref sub ty
  | .App f a ty => .App <$> go stref sub f <*> go stref sub a <*> renT stref sub ty
  | .TyLam a body => do
    let res := Helper.peelTyLamTV [a] body
    let (sub', tvs') <- renameBinders stref sub res.1
    let inner <- go stref sub res.2
    Helper.wrapTyLams tvs'.reverse <$> go stref sub' inner
  | .TyApp f arg => .TyApp <$> go stref sub f <*> renT stref sub arg
  | .Let binds body ty => do
    let binds <- binds.mapM fun (n, sch, fe) => do
      let st <- stref.get
      let (sch, sub', st') := renameMVSchFrom st sch
      stref.set st'
      let fe' <- go stref (sub' ∪' sub) fe
      return (n, apply sub sch, fe')
    .Let binds <$> go stref sub body <*> renT stref sub ty
  | .Prod' l r ty => .Prod' <$> go stref sub l <*> go stref sub r <*> renT stref sub ty
  | .Cond c t e ty => .Cond <$> go stref sub c <*> go stref sub t <*> go stref sub e <*> renT stref sub ty
  | .Match discr branches resTy ex rd =>
    .Match <$> discr.mapM (go stref sub)
      <*> branches.mapM (fun (pats, e) => (pats, ·) <$> go stref sub e)
      <*> renT stref sub resTy <*> pure ex <*> pure rd
  | .Fix e ty => .Fix <$> go stref sub e <*> renT stref sub ty
  | .Proj src mname idx ty => .Proj <$> go stref sub src <*> pure mname <*> pure idx <*> renT stref sub ty

local instance : Std.ToFormat Pattern where
  format := .text ∘ Pattern.toStr
open Std Std.Format in
partial def FExpr.unexpand : FExpr -> Format
  | .CI i _ | .CB i _ | .CS i _ => repr i
  | .CUnit _ => format ()
  | .App f a@(.App ..) _ => fill $ parenL? f ++ (indentD (parenR? a))
  | .App f a _ => fill $ parenL? f ++ indentD (unexpand a)
  | .Proj src mname i _ => parenL? src ++ sbracket (format i ++ "," <> format mname)
  | .Cond c t e _ => group $
    "if" <> unexpand c <+> "then" ++ indentD (unexpand t)
    <+> "else" ++ indentD (unexpand e)
  | .Fix e _ => "rec" <> unexpand e
  | .Var x _ => format x
  | .Prod' p q _ => bracket "⟨" (unexpand p ++ "," <+> unexpand q) "⟩"
  | .Fun param pTy body _ =>
    fill $ "fun" <> param ++ indentD (":" <> pTy.renderFmt <> "=>" <+> unexpand body)
  | .Match discr branches .. =>
    let discr := discr.map unexpand
    let br := branches.map fun (pats, e) =>
      group $ "|" <> joinSep' pats ("," ++ line) <> "=>" ++ indentD (unexpand e)
    group $ "match" <> joinSep' discr ("," ++ line) <> "with" ++ "\n" ++ joinSep' br "\n"
  | .Let binds body _ =>
    let (binds, recflag) := binds.foldl (init := (#[], false)) fun (acc, recflag) (id, sch, fe) =>
      match fe with
      | .Fix (.Fun _ _ body _) _ =>
        (acc.push $ fill $ id ++ indentD (":" <> sch.renderFmt <> "=" <+> unexpand body), true)
      | _ =>
        (acc.push $ fill $ id ++ indentD (":" <> sch.renderFmt <> "=" <+> unexpand fe), recflag)
    let recStr := if recflag then .text " rec " else .text " "
    group $ "let" ++ recStr ++ joinSep' binds (line ++ "and ") <+> "in" <>
      match body with
      | .Fun .. => unexpand body
      | _ => nest 3 $ unexpand body
  | .TyLam a body =>
    let (tvs, body) := Helper.peelTyLam [a.elimStr] body
    group $ "Λ" <> joinSep tvs " " ++ "." ++ indentD (unexpand body)
  | .TyApp f ty => parenL? f ++ "@" ++ parenT ty
where
parenR?
  | p@(.App ..) | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
  | p => unexpand p
parenL?
  | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
  | p => unexpand p
parenT
  | t@(TVar _) | t@(TCon _) | t@(TApp _ []) => t.renderFmt
  | t => paren t.renderFmt
