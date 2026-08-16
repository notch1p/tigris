import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.constraint
import Tigris.typing.resolve
import Tigris.typing.kinds

def String.isSkolemOf (h : String) (v : TV) : Bool :=
  let h' := Substring.Raw.mk h ⟨4⟩ h.rawEndPos
  let v := v.toStr.toRawSubstring
  h.startsWith "?sk." && h' == v

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
open ConstraintInfer (unify)
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

def αRename (qs : List TV) : Subst × List TV :=
  let mkFresh : TV -> Nat -> TV
    | _, i => .mkTV s!"?inst.{i}"
  qs.foldrIdx (init := (∅, [])) fun i q (sub, acc) =>
    let q' := mkFresh q i
    (sub.insert q (.TVar q'), q' :: acc)

def instantiateArgs (qs : List TV) (ctx : List Pred) (schemeBody instTy : MLType)
  : F (List MLType × Subst × List Pred) := do
  if qs.isEmpty then return ([], ∅, ctx)
  let (rn, qs) := αRename qs
  let schemeBody := apply rn schemeBody
  let ctx := apply rn ctx

  let ke <- get <&> (·.ke)
  let (sub, ke) <- unify ke (monoOfTSch schemeBody) (monoOfTSch instTy)
  modify fun st => {st with ke := ke}
  return (qs.map (fun a => apply sub (TVar a)), sub, apply sub ctx |>.map Helper.normHKPred)

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e
@[inline] def mkApp (f a : FExpr) : FExpr :=
  .App f a $ match f.getTy with | _ ->' b => b | other => other

partial def eqSkolem : MLType -> MLType -> Bool
  | .TVar v, .TVar w => v == w
  | .TVar v, .TCon h | .TCon h, .TVar v => h.isSkolemOf v
  | .TApp h₁ as₁, .TApp h₂ as₂ =>
    eqSkolem h₁ h₂
    && as₁.length == as₂.length
    && List.all2 eqSkolem as₁ as₂
  | .TyLam x b₁, .TyLam y b₂ => x == y && eqSkolem b₁ b₂
  | t₁ ->' t₂, u₁ ->' u₂ | t₁ ×'' t₂, u₁ ×'' u₂ => eqSkolem t₁ u₁ && eqSkolem t₂ u₂
  | .TCon a, .TCon b => a == b
  | _, _ => false

def mv? : TV -> Lean.Name
  | .mkTV s =>
    if s.startsWith "?m" then `Amb
    else if s.startsWith "?i" then `CAmb
    else `d

@[inline] def isHKVarTV : TV -> Bool
  | .mkTV s => s.isLowerInit

def predEqSkolem (templ goal : Pred) : Bool :=
  templ.cls == goal.cls
  && templ.args.length == goal.args.length
  && List.all2 eqSkolem templ.args goal.args

-- linear search, scope is usually tiny.
def lookupDictVar (scope : DictScope) (goal : Pred) : Option (String × MLType) :=
  go scope where
  go
  | [] => none
  | (templ, v) :: xs =>
    if predEqSkolem templ goal /- || predEqGoal templ goal -/ then some (v, dictTypeOfPred templ)
    else go xs

@[inline] def isGroundPred (p : Pred) : Bool :=
  (fv p.args).isEmpty

@[inline] def patOfIdx (ctor : Symbol) (idx : Nat) (sz : Nat) : Pattern :=
  .PCtor ctor $ Array.replicate sz .PWild |>.set! idx (.PVar s!"m_{ctor}_{idx}")

def mvs (p : Pred) : (List TV × List TV) :=
  let vs := fv p.args
  vs.foldl
    (fun (mv, iv) tv =>
      match mv? tv with
      | `Amb => (tv :: mv, iv)
      | `CAmb => (mv, tv :: iv)
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
  | .TyLam (.mkTV p) b => peelTyLam (p :: acc) b
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

partial def mapTypes (f : MLType -> MLType) (g : Scheme -> Scheme := id) : FExpr -> FExpr
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
    let binds := binds.map fun (x, sch, rhs) => (x, g sch, mapTypes f g rhs)
    .Let binds (mapTypes f g body) (f ty)
  | .Prod' l r ty         => .Prod' (mapTypes f g l) (mapTypes f g r) (f ty)
  | .Cond c t e ty        => .Cond (mapTypes f g c) (mapTypes f g t) (mapTypes f g e) (f ty)
  | .Match scr br ty ex rd =>
    let scr := scr.map (mapTypes f g)
    let br  := br.map fun (ps, rhs) => (ps, mapTypes f g rhs)
    .Match scr br (f ty) ex rd
  | .Fix e ty             => .Fix (mapTypes f g e) (f ty)

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

partial def fvF : FExpr -> Std.TreeSet String
  | .CI _ _ | .CB _ _ | .CS _ _ | .CUnit _ => ∅
  | .Var x _ => {x}
  | .Fun p _ b _ => (fvF b).erase p
  | .App f a _ => fvF f ∪ fvF a
  | .TyLam _ b => fvF b
  | .TyApp f _ => fvF f
  | .Proj src _ _ _ => fvF src
  | .Let binds body _ =>
    let fvBinds := binds.foldl (init := ∅) fun acc (_, _, rhs) => acc ∪ fvF rhs
    fvBinds ∪ binds.foldl (·.erase ·.1) (fvF body)
  | .Prod' l r _ => fvF l ∪ fvF r
  | .Cond c t e _ => fvF c ∪ fvF t ∪ fvF e
  | .Match scr br _ _ _ =>
    let fvScr := scr.foldl (· ∪ fvF ·) ∅
    let fvBr  := br.foldl (init := ∅) fun acc (ps, rhs) =>
      let bound := ps.flatMap pvs
      acc ∪ bound.foldl .erase (fvF rhs) -- .eraseMany bound
    fvScr ∪ fvBr
  | .Fix e _ => fvF e

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
-/
def renameMVSch : Scheme -> Scheme × Subst
  | .Forall tvs ps body =>
    let (sub, tvs') := tvs.foldlIdx (init := (∅, [])) fun i (sub, acc) tv =>
      if tv.toStr.startsWith "?m." then
        let tv' := .mkTV (gensym i)
        (sub.insert tv (.TVar tv'), tv' :: acc)
      else (sub, tv :: acc)
    let rec renameBody
      | .TSch inner =>
        let (inner, _) := renameMVSch inner
        apply sub (.TSch inner)
      | t => apply sub t
    (.Forall tvs'.reverse (ps.map (applyP sub)) (renameBody body), sub)

partial def applyFE (sub : Subst) : FExpr -> FExpr
  | .CI i ty => .CI i (apply sub ty)
  | .CS s ty => .CS s (apply sub ty)
  | .CB b ty => .CB b (apply sub ty)
  | .CUnit ty => .CUnit (apply sub ty)
  | .Var x ty => .Var x (apply sub ty)
  | .Fun p pTy body ty => .Fun p (apply sub pTy) (applyFE sub body) (apply sub ty)
  | .App f a ty => .App (applyFE sub f) (applyFE sub a) (apply sub ty)
  | .TyLam a body =>
    let res := Helper.peelTyLamTV [a] body
    let (sub', tvs') := res.1.foldlIdx (init := (∅, [])) fun i (sub, acc) tv =>
      if tv.toStr.startsWith "?m." then
        let tv' := .mkTV (gensym i)
        (sub.insert tv (.TVar tv'), tv' :: acc)
      else (sub, tv :: acc)
    Helper.wrapTyLams tvs'.reverse $ applyFE sub' $ applyFE sub res.2
  | .TyApp f arg => .TyApp (applyFE sub f) (apply sub arg)
  | .Let binds body ty =>
    let binds := binds.map fun (n, sch, fe) =>
      let (sch, sub') := renameMVSch sch
      (n, apply sub sch, applyFE (sub' ∪' sub) fe)
    .Let binds (applyFE sub body) (apply sub ty)
  | .Prod' l r ty => .Prod' (applyFE sub l) (applyFE sub r) (apply sub ty)
  | .Cond c t e ty => .Cond (applyFE sub c) (applyFE sub t) (applyFE sub e) (apply sub ty)
  | .Match discr branches resTy ex rd =>
    .Match (discr.map (applyFE sub))
      (branches.map fun (pats, e) => (pats, applyFE sub e))
      (apply sub resTy) ex rd
  | .Fix e ty => .Fix (applyFE sub e) (apply sub ty)
  | .Proj src mname idx ty => .Proj (applyFE sub src) mname idx (apply sub ty)

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
