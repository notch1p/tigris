import Tigris.typing.ttypes
import Tigris.typing.tsyntax
import Tigris.typing.constraint
import Tigris.typing.resolve

def String.isSkolemOf (h : String) (v : TV) : Bool :=
  let h' := Substring.mk h ⟨4⟩ h.endPos
  let v := v.toStr.toSubstring
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
deriving Repr, Inhabited

def FExpr.getTy
  | CI _ ty | CS _ ty | CB _ ty | CUnit ty
  | Var _ ty | Fun _ _ _ ty | App _ _ ty
  | Let _ _ ty | Prod' _ _ ty | Cond _ _ _ ty
  | Match _ _ ty _ _ | Fix _ ty | Proj _ _ _ ty => ty
  | TyLam _ f
  | TyApp f _ => f.getTy
    -- TyApp currently doesn't carry result type.
    -- f.getTy should NOT yield a arrow type as polys are erased after instantiation

namespace SysF open MLType TExpr Rewritable
open ConstraintInfer (unify)
open Resolve (resolvePred)

abbrev FEnv := Std.TreeMap String Scheme
abbrev DictScope := List (Pred × String)  -- predicate template + dict variable name

structure FState where
  log    : Logger := ""
  memo   : Std.HashMap Pred (String × Scheme × FExpr) := ∅
  gensym : Nat := 0
deriving Inhabited

abbrev F := EStateM TypingError FState
abbrev Blocked := Std.HashSet String

@[inline] def logAppend (s : String) : F Unit :=
  modify fun st => {st with log := st.log ++ s}

@[inline] def fresh (pfx := "_rd") : F String :=
  modifyGet fun st => (pfx ++ toString st.gensym, {st with gensym := st.gensym + 1})

@[inline] def memoLookup (p : Pred) : F (Option (String × Scheme × FExpr)) :=
  get <&> (·.memo[p]?)

@[inline] def memoInsert (p : Pred) (entry : String × Scheme × FExpr) : F Unit :=
  modify fun st => {st with memo := st.memo.insert p entry}

instance : MonadLift (Except TypingError) F where
  monadLift
  | .error e => throw e
  | .ok res => return res

namespace Helper

@[inline] def dictTypeOfPred : Pred -> MLType
  | {cls, args,..} => TApp cls args

@[inline] def monoOfTSch : MLType -> MLType
  | .TSch (.Forall _ _ t) => t
  | t => t

def αRename (qs : List TV) : Subst × List TV :=
  let mkFresh : TV -> Nat -> TV
    | _, i => .mkTV s!"?inst{i}"
  qs.foldrIdx (init := (∅, [])) fun i q (sub, acc) => 
    let q' := mkFresh q i
    (sub.insert q (.TVar q'), q' :: acc)

def instantiateArgs (qs : List TV) (ctx : List Pred) (schemeBody instTy : MLType)
  : F (List MLType × Subst × List Pred) := do
  if qs.isEmpty then return ([], ∅, ctx)
  let (rn, qs) := αRename qs
  let schemeBody := apply rn schemeBody
  let ctx := apply rn ctx

  let sub <- unify (monoOfTSch schemeBody) (monoOfTSch instTy)
  return (qs.map (fun a => apply sub (TVar a)), sub, apply sub ctx |>.map Helper.normHKPred)

@[inline] def wrapTyLams (qs : List TV) (e : FExpr) : FExpr := qs.foldr .TyLam e
@[inline] def mkApp (f a : FExpr) : FExpr :=
  .App f a $ match f.getTy with | _ ->' b => b | other => other

partial def eqSkolem : MLType -> MLType -> Bool
  | .TVar v, .TVar w => v == w
  | .TVar v, .TCon h => h.isSkolemOf v
  | .KApp v asT, .KApp w asG
  | .TApp v asT, .TApp w asG =>
    v == w 
    && asT.length == asG.length
    && List.all2 eqSkolem asT asG
  | .KApp v asT, .TApp h asG | .TApp h asG, .KApp v asT =>
    h.isSkolemOf v || h.isLowerInit && toString v == h
    && asT.length == asG.length
    && List.all2 eqSkolem asT asG
  | t₁ ->' t₂, u₁ ->' u₂ | t₁ ×'' t₂, u₁ ×'' u₂ => eqSkolem t₁ u₁ && eqSkolem t₂ u₂
  | .TCon a, .TCon b => a == b
  | _, _ => false

def mv? : TV -> Bool
  | .mkTV s => s.startsWith "?"

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

def mvs (p : Pred) : List TV :=
  let vs := fv p.args
  vs.foldl (fun a tv => if mv? tv then tv :: a else a) []

def stuckMessage (p : Pred) (method : String) : TypingError :=
  let metas := mvs p
  let metaS := if metas.isEmpty then ""
  else
    s!"{p}: typeclass elaboration is stuck because of metavariable(s)\n  \
       {toString metas}\n\
       induced by a call to {method}. Consider adding type ascriptions.\n"
  let base := s!"{p}: missing in-scope instance for method {method}\n"
  if metas.isEmpty then .NoSynthesize base
  else .Ambiguous metaS

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

def withMemoScope (act : F FExpr) : F FExpr := fun st =>
  match act {st with memo := ∅} with
  | .error e st => .error e st
  | .ok e st' =>
    let binds := st'.memo.valuesArray.qsort (strLE.on Prod.fst)
    let st := {st' with memo := st.memo}
    if binds.isEmpty then .ok e st
    else .ok (place binds e) st where
place binds
  | .TyLam a b => .TyLam a (place binds b)
  | .Fix (.Fun self selfTy funChain _) fixTy =>
    let (params, core) := Helper.peelFun [] funChain
    let core := .Let binds core core.getTy
    let rebuilt := params.foldr (fun (n, ty) acc => .Fun n ty acc (ty ->' acc.getTy)) core
    let newSelfFun := .Fun self selfTy rebuilt (selfTy ->' rebuilt.getTy)
    .Fix newSelfFun fixTy
  | other => .Let binds other other.getTy

local instance : Std.ToFormat Pattern where
  format := .text ∘ Pattern.toStr
open Std Std.Format in
partial def FExpr.unexpand : FExpr -> Format
  | .CI i _ | .CB i _ | .CS i _ => repr i
  | .CUnit _ => format ()
  | .App f a _ => parenL? f ++ group (indentD (parenR? a))
  | .Proj src mname i _ => parenL? src ++ sbracket (format i ++ ", " ++ format mname)
  | .Cond c t e _ =>
    "if" <> unexpand c <+> "then" ++ indentD (unexpand t)
    <+> "else" ++ indentD (unexpand e)
  | .Fix e _ => "rec" <> unexpand e
  | .Var x _ => format x
  | .Prod' p q _ => paren $ unexpand p <> "," <> unexpand q
  | .Fun param pTy body _ =>
    group $ "fun" <> param <> ":" <> pTy.toStr <> "=>" ++ group (indentD (unexpand body))
  | .Match discr branches .. =>
    let discr := discr.map unexpand
    let br := branches.map fun (pats, e) =>
      "|" <> joinSep' pats ", " <> "=>" ++ group (indentD (unexpand e))
    group $ "match" <> joinSep' discr ", " <> "with" <+> joinSep' br line
  | .Let binds body _ =>
    let (binds, recflag) := binds.foldl (init := (#[], false)) fun (acc, recflag) (id, sch, fe) =>
      match fe with
      | .Fix (.Fun _ _ body _) _ =>
        (acc.push $ id <> ":" <> toString sch <> group ("=" ++ indentD (unexpand body)), true)
      | _ =>
        (acc.push $ id <> ":" <> toString sch <> group ("=" ++ indentD (unexpand fe)), recflag)
    let recStr := if recflag then .text " rec " else .text " "
    "let" ++ recStr ++ joinSep' binds (line ++ "and ") <+> "in" <> unexpand body
  | .TyLam a body =>
    let (tvs, body) := Helper.peelTyLam [a.elimStr] body
    group $ paren $ "Λ" <> joinSep tvs " " ++ "." ++ indentD (unexpand body)
  | .TyApp f ty => parenL? f ++ "@" ++ parenT ty
where 
parenR?
  | p@(.App ..) | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
  | p => unexpand p
parenL?
  | p@(.Fun ..) | p@(.Cond ..) | p@(.Let ..) | p@(.Match ..) => paren (unexpand p)
  | p => unexpand p
parenT
  | t@(TVar _) | t@(TCon _) | t@(TApp _ []) | t@(KApp _ []) => text t.toStr
  | t => paren t.toStr
