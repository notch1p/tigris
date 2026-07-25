import Tigris.TCNF.nf
import Tigris.oldcore2.matchAppF


/-!
# TCNF Lambda Lifting (CC) Pass

local functions becomes one top-level `Decl` per member, and the definition site is
replaced by a flat closure `LetValue.mkClos`, denoted 𝐂⟦code, env,*⟧.

Compared to the previous design which uses 𝐂, 𝐄 to encode code pointers/captured scope,
we adopt a simpler design here.

- Closure.
  refers to a set of free variables ("fvar" is used exclusively for FVarId)
  captured by a function. Closure is flat and stored inline, without a 𝐄 indirection.
  fvars are _reused_ as the lifted decl's leading parameters,
  allowing the lifted params to shadow-match the captured ids.

- Recursion.
  a group member (or self, if self recursion) referenced inside a lifted body is
  _rebuilt_ there from the shared env, (re)using the fvar.
  The enclosing site binds the same closures.

- Join points.
  retains as we do not see them as functions, irrelevant to lambda lifting.

We use externNames to exclude globals from envs.
-/

namespace TCNF.CC open FExpr IRf

abbrev FVSet := Std.HashSet FVarId

/-! {x}, {(k, v), (k', v'), ·} is valid syntax for set/map respectively. -/

def fvAtom (bound : FVSet) : Atom -> FVSet
  | .fvar x => if x ∈ bound then ∅ else {x}
  | _ => ∅

def fvAtoms (bound : FVSet) (as : Array Atom) : FVSet :=
  as.foldl (· ∪ fvAtom bound ·) ∅

def fvValue (bound : FVSet) : LetValue .postCC -> FVSet
  | .lit _          => ∅
  | .pair p q       => fvAtom bound p ∪ fvAtom bound q
  | .proj _ s
  | .field _ _ s    => fvAtom bound $ .fvar s
  | .ctor _ as
  | .prim _ as
  | .extern _ as    => fvAtoms bound as
  | .app h as
  | .pap h as       => fvAtom bound (.fvar h) ∪ fvAtoms bound as
  | .isCtor s _ _   => fvAtom bound (.fvar s)
  -- `code` is a lifted decl, never captured
  | .mkClos _ env _ => fvAtoms bound env

mutual
def fvCode (bound : FVSet) : CodePost -> FVSet
  | .let d k         => fvValue bound d.value ∪ fvCode (bound.insert d.fvarId) k
  | .jp d k          => fvFun bound d ∪ fvCode (bound.insert d.fvarId) k
  | .jmp j as        => fvAtom bound (.fvar j) ∪ fvAtoms bound as
  | .cases dc _ alts => alts.foldl (· ∪ fvAlt bound ·) $ fvAtom bound $ .fvar dc
  | .ret v           => fvAtom bound v
  | .unreach _       => ∅
--  | .fun _ _ h       => nomatch h
def fvFun (bound : FVSet) : FunDecl .postCC -> FVSet
  | {params, body, ..} => fvCode (params.foldl (·.insert ·.fvarId) bound) body
def fvAlt (bound : FVSet) : Alt .postCC -> FVSet
  | .ctor _ ps k => fvCode (ps.foldl (·.insert ·.fvarId) bound) k
  | .const _ k
  | .default k   => fvCode bound k
end

structure CCCtx where
  /-- never captured. -/
  globals : FVSet
  /-- in-scope binders for env parameter names/types. -/
  scope   : Std.HashMap FVarId (String × MLType) := ∅

abbrev CCM := ReaderT CCCtx
                        /-      results      -/
            $ StateRefT (Array (Decl .postCC)) CompilerM

@[inline] def withBinder (fv : FVarId) (nm : String) (ty : MLType) (x : CCM α) : CCM α :=
  withReader (x := x) fun c => {c with scope := c.scope.insert fv (nm, ty)}

@[inline] def withBinders (ps : Array Param) (x : CCM α) : CCM α :=
  withReader (x := x) fun c =>
    {c with scope :=
      ps.foldl (fun m {fvarId, binderName, ty} => m.insert fvarId (binderName, ty)) c.scope}

def gatherFuns : CodePre -> List (FunDecl .preCC) × CodePre
  | .fun d k _ =>
    let (ds, r) := gatherFuns k
    (d :: ds, r)
  | c => ([], c)


@[inline, always_inline]
unsafe def coerceCC : LetValue .preCC -> LetValue .postCC := unsafeCast
/--
  this coercion has realistically no cost
  as it is implemented by unsafeCast, which is a no-op in Lean.
-/
@[implemented_by coerceCC] def ccValue : LetValue .preCC -> LetValue .postCC
  | .lit k        => .lit k
  | .pair p q     => .pair p q
  | .proj i s     => .proj i s
  | .field c i s  => .field c i s
  | .ctor t as    => .ctor t as
  | .prim op as   => .prim op as
  | .extern nm as => .extern nm as
  | .app h as     => .app h as
  | .pap h as     => .pap h as
  | .isCtor s t a => .isCtor s t a
  | .mkClos _ _ h => Phase.noConfusion h -- False

mutual
partial def ccCode : CodePre -> CCM (CodePost)
  | .let d k => do
    let v := ccValue d.value
    let k <- withBinder d.fvarId d.binderName d.ty (ccCode k)
    return .let ⟨d.fvarId, d.binderName, d.ty, v⟩ k
  | .fun d k _ =>
    let (funs, rest) := gatherFuns k
    ccFunGroup (d :: funs).toArray rest
  | .jp d k => do
    let body <- withBinders d.params (ccCode d.body)
    let k <- withBinder d.fvarId d.binderName d.ty (ccCode k)
    return .jp ⟨d.fvarId, d.binderName, d.params, d.ty, body⟩ k
  | .cases dc ty alts => .cases dc ty <$> alts.mapM ccAlt
  | .jmp j as   => return .jmp j as
  | .ret v      => return .ret v
  | .unreach ty => return .unreach ty

partial def ccAlt : Alt .preCC -> CCM (Alt .postCC)
  | .ctor t ps k => (Alt.ctor t ps ·) <$> withBinders ps (ccCode k)
  | .const c k   => (Alt.const c ·) <$> ccCode k
  | .default k   => (Alt.default ·) <$> ccCode k

/-- Lift a run of (mutually recursive) funs to top-level decls; replace their
definition site with flat closures. -/
partial def ccFunGroup (funs : Array (FunDecl .preCC)) (rest : CodePre) : CCM (CodePost) := do
  let {globals, scope := outerScope} <- read
  -- fresh code pointer per member
  let mut codeIds := #[]
  let mut bodies  := #[]

  for d in funs do
    codeIds <- codeIds.push <$> fresh
    bodies  <- bodies.push <$> withBinders d.params (ccCode d.body)

  let G : FVSet := funs.foldl (·.insert ·.fvarId) ∅
  -- convert each body with its own params in scope
  let rawFVs := Array.zipWith (as := funs) (bs := bodies)
    fun d b => fvCode (d.params.foldl (·.insert ·.fvarId) ∅) b
  -- shared captured env = union of members' free vars \ group \ globals
  let E := rawFVs.foldl Std.HashSet.union ∅ |>.fold (init := (∅ : FVSet)) fun s x =>
    if G.contains x || globals.contains x then s else s.insert x

  let mut Eparams := #[]
  let mut Eatoms  := #[]
  let mut Etys    := #[]

  for e in E do
    let (nm, ty) := outerScope[e]?.getD ("env", dummyTy)
    Eparams := Eparams.push $ Param.mk e nm ty
    Etys    := Etys.push ty
    Eatoms  := Eatoms.push $ Atom.fvar e

  for d in funs, code in codeIds, body in bodies, rawFV in rawFVs do
    -- emit one lifted decl per member
    -- rebuild referenced group members (self / mutual) from the env params
    let liftedBody :=
      Array.foldr2 (init := body) (xs := funs) (ys := codeIds) fun dj cj acc =>
        if rawFV.contains dj.fvarId
        then .let ⟨dj.fvarId, dj.binderName, dj.ty, .mkClos cj Eatoms⟩ acc
        else acc
    let params    := Eparams ++ d.params
    let liftedTy  := Etys.foldr (· ->' ·) d.ty
    let recursive := funs.foldl (fun b dj => b || rawFV.contains dj.fvarId) false
    setArity code params.size
    modify (·.push { fvarId := code
                   , name   := d.binderName
                   , params
                   , ty     := liftedTy
                   , body   := liftedBody
                   , arity  := params.size
                   , recursive})

  -- continue, with the group members bound as closures in the enclosing scope
  let groupParams := funs.map fun d => Param.mk d.fvarId d.binderName d.ty
  let rest' <- withBinders groupParams (ccCode rest)

  return Array.foldr2 (init := rest') (xs := funs) (ys := codeIds) fun d code acc =>
    .let ⟨d.fvarId, d.binderName, d.ty, .mkClos code Eatoms⟩ acc
end

def ccDecl (d : Decl .preCC) : CCM (Decl .postCC) := do
  let scope₀ := d.params.foldl (fun m {fvarId, binderName, ty} => m.insert fvarId (binderName, ty)) ∅
  let body' <- withReader (fun c => {c with scope := scope₀}) (ccCode d.body)
  return {d with body := body'}

end CC
