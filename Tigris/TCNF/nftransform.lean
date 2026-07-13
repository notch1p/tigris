import Tigris.interpreter.entrypoint
import Tigris.TCNF.nflift

/-!
# TCNF lowering (preCC)

Lowers a `FExpr` into `Code .preCC`.

- Continuations.
  A branch shares its continuation as a join point (`withJoin`)
  instead of duplicating it; in tail position (`.ret`) or when
  the continuation is already a `.jmp`, no join point is allocated.

- N-ary application.
  syntactic arity refers to a head's consecutive `Fun`s (from NFState.arity);
  type arity refers to a head's arrow type count.

  see also `emitApp`.

- Ctor application.
  partially applied ctor is η-expanded to a function wrapper.

  It's worth noting that this η-expansion is dumb in the sense it duplicates
  wrapper for each partial application of the same ctor.

- Decision tree-based case analysis compilation.
  reuses matchAppF module; the decision tree lowers to `cases` whose ctor
  alternatives _bind the fields as params_, threaded through a `Sel -> FVarId`
  hashmap with a `proj` fallback. The success continuation and the fail path are
  each materialized once (join points).

  Note that complete pattern matrices have their fallback marked as unreachable (`Code.unreach`)

- Reserved ids / externals.
  refers to primitives/external decls/runtime builtins.

  0 is reserved for the runtime match-failure builtin;
-/

namespace TCNF.Compiler open FExpr IRf
abbrev FVarEnv   := Lean.Data.Trie FVarId

/-- intern a stable fvar for a free name.
    used for runtime builtin or unresolved global -/
def internExtern (x : String) : CompilerM FVarId :=
  modifyGet fun s@{externs, externNames, nextId, ..} =>
    if let some v := externs[x]? then (v, s)
    else
      let nextId      := nextId + 1
      let externs     := externs.insert x nextId
      let externNames := externNames.insert nextId x
      (nextId, {s with nextId, externs, externNames, h := by omega})

/-- `let name#(fvar <- fresh) : ty := value in kont fvar` -/
@[inline] def bindLet (name : String) (ty : MLType) (value : LetValue .preCC)
  (kont : FVarId -> CompilerM CodePre) : CompilerM CodePre :=
  fresh >>= fun fv => .let ⟨fv, name, ty, value⟩ <$> kont fv

section Helper
def arrArity : MLType -> Nat
  | .TSch (.Forall _ _ t) => arrArity t
  | _ ->' b => 1 + arrArity b
  | _ => 0

def peelArrows : Nat -> MLType -> MLType
  | 0, t => t
  | n + 1, .TSch (.Forall _ _ t) => peelArrows n.succ t
  | n + 1, _ ->' b => peelArrows n b
  | _ + 1, t => t

/-- Peel a curried lambda chain into its params (with types) and core body. -/
def peelLam : FExpr -> List (String × MLType) × FExpr
  | .Fun p pty b _ => let (ps, c) := peelLam b; ((p, pty) :: ps, c)
  | e => ([], e)

def decomposeApp : FExpr -> FExpr × Array FExpr
  | .App f a _ => let (h, as) := decomposeApp f; (h, as.push a)
  | e => (e, #[])

def primOfName : String -> Option PrimOp
  | "add"        => some .add
  | "sub"        => some .sub
  | "mul"        => some .mul
  | "div"        => some .div
  | "__eqInt"    => some .eqInt
  | "__eqBool"   => some .eqBool
  | "__eqString" => some .eqStr
  | _            => none

def matchBinaryPrim : FExpr -> Option (PrimOp × FExpr × FExpr)
  | .App (.App (.Var f _) x _) y _   => (·, x, y) <$> primOfName f
  | .App (.Var f _) (.Prod' x y _) _ => (·, x, y) <$> primOfName f
  | _ => none

def matchCtorApp (ctors : Std.HashMap String Nat) (e : FExpr)
  : Option (String × Array FExpr × Nat) :=
  match decomposeApp e with
  | (.Var cname _, args) => ctors[cname]? |>.map fun ar => (cname, args, ar)
  | _ => none

def isRecBind : FExpr -> Bool
  | .Fix (.Fun ..) _ => true
  | _ => false

/-- should be more efficient than xs[0:i] ++ ys ++ xs[i + 1:] -/
@[inline] def replaceCol (xs : Array α) (i : Nat) (ys : Array α) : Array α :=
  xs[i + 1:].foldl Array.push $ ys.foldl Array.push xs[0:i].copy
end Helper



def Sel.beq : Sel -> Sel -> Bool
  | .base i,    .base j    => i == j
  | .field s i, .field t j => i == j && Sel.beq s t
  | _, _ => false
instance : BEq Sel := ⟨Sel.beq⟩

/-- projection path |-> (respective fvar, its type) -/
abbrev SelMap := Std.HashMap Sel (FVarId × MLType)

/-- monotype recorded for a projection path -/
def selTyOf (sel : Sel) (m : SelMap) : MLType := m[sel]?.map (·.2) |>.getD dummyTy

/-- Instantiate a ctor's param types at the scrutinee's type args -/
def instCtorFields (cname : String) (ar : Nat) (scrutTy : MLType) : CompilerM (Array MLType) := do
  let s <- get
  match s.fieldTys[cname]? with
  | none => return Array.replicate ar dummyTy
  | some declared =>
    let params      := s.ctorTyParams[cname]?.getD []
    let tyArgs      := match scrutTy with | .TApp _ as => as | _ => []
    let sub : Subst := List.foldl2 Std.TreeMap.insert ∅ params tyArgs
    return declared.map $ Rewritable.applyT sub

/-- The sole constructor of a single-ctor type. used for record/dictionary -/
def soleCtorOf (ty : MLType) : CompilerM String := do
  let {tyDecl,..} <- get
  return tyDecl[tycon]?.bind (·.ctors[0]?)
      |>.elim tycon Prod.fst
where tycon := match unwrapTSch ty with
  | .TApp (.TCon c) _ | .TCon c => c
  | _ => ""

/-- Resolve a `Sel` to a variable, emitting projections for any
resolved prefix, that is, fallback as ctor fields / pair splits are usually pre-bound -/
def resolveSel (sel : Sel) (roots : Array FVarId) (selMap : SelMap)
  (kont : FVarId -> SelMap -> CompilerM CodePre) : CompilerM CodePre :=
  match selMap[sel]? with
  | some (v, _) => kont v selMap
  | none =>
    match sel with
    | .base i => kont roots[i]! selMap
    | .field s i =>
      resolveSel s roots selMap fun sv selMap => do
        let v <- fresh
        let rest <- kont v $ selMap.insert sel (v, dummyTy)
        return .let ⟨v, "sel", dummyTy, .proj i sv⟩ rest

/-- Alias each PVar binding to its resolved variable -/
def bindPatVars (binds : List (String × Sel)) (roots : Array FVarId)
  (selMap : SelMap) (ρ : FVarEnv) (kont : FVarEnv -> CompilerM CodePre) : CompilerM CodePre :=
  match binds with
  | [] => kont ρ
  | (x, sel) :: rest =>
    resolveSel sel roots selMap fun v selMap =>
      bindPatVars rest roots selMap (ρ.insert x v) kont

/-- `let r = matchFailure (); ret r`. -/
def mkMatchFail (resTy : MLType) : CompilerM CodePre :=
  fresh <&> fun r => .let ⟨r, "fail", resTy, .app matchFailFVar #[]⟩ $ .ret $ .fvar r

inductive Cont where
  | ret
  | jmp    : FVarId -> Cont
    /-- exists in metalanguage, that is, Lean. -/
  | «meta» : (Atom -> CompilerM CodePre) -> Cont

def Cont.apply : Cont -> Atom -> CompilerM CodePre
  | .ret    => pure ∘ .ret
  | .jmp j  => pure ∘ Code.jmp j ∘ Array.singleton
  | .meta k => k

def Cont.applyFVar : Cont -> FVarId -> CompilerM CodePre := (·.apply ∘ .fvar)

/--
  reify `k` into a jp.
  used by Cond/Match to make inner matches jump straight to the outer jp.
-/
def withJoin (k : Cont) (resTy : MLType) (body : Cont -> CompilerM CodePre)
  : CompilerM CodePre :=
  match k with
  | .meta k => do
    let j <- fresh; let p <- fresh
    let jbody <- k $ .fvar p
    let inner <- body $ .jmp j
    return .jp ⟨j, "κ", #[⟨p, "v", resTy⟩], resTy, jbody⟩ inner
  | k => body k

/-- emit n-ary application according to the head's arity. Denotational semantics:

```plaintext
arity  ::= k               syntactic; typal fallback
         | 0               unknown; handled in codegen
rawapp ::= fₙ(x₁,..,xₖ)
         | ◾(x₁,..,xₖ)     pluggable; chained
funapp ::= fᶠ(a₁,..,aₙ)    app
         | fᵖ(a₁,..,aₙ)    pap

⟦f₀(a₁,..,aₘ)⟧ = fᶠ(a₁,..,aₘ)                         (EXACT)
⟦fₙ(a₁,..,aₙ)⟧ = fᶠ(a₁,..,aₙ)     Full                (KNOWNCALL)
⟦fₖ(a₁,..,aₘ)⟧ = fᵖ(a₁,..,aₘ)     Part; where m < k   (PAP2)
               | fᶠ(a₁,..,aₖ)     Over; where m > k   (CallK)
               ; ⟦◾(aₖ₊₁,..,aₘ)⟧
                 ^^^^^^^^^^^^^^^
                /
               /
Note that this part is also (with EXACT) handled in codegen
through generic apply/curry if the tail arity is unknown
```

See also:
> Marlow, Simon, and Simon Peyton Jones.
> "Making a fast curry: push/enter vs. eval/apply for higher-order languages."
> ACM SIGPLAN Notices 39.9 (2004): 4-15.
-/
partial def emitApp (f : FVarId) (fty : MLType) (args : Array Atom)
  (kont : FVarId -> CompilerM CodePre) : CompilerM CodePre :=
  if args.isEmpty then kont f
  else do --          syntactic arity first, then (· -> ·) count
    let ar <- get <&> (·.arity[f]?.getD $ arrArity fty)
    if ar == 0 then
      bindLet "app" fty (.app f args) kont
    else if args.size <= ar then
      let node := if args.size < ar then .pap f args else .app f args
      bindLet "app" (peelArrows args.size fty) node kont
    else
      let now  := args.extract (stop := ar)
      let rest := args.extract (start := ar)
      bindLet "app" (peelArrows ar fty) (.app f now) fun r =>
        emitApp r (peelArrows ar fty) rest kont

mutual

partial def lower (e : FExpr) (ρ : FVarEnv) (k : Cont) : CompilerM CodePre := do
  let ctors <- NFState.ctors <$> get
  if let some (op, x, y) := matchBinaryPrim e then
    lowerMany #[x, y] ρ fun as =>
      bindLet "π" e.getTy (.prim op as) k.applyFVar

  else if let some (cname, args, ar) := matchCtorApp ctors e then
    lowerCtorApp cname args ar e.getTy ρ k

  else match e with
    | .CI i _  => k.apply $ .lit $ .PInt i
    | .CB b _  => k.apply $ .lit $ .PBool b
    | .CS s _  => k.apply $ .lit $ .PStr s
    | .CUnit _ => k.apply $ .lit $ .PUnit

    | .Var x _ =>
      match ρ.find? x with
      | some v => k.apply $ .fvar v
      | none   => internExtern x >>= k.applyFVar

    | .TyLam _ b => lower b ρ k
    | .TyApp f _ => lower f ρ k

    | .Prod' l r ty =>
      lower l ρ $ .meta fun a => lower r ρ $ .meta fun b =>
        bindLet "p" ty (.pair a b) k.applyFVar

    | .Proj src _ idx ty =>
      -- always a record/dictionary field access (single-ctor struct).
      lowerV src ρ fun s => do
        bindLet "pr" ty (.field (<- soleCtorOf src.getTy) idx s) k.applyFVar

    | .App .. =>
      let (head, args) := decomposeApp e
      lowerV head ρ fun f =>
        lowerMany args ρ fun as =>
          emitApp f head.getTy as k.applyFVar
    | .Fun .. =>
      let (params, core) := peelLam e
      lowerFun "fn" params.toArray core e.getTy ρ k.applyFVar

    | .Fix inner _ =>
      let (allParams, core) := peelLam inner
      lowerRec e.getTy allParams.toArray core ρ k.applyFVar

    | .Let binds body _ => lowerLet binds body ρ k

    | .Cond c t e' ty =>
      withJoin k ty fun k' => lowerV c ρ fun cv =>
        ( .cases cv ty #[.const (.PBool true) ·, .const (.PBool false) ·])
       <$> lower t ρ k'  -- then
       <*> lower e' ρ k' -- else

    | .Match scrs rows resTy ex _ => lowerMatch scrs rows resTy ex.isNone ρ k

partial def lowerV (e : FExpr) (ρ : FVarEnv) (k : FVarId -> CompilerM CodePre)
  : CompilerM CodePre :=
  lower e ρ $
    .meta fun
    | .fvar v => k v
    | .lit c  => bindLet "v" e.getTy (.lit c) k
    | .erased => throw "lowerV: erased atom in variable position"

partial def lowerMany (es : Array FExpr) (ρ : FVarEnv)
  (kont : Array Atom -> CompilerM CodePre)
  (i : Nat := 0) (acc : Array Atom := #[]) : CompilerM CodePre :=
  if h : i < es.size then
    lower es[i] ρ <| .meta fun a => lowerMany es ρ kont (i + 1) (acc.push a)
  else kont acc

partial def lowerVMany (es : Array FExpr) (ρ : FVarEnv)
  (kont : Array FVarId -> CompilerM CodePre)
  (i : Nat := 0) (acc : Array FVarId := #[]) : CompilerM CodePre :=
  if h : i < es.size then
    lowerV es[i] ρ fun v => lowerVMany es ρ kont (i + 1) (acc.push v)
  else kont acc

partial def lowerFun (name : String) (params : Array (String × MLType))
  (core : FExpr) (funTy : MLType) (ρ : FVarEnv)
  (kont : FVarId -> CompilerM CodePre) : CompilerM CodePre := do
  let fv <- fresh
  let mut paramArr     := #[]
  let mut ρ' : FVarEnv := ρ

  for (nm, ty) in params do
    let pf <- fresh
    paramArr := paramArr.push $ Param.mk pf nm ty
    ρ'       := ρ'.insert nm pf

  let body <- lower core ρ' .ret
  setArity fv params.size
  .fun ⟨fv, name, paramArr, funTy, body⟩ <$> kont fv

partial def lowerRec (funTy : MLType) (allParams : Array (String × MLType))
  (core : FExpr) (ρ : FVarEnv) (kont : FVarId -> CompilerM CodePre) : CompilerM CodePre := do
  let fv <- fresh
  let selfN := allParams[0]?.map Prod.fst |>.getD "self"
  let mut paramArr := #[]
  let mut ρ'       := ρ.insert selfN fv

  for (nm, ty) in allParams[1:] do
    let pf <- fresh
    paramArr := paramArr.push $ Param.mk pf nm ty
    ρ'       := ρ'.insert nm pf

  let body <- lower core ρ' .ret
  setArity fv paramArr.size -- = |allParams| - 1
  .fun ⟨fv, selfN, paramArr, funTy, body⟩ <$> kont fv

partial def lowerLet (binds : Array (String × Scheme × FExpr)) (body : FExpr)
  (ρ : FVarEnv) (k : Cont) : CompilerM CodePre :=
  let (recs, nonrecs) := binds.partition (isRecBind ∘ Prod.snd ∘ Prod.snd)
  lowerNonRec nonrecs ρ fun ρ =>
    if recs.isEmpty then lower body ρ k
    else lowerRecGroup recs ρ fun ρ => lower body ρ k

partial def lowerNonRec (ns : Array (String × Scheme × FExpr)) (ρ : FVarEnv)
  (kont : FVarEnv -> CompilerM CodePre) (i : Nat := 0) : CompilerM CodePre :=
  if h : i < ns.size then
    let (x, _, fe) := ns[i]
    lowerV fe ρ fun v => lowerNonRec ns (ρ.insert x v) kont i.succ
  else kont ρ

partial def lowerRecGroup (recs : Array (String × Scheme × FExpr)) (ρ : FVarEnv)
  (kont : FVarEnv -> CompilerM CodePre) : CompilerM CodePre := do
  let fvs <- recs.mapM fun _ => fresh
  let ρg := Array.foldl2 (·.insert ·.1 ·) ρ recs fvs
  let decls <- Array.zipWithM (as := recs) (bs := fvs) fun (name, _, fe) fv => do
    let inner := match fe with | .Fix i _ => i | _ => fe
    let (allParams, core) := peelLam inner
    let selfN := allParams.head?.map Prod.fst |>.getD name
    let mut paramArr := #[]
    let mut ρ' := ρg.insert selfN fv
    let mut length := 0

    for (nm, ty) in allParams.tail do
      let pf <- fresh
      paramArr := paramArr.push $ Param.mk pf nm ty
      ρ'       := ρ'.insert nm pf
      length   := length + 1

    let body <- lower core ρ' .ret
    setArity fv length
    pure (⟨fv, name, paramArr, fe.getTy, body⟩ : FunDecl .preCC)

  let rest <- kont ρg
  return decls.foldr .fun rest

partial def lowerCtorApp (cname : String) (args : Array FExpr) (ar : Nat)
  (resTy : MLType) (ρ : FVarEnv) (k : Cont) : CompilerM CodePre := do
  if args.size == ar then
    lowerMany args ρ fun as => bindLet "con" resTy (.ctor cname as) fun r => k.apply $ .fvar r
  else if args.size < ar then
    lowerMany args ρ fun supplied => do
      let missing := ar - args.size
      let (missTys, finalTy) := resTy.decomposeArr'
      let fv <- fresh
      let mut supplied := supplied
      let mut paramArr := #[]
      let mut missTys  := missTys

      for _ in [:missing] do
        let pf <- fresh
        let ty := missTys.head?.getD dummyTy
        supplied := supplied.push $ Atom.fvar pf
        paramArr := paramArr.push $ Param.mk pf "η" ty
        missTys  := missTys.tail

      let conFv <- fresh
      let body := .let ⟨conFv, "con", finalTy, .ctor cname supplied⟩ $ .ret $ .fvar conFv
      setArity fv missing
      .fun ⟨fv, cname, paramArr, resTy, body⟩ <$> k.apply (.fvar fv)
  else
    panic! s!"over-applied constructor {cname}"

partial def lowerMatch (scrs : Array FExpr) (rows : Array (Array Pattern × FExpr))
  (resTy : MLType) (exhaustive : Bool) (ρ : FVarEnv) (k : Cont) : CompilerM CodePre :=
  let scrTys := scrs.map (·.getTy)
  withJoin k resTy fun k' =>
    lowerVMany scrs ρ fun roots => do
      let cols : Array Sel := Array.ofFn (n := roots.size) fun i => Sel.base i.val
      let rstates := rows.map fun (pats, rhs) => show RowState from {pats, rhs}
      let dt := buildTree cols rstates
      let selMap : SelMap :=
        roots.size.fold (fun i h a => a.insert (.base i) (roots[i], scrTys[i]!)) ∅
      if exhaustive then
        lowerDT dt cols roots selMap ρ k' resTy $ .unreach resTy
      else
        let jf <- fresh
        let failBody <- mkMatchFail resTy
        let cases <- lowerDT dt cols roots selMap ρ k' resTy $ .jmp jf #[]
        return .jp ⟨jf, "fail", #[], resTy, failBody⟩ cases

partial def lowerDT (dt : DTree) (cols : Array Sel) (roots : Array FVarId)
  (selMap : SelMap) (ρ : FVarEnv) (k' : Cont) (resTy : MLType) (onFail : CodePre)
  : CompilerM CodePre := do
  match dt with
  | .fail => return onFail
  | .leaf row =>
    bindPatVars row.binds.toList roots selMap ρ fun ρ => lower row.rhs ρ k'
  | .splitProd j next =>
    let sel := cols[j]!
    let (tA, tB) := match selTyOf sel selMap with | a ×'' b => (a, b) | _ => (dummyTy, dummyTy)
    resolveSel sel roots selMap fun sv selMap => do
      let a <- fresh; let b <- fresh
      let selMap := selMap.insert (.field sel 0) (a, tA) |>.insert (.field sel 1) (b, tB)
      let cols := replaceCol cols j #[.field sel 0, .field sel 1]
      let rest <- lowerDT next cols roots selMap ρ k' resTy onFail
      return .let ⟨a, "fst", tA, .proj 0 sv⟩
           $ .let ⟨b, "snd", tB, .proj 1 sv⟩ rest
  | .testCtor j cases dflt? =>
    let sel := cols[j]!
    let scrutTy := selTyOf sel selMap
    resolveSel sel roots selMap fun sv selMap => do
      let alts <- cases.mapM fun (cname, ar, sub) => do
        let fieldFvs <- Array.ofFnM (n := ar) fun _ => fresh
        let ftys <- instCtorFields cname ar scrutTy
        let selMap' := ar.fold (fun i _ m => m.insert (.field sel i) (fieldFvs[i]!, ftys[i]!)) selMap
        let cols' := replaceCol cols j (Array.ofFn (n := ar) fun i => .field sel i.val)
        let body <- lowerDT sub cols' roots selMap' ρ k' resTy onFail
        let params := fieldFvs.mapIdx fun i fv => Param.mk fv "f" ftys[i]!
        pure (Alt.ctor cname params body)
      let defAlt <- mkDefaultAlt dflt? cols j roots selMap ρ k' resTy onFail
      return .cases sv resTy (alts ++ defAlt)
  | .testConst j cases dflt? =>
    let sel := cols[j]!
    resolveSel sel roots selMap fun sv selMap => do
      let alts <- cases.mapM fun (c, sub) => do
        let cols' := cols.eraseIdx! j
        let body <- lowerDT sub cols' roots selMap ρ k' resTy onFail
        pure (Alt.const c body)
      let defAlt <- mkDefaultAlt dflt? cols j roots selMap ρ k' resTy onFail
      return .cases sv resTy (alts ++ defAlt)

partial def mkDefaultAlt (dflt? : Option DTree) (cols : Array Sel) (j : Nat)
  (roots : Array FVarId) (selMap : SelMap) (ρ : FVarEnv) (k' : Cont) (resTy : MLType)
  (onFail : CodePre) : CompilerM (Array (Alt .preCC)) :=
  match dflt? with
  | some d => do
    let cols' := cols.eraseIdx! j
    let body <- lowerDT d cols' roots selMap ρ k' resTy onFail
    return #[.default body]
  | none => return #[.default onFail]

end

section Helper

/-- for toplevel pattern binding -/
def patExhaustive (scrutTy : MLType) (pat : Pattern) : CompilerM Bool := do
  let {tyDecl,..} <- get
  let x : Env := ∅
  return Exhaustive.exhaustWitness {x with tyDecl := tyDecl} #[scrutTy] #[(#[pat], ())] |>.1 |>.isNone

/--
  Deriving monotype for toplevel PVar bindings by checking `pat` against `scrutTy`
  - PCtor c as: consults `instCtorFields c |as| scrutTy`
  - PProd p q: recurse directly on p and q.
-/
partial def patVarTys (scrutTy : MLType) (pat : Pattern) : CompilerM (Array (String × MLType)) := do
  let scrutTy := unwrapTSch scrutTy
  match pat with
  | .PVar x       => return #[(x, scrutTy)]
  | .PWild        => return #[]
  | .PConst _     => return #[]
  | .PProd' p q   =>
    let (tA, tB) := match scrutTy with | a ×'' b => (a, b) | _ => (dummyTy, dummyTy)
    (· ++ ·) <$> (patVarTys tA p) <*> (patVarTys tB q)
  | .PCtor cname args =>
    let ftys <- instCtorFields cname args.size scrutTy
    Array.foldlM2
      (fun acc arg fty => (acc ++ ·) <$> patVarTys fty arg)
      #[] args ftys

def collectTopNames (decls : Array TopDeclF) : Array String :=
  decls.flatMap fun
  | .idBind binds =>
    binds.filterMap fun (x, _, _) => if x.startsWith "(" then none else some x
  | .patBind (pat, _) => pat.vars
end Helper

/-- Lower one top-level declaration to 1+ decls.
Note that `p₀` maps every top-level name to its global `FVarId`,
allowing mutual/forward references and `extern`/builtin to resolve -/
partial def lowerTopDecl (ρ₀ : FVarEnv) : TopDeclF -> CompilerM (Array (Decl .preCC))
  | .idBind binds => binds.filterMapM fun (name, _, fe) => do
    if name.startsWith "(" then return none

    let fe := stripTy fe
    let fv <- match ρ₀.find? name with | some v => pure v | none => internExtern name
    if isRecBind fe then
      let inner := match fe with | .Fix i _ => i | _ => fe
      let (allP, core) := peelLam inner
      let selfN := allP.head?.map Prod.fst |>.getD name
      let mut paramArr := #[]
      let mut ρ'       := ρ₀.insert selfN fv
      let mut length   := 0

      for (nm, ty) in allP.tail do
        let pf <- fresh
        paramArr := paramArr.push $ Param.mk pf nm ty
        ρ'       := ρ'.insert nm pf
        length   := length + 1

      let body <- lower core ρ' .ret
      setArity fv length
      return some {fvarId := fv, name, params := paramArr, ty := fe.getTy, body, recursive := true}
    else
      let (params, core) := peelLam fe
      -- `extern id str : sch` lowered to `let id = Var str`, where `str` is a
      -- foreign name. η-expand to an N-ary wrapper decl
      -- whose body is a direct saturated foreign call.
      if let .Var str _ := core then
        if params.isEmpty && (ρ₀.find? str).isNone then
          let (argTys, finalTy) := core.getTy.decomposeArr'
          let mut paramArr   := #[]
          let mut paramAtoms := #[]
          for aty in argTys do
            let pf <- fresh
            paramArr   := paramArr.push $ Param.mk pf "η" aty
            paramAtoms := paramAtoms.push $ Atom.fvar pf
          let r <- fresh
          let body := .let ⟨r, "ffi", finalTy, .extern str paramAtoms⟩ $ .ret $ .fvar r
          setArity fv paramArr.size
          return some {fvarId := fv, name, params := paramArr, ty := fe.getTy, body}

      let mut paramArr := #[]
      let mut ρ'       := ρ₀
      let mut length   := 0

      for (nm, ty) in params do
        let pf <- fresh
        paramArr := paramArr.push $ Param.mk pf nm ty
        ρ'       := ρ'.insert nm pf
        length   := length + 1

      let body <- lower core ρ' .ret
      setArity fv length
      return some {fvarId := fv, name, params := paramArr, ty := fe.getTy, body, recursive := false}
  | .patBind (.PVar x, fe) => do
    let fv <- match ρ₀.find? x with | some v => pure v | none => internExtern x
    let body <- lower (stripTy fe) ρ₀ .ret
    return #[{fvarId := fv, name := x, params := #[], ty := fe.getTy, body}]
  | .patBind (pat, fe) => do
    -- `let pat = e` : bind a scrutinee `e`, then re-match it per bound variable.
    let fe := stripTy fe
    let fv <- fresh
    let pbName := s!"pb#{fv}"
    let pbFv <- internExtern pbName
    let ρp := ρ₀.insert pbName pbFv
    let scrutBody <- lower fe ρ₀ .ret
    let scrutDecl : Decl .preCC := {fvarId := pbFv, name := pbName, params := #[], ty := fe.getTy, body := scrutBody}
    let exhaustive <- patExhaustive fe.getTy pat
    let varDecls <- (<- patVarTys fe.getTy pat).mapM fun (x, xty) => do
      let xfv <- match ρ₀.find? x with | some v => pure v | none => internExtern x
      let body <- lowerMatch
        #[.Var pbName fe.getTy]
        #[(#[pat], .Var x xty)]
        xty
        exhaustive
        ρp .ret
      return ({fvarId := xfv, name := x, params := #[], ty := xty, body} : Decl .preCC)
    return #[scrutDecl] ++ varDecls

/-- ctor ↦ (its param types, tyctor TVs) -/
def ctorTypeInfo (tyDecls : TyMap)
  : Std.HashMap String (Array MLType) × Std.HashMap String (List TV) :=
  tyDecls.fold (init := (∅, ∅)) fun acc _ td =>
    let params := td.param.foldr (List.cons ∘ TV.mkTV ∘ Prod.fst) []
    td.ctors.foldl (init := acc) fun (fts, tps) (cname, fields, _) =>
      ( fts.insert cname $ fields.foldl (Array.push · ·.2) #[]
      , tps.insert cname params)

end Compiler
