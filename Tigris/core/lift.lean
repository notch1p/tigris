import Tigris.core.lam
import Tigris.core.opt
namespace IR

/-!
Closure conversion for the Lambda IR.

Layout:
- Eliminate Value.lam by lifting to code pointers (functions) that take a single
  "payload" parameter = ⟨arg, env⟩.
- Environments (Γ) are explicit values holding captured variables.
- A closure is a 2-field constructor: (𝐂⟦codePtr, env⟧).
- Calls through closure variables project (code, env) and pass (arg, env) to the code pointer.
- letRec groups are converted so each function body projects (arg, env) from payload. For recursion,
  body calls the code pointer with the same env. Mutual recursion is planned: all fns in a group
  use the same env layout.

We also:
- Lifts nested lambdas inside code bodies.
- Treats known global code pointers as direct calls (building an empty env payload),
  instead of projecting them as if they were closures (only in code bodies where not shadowed).
- Makes captured-variable layout deterministic by sorting the captures by name.
- Reuses entry env (avoid re-projecting payload[1] in recursive calls).
- Peephole: eliminates immediate closure-call
- cleanup is reinforced by optimizeLam.
-/

namespace CC
variable {σ}
abbrev CodeSet := Std.TreeSet Name
abbrev AvoidSet := Std.HashSet Name

def sortedNames (s : Std.HashSet Name) : Array Name := s.toArray.qsort

/-- we reuse the `M` monad found in lam.lean which carries a state where
  - gensym: counter
  - AMap: useless in CC/opt.
-/
nonrec def fresh (h := "cc") : M σ Name := fresh h

def mkEnv (envTag : Name) (fields : Array Name) (kont : Name -> LExpr) : LExpr :=
  letI envName := "Γ"
  .letRhs envName (.mkConstr envTag fields) (kont envName)

def bindClos (target : Name) (code : Name) (envName : Name) (kont : LExpr) : LExpr :=
  .letRhs target (.mkConstr "𝐂" #[code, envName]) kont

def mkPayload (arg env : Name) (kont : Name -> LExpr) : LExpr :=
  letI p := "ρ"
  .letRhs p (.mkPair arg env) (kont p)

def proj (src : Name) (i : Nat) (kont : Name -> LExpr) : LExpr :=
  letI x := "π" ++ toString i
  .letRhs x (.proj src i) (kont x)

def projPair (src : Name) (kont : Name -> Name -> LExpr) : LExpr :=
  proj src 0 fun a => proj src 1 fun b => kont a b

def freeVars (e : LExpr) : Std.HashSet Name :=
  fvExpr e

def tailAppDirectM
  (payload : Name) (envVar? : Option Name)
  (f : Name) (a : Name) : M σ (Array Stmt × Tail) := do
  match envVar? with
  | some e =>
    let pl <- fresh "ρ"
    return (#[.let1 pl (.mkPair a e)], .app f pl)
  | none =>
    let env <- fresh "Γ"
    let pl <- fresh "ρ"
    return (#[.let1 env (.proj payload 1), .let1 pl (.mkPair a env)], .app f pl)

def tailAppViaClosureM (clos : Name) (a : Name) : M σ (Array Stmt × Tail) := do
  let code <- fresh "_code"
  let env  <- fresh "Γc"
  let pl   <- fresh "ρc"
  return ( #[ .let1 code (.proj clos 0)
            , .let1 env  (.proj clos 1)
            , .let1 pl   (.mkPair a env)]
         , Tail.app code pl)

def tailAppGlobalM (f : Name) (a : Name) : M σ (Array Stmt × Tail) := do
  let env <- fresh "Γ₀"
  let pl  <- fresh "ρ"
  return ( #[ .let1 env (.mkConstr "𝐄" #[])
            , .let1 pl  (.mkPair a env)]
         , Tail.app f pl)

attribute [inline]
  proj  bindClos   mkPayload
  fresh freeVars
  mkEnv projPair
  sortedNames

/-- Monadic rewriting of a tail inside a code body (can lift lambdas in branches).
    selfVar? = some v means: if callee == v, rewrite as a direct call to the current code pointer `selfCode`.
    envVar? = some e reuses the entry env (avoid re-projecting payload[1]). -/
partial def rewriteTailInCodeM
  (payload : Name) (envVar? : Option Name) (codeSet gCodes : CodeSet)
  (selfVar? : Option Name) (selfCode : Name)
  (cc : LExpr -> M σ (LExpr × Array LFun))
  : Tail -> M σ (Array Stmt × Tail × Array LFun)
  | .app f a => do
    if selfVar?.isEqSome f then
      let (bs, t) <- tailAppDirectM payload envVar? selfCode a
      return (bs, t, #[])
    else if f ∈ codeSet then
      let (bs, t) <- tailAppDirectM payload envVar? f a
      return (bs, t, #[])
    else if f ∈ gCodes then
      let (bs, t) <- tailAppGlobalM f a
      return (bs, t, #[])
    else
      let (bs, t) <- tailAppViaClosureM f a
      return (bs, t, #[])
  | .cond c t e => do
    let (t', ft) <- cc t
    let (e', fe) <- cc e
    return (#[], .cond c t' e', ft ++ fe)
  | .switchConst s cases d? => do
    let (cases', fs) <- cases.foldlM
      (init := (#[], #[]))
      fun (acc, fs) (k, b) => do
        let (b', f) <- cc b
        pure (acc.push (k, b'), fs ++ f)
    let (d'?, fs2) <-
      match d? with
      | some b => do
          let (b', f) <- cc b
          pure (some b', f)
      | none => pure (none, #[])
    return (#[], .switchConst s cases' d'?, fs ++ fs2)
  | .switchCtor s cases d? => do
    let (cases', fs) <- cases.foldlM
      (init := (#[], #[]))
      fun (acc, fs) (c, ar, b) => do
        let (b', f) <- cc b
        pure (acc.push (c, ar, b'), fs ++ f)
    let (d'?, fs2) <-
      match d? with
      | some b => do
          let (b', f) <- cc b
          pure (some b', f)
      | none => pure (none, #[])
    return (#[], .switchCtor s cases' d'?, fs ++ fs2)
  | tl => pure (#[], tl, #[]) -- ret, matchFail

/-- Emit a non-tail `x := f a` inside a code body, handling:
    - self redirection (calls to wrapper variable → current code pointer),
    - direct calls to local group code pointers (use payload env),
    - direct calls to known global code pointers (empty env),
    - closure calls via projection. -/
def emitLetCallInCode
  (payload : Name) (envVar? : Option Name) (codeSet gCodes : CodeSet)
  (selfVar? : Option Name) (selfCode : Name)
  (x f a : Name) (k : LExpr) : M σ LExpr := do
  if selfVar?.isEqSome f then
    let pl <- fresh "ρ"
    match envVar? with
    | some e =>
      return .letRhs pl (.mkPair a e)
           $ .letRhs x  (.call selfCode pl) k
    | none =>
      let env <- fresh "Γ"
      return .letRhs env (.proj payload 1)
           $ .letRhs pl  (.mkPair a env)
           $ .letRhs x   (.call selfCode pl) k
  else if f ∈ codeSet then
    let pl <- fresh "ρ"
    match envVar? with
    | some e =>
      return .letRhs pl (.mkPair a e)
           $ .letRhs x  (.call f pl) k
    | none =>
      let env <- fresh "Γ"
      return .letRhs env (.proj payload 1)
           $ .letRhs pl  (.mkPair a env)
           $ .letRhs x   (.call f pl) k
  else if f ∈ gCodes then
    let env <- fresh "Γ₀"
    let pl  <- fresh "ρ"
    return .letRhs env (.mkConstr "𝐄" #[])
         $ .letRhs pl  (.mkPair a env)
         $ .letRhs x   (.call f pl) k
  else
    let code <- fresh "_code"
    let env  <- fresh "Γc"
    let pl   <- fresh "ρc"
    return .letRhs code (.proj f 0)
         $ .letRhs env  (.proj f 1)
         $ .letRhs pl   (.mkPair a env)
         $ .letRhs x    (.call code pl) k

/-- Peephole:
  if body is `xᵀ(a)` and `x` is the closure we just bound for code `fid`
    and env `envName`, rewrite the tail to `fidᵀ(⟨a, envName⟩)` and let DCE remove the closure. -/
def fuseImmediateTailCall (envName x fid : Name) : LExpr -> LExpr
  | .seq binds (.app f a) =>
    if f == x then
      let pl := "ρ"
      .seq (binds.push (.let1 pl (.mkPair a envName))) (.app fid pl)
    else .seq binds (.app f a)
  | .letVal y v b => .letVal y v (fuseImmediateTailCall envName x fid b)
  | .letRhs y r b => .letRhs y r (fuseImmediateTailCall envName x fid b)
  | .letRec fs b => .letRec fs (fuseImmediateTailCall envName x fid b)
  | e => e

namespace Rename
abbrev NMap := Std.HashMap Name Name

@[inline] def rw (m : NMap) (x : Name) : Name :=
  match m.get? x with | some y => y | none => x
mutual
partial def value (m : NMap) : Value -> Value
  | .var x       => .var (rw m x)
  | .cst k       => .cst k
  | .constr t fs => .constr t (fs.map (rw m))
  | .lam p b     => .lam p (expr (m.erase p) b)

partial def rhs (m : NMap) : Rhs -> Rhs
  | .prim op args     => .prim op (args.map (rw m))
  | .proj s i         => .proj (rw m s) i
  | .mkPair a b       => .mkPair (rw m a) (rw m b)
  | .mkConstr t fs    => .mkConstr t (fs.map (rw m))
  | .isConstr s t ar  => .isConstr (rw m s) t ar
  | .call f a         => .call (rw m f) (rw m a)

partial def tail (m : NMap) : Tail -> Tail
  | .ret x      => .ret (rw m x)
  | .app f a    => .app (rw m f) (rw m a)
  | .cond c t e => .cond (rw m c) (expr m t) (expr m e)
  | .switchConst s cases d? =>
    .switchConst (rw m s) (cases.map (fun (k,b) => (k, expr m b))) (d? |>.map (expr m))
  | .switchCtor s cases d? =>
    .switchCtor (rw m s) (cases.map (fun (c,ar,b) => (c, ar, expr m b))) (d? |>.map (expr m))
  | mf => mf -- matchFail

partial def expr (m : NMap) : LExpr -> LExpr
  | .letVal x v b => .letVal x (value m v) (expr (m.erase x) b)
  | .letRhs x r b => .letRhs x (rhs m r) (expr (m.erase x) b)
  | .letRec fs b =>
    let m' := fs.foldl (init := m) (fun acc f => acc.erase f.fid |>.erase f.param)
    let fs' := fs.map (fun ⟨fid,p,body⟩ => ⟨fid, p, expr (m'.erase p) body⟩)
    .letRec fs' (expr m' b)
  | .seq binds t => .seq (binds.map (fun (.let1 x r) => .let1 x (rhs m r))) (tail m t)
end
end Rename

mutual
/--

Notable params:
- fid: code pointer name (kept to detect direct recursion).
- paramPayload: the single parameter name for the new function.
- capVars: the list of captured variables (deterministic order gives env layout).
- codeSet: set of code pointer names visible in the current recursive group (for mutual recursion).
- body: original function body with old parameter `origParam` occurrences.
- selfVar? = some wrapperName means:
  - inside this lambda body, calls to wrapperName are direct recursive calls to the current code pointer

Note that we assume the caller has already α-conv the old parameter to `origParam`
and provided its name, so we can bind it from payload.
-/
partial def ccCodeBodyM
  (gCodes : CodeSet)
  (fid : Name) (paramPayload : Name) (origParam : Name)
  (capVars : Array Name) (codeSet : CodeSet)
  (selfVar? : Option Name) (envVar? : Option Name)
  : LExpr -> M σ (LExpr × Array LFun)
  | .seq binds tail => do
    let (extra, tail', ft) <-
      rewriteTailInCodeM
        paramPayload envVar? codeSet
        gCodes selfVar? fid
        (ccCodeBodyM gCodes fid paramPayload origParam
         capVars codeSet selfVar? envVar?)
        tail
    return (.seq (binds ++ extra) tail', ft)

  | .letVal x (.lam p b) body => do
    let fid' <- fresh "fn"
    let capsSet := (fvExpr b).erase p
    let capVars' := sortedNames capsSet
    let payload := "payload"
    let codeSet' := codeSet.insert fid'
    let (lb, liftedFuns) <-
      ccLiftedFunBodyM
        gCodes fid' payload p
        capVars' codeSet' none b
    let funDef : LFun := ⟨fid', payload, lb⟩
    let (body', fs) <-
      ccCodeBodyM
        gCodes fid paramPayload origParam
        capVars codeSet selfVar? envVar? body
--    let newBody :=
--      mkEnv "𝐄" capVars' fun env =>
--        bindClos x fid' env body'
    let newBody :=
      mkEnv "𝐄" capVars' fun env =>
        bindClos x fid' env (fuseImmediateTailCall env x fid' body')
    return (newBody, liftedFuns.push funDef ++ fs)

  | .letVal x v body => do
    let (b', fs) <-
      ccCodeBodyM
        gCodes fid paramPayload origParam
        capVars codeSet selfVar? envVar?
        body
    return (.letVal x v b', fs)

  | .letRhs x (.call f a) body => do
    let (b', fs) <-
      ccCodeBodyM
        gCodes fid paramPayload origParam
        capVars codeSet selfVar? envVar? body
    let e' <- emitLetCallInCode paramPayload envVar? codeSet gCodes selfVar? fid x f a b'
    return (e', fs)

  | .letRhs x rhs body => do
    let (b', fs) <-
      ccCodeBodyM
        gCodes fid paramPayload origParam
        capVars codeSet selfVar? envVar? body
    return (.letRhs x rhs b', fs)

  | .letRec funs body => do
    let (e', fs) <- ccExpr gCodes (.letRec funs body)
    return (e', fs)

/-- At code entry: payload = ⟨origParam, env⟩. -/
partial def ccLiftedFunBodyM
  (gCodes : CodeSet)
  (fid : Name) (payload : Name) (origParam : Name)
  (capVars : Array Name) (codeSet : CodeSet)
  (selfVar? : Option Name := none)
  (body : LExpr)
  : M σ (LExpr × Array LFun) := do
  let aN    := "α"
  let envN  := "Γ"
  let (inner, fs) <-
    ccCodeBodyM
      gCodes fid payload origParam
      capVars codeSet selfVar? (some envN) body
  let wrapped :=
    .letRhs aN  (.proj payload 0) $
    .letRhs envN (.proj payload 1) $
    .letVal origParam (.var aN) $
      capVars.size.fold
        (init := inner)
        (fun i _ acc => .letRhs capVars[i] (.proj envN i) acc)
  return (wrapped, fs)

/-- Rewrite tails in non-code contexts (e.g., main)-/
partial def rewriteTailOutsideM
  (gCodes : CodeSet)
  (cc : LExpr -> M σ (LExpr × Array LFun))
  : Tail -> M σ (Array Stmt × Tail × Array LFun)
  | .app f a => do
--    let (bs, t) <- tailAppViaClosureM f a
--    return (bs, t, #[])
    if f ∈ gCodes then
      let (bs, t) <- tailAppGlobalM f a
      return (bs, t, #[])
    else
      let (bs, t) <- tailAppViaClosureM f a
      return (bs, t, #[])
  | .cond c t e => do
    let (t', ft) <- cc t
    let (e', fe) <- cc e
    return (#[], .cond c t' e', ft ++ fe)
  | .switchConst s cases d? => do
    let (cases', fs) <- cases.foldlM
      (init := (#[], #[]))
      fun (acc, fs) (k, b) => do
        let (b', f) <- cc b
        pure (acc.push (k, b'), fs ++ f)
    let (d'?, fs2) <- match d? with
                      | some b => do let (b', f) <- cc b; pure (some b', f)
                      | none   => pure (none, #[])
    return (#[], .switchConst s cases' d'?, fs ++ fs2)
  | .switchCtor s cases d? => do
    let (cases', fs) <- cases.foldlM
      (init := (#[], #[]))
      fun (acc, fs) (c, ar, b) => do
        let (b', f) <- cc b
        pure (acc.push (c, ar, b'), fs ++ f)
    let (d'?, fs2) <- match d? with
                      | some b => do let (b', f) <- cc b; pure (some b', f)
                      | none   => pure (none, #[])
    return (#[], .switchCtor s cases' d'?, fs ++ fs2)
  | tl => pure (#[], tl, #[]) -- ret, matchFail

/--
Closure-convert an expression (non-code context):
- Value.lam is lifted to a code pointer and replaced with a closure �(code, env).
- letRec groups become code pointers with payload; continuation binds closures from a shared env.
- Calls are rewritten to closure-call form in both letRhs and tails.
Returns converted expr + any lifted functions to add to the module.
-/
partial def ccExpr (gCodes : CodeSet) : LExpr -> M σ (LExpr × Array LFun)
  | .seq binds tail => do
    let (extra, tail', ft) <- rewriteTailOutsideM gCodes (ccExpr gCodes) tail
    return (.seq (binds ++ extra) tail', ft)

  | .letVal x (.lam p b) body => do
    let fid <- fresh "fn"
    let capsSet := (fvExpr b).erase p
    let capVars := sortedNames capsSet
    let payload := "payload"
    let codeSet : CodeSet := (∅ : CodeSet).insert fid
    let (liftedBody, fsL) <- ccLiftedFunBodyM gCodes fid payload p capVars codeSet none b
    let funDef : LFun := ⟨fid, payload, liftedBody⟩
    let (body', newFuns) <- ccExpr gCodes body
    let newBody :=
      mkEnv "𝐄" capVars fun env =>
        bindClos x fid env (fuseImmediateTailCall env x fid body')
    return (newBody, fsL.push funDef ++ newFuns)

  | .letVal x v body => do
    let (b', fs) <- ccExpr gCodes body
    return (.letVal x v b', fs)

  | .letRhs x (.call f a) body => do
    if f ∈ gCodes then
      let env0 <- fresh "Γ₀"
      let pl   <- fresh "ρ"
      let (b', fs) <- ccExpr gCodes body
      let e' :=
        .letRhs env0 (.mkConstr "𝐄" #[])
        $ .letRhs pl   (.mkPair a env0)
        $ .letRhs x    (.call f pl) b'
      return (e', fs)
    else
      let code <- fresh "_code"
      let env  <- fresh "Γc"
      let pl   <- fresh "ρc"
      let (b', fs) <- ccExpr gCodes body
      let e' :=
        .letRhs code (.proj f 0)
        $ .letRhs env  (.proj f 1)
        $ .letRhs pl   (.mkPair a env)
        $ .letRhs x    (.call code pl) b'
      return (e', fs)

  | .letRhs x rhs body => do
    let (b', fs) <- ccExpr gCodes body
    return (.letRhs x rhs b', fs)

  | .letRec funs body => do
    -- Possibly mutual group
    let ids := funs.map (·.1)
    let fvBodies : Std.HashSet Name :=
      funs.foldl (fun acc ⟨_, p, b⟩ => acc ∪ (fvExpr b).erase p) ∅
    let capsSet := ids.foldl (·.erase) fvBodies
    let capVars := sortedNames capsSet
    let codeSet : CodeSet := ids.foldl (·.insert) ∅
    -- Convert each function to payload convention
    let funs' : Array LFun <- funs.flatMapM fun ⟨fid, p, b⟩ => do
        let payload := "payload"
        let (body', fs) <- ccLiftedFunBodyM gCodes fid payload p capVars codeSet none b
        pure $ #[⟨fid, payload, body'⟩] ++ fs
    let (body', tailFuns) <- ccExpr gCodes body

    let wrappers : Array (Name × Name) <- ids.mapM (fun fid => (fid, ·) <$> fresh (fid ++ "#clo"))
    let renameMap : Rename.NMap := wrappers.foldl (fun m (fid, w) => m.insert fid w) ∅
    let bodyRenamed := Rename.expr renameMap body'

    let rec bindClosures (i : Nat) (envName : Name) (k : LExpr) : LExpr :=
      if h : i < wrappers.size then
        let (fid, w) := wrappers[i]
        bindClos w fid envName (bindClosures (i + 1) envName k)
      else k
    let groupIntro :=
      mkEnv "𝐄" capVars fun envName =>
        let fused :=
          funs.foldl
            (init := bodyRenamed)
            (fun acc ⟨fid, _, _⟩ => fuseImmediateTailCall envName fid fid acc)
        bindClosures 0 envName fused
    --let groupIntro :=
    --  mkEnv "𝐄" capVars fun envName => bindClosures 0 envName body'
    return (groupIntro, funs' ++ tailFuns)
end
end CC

section open CC variable {σ}
/--
- convert 1 function. `gCodes` is the global code-pointer set
  - also runs optimizations.
- the variant `closureConvert` converts a whole module. Usually this should be used.
-/
def closureConvertFun (gCodes : CC.CodeSet) (f : LFun) : M σ (LFun × Array LFun) := do
  let pl := "payload"
  let capVars : Array Name := #[]
  let {fid, param, body} := f
  let codeSet : CodeSet := {f.fid}
  let (body, lifted) <- ccLiftedFunBodyM gCodes fid pl param capVars codeSet none body
  return ({fid, param := pl, body}, lifted)

@[inherit_doc closureConvertFun]
def closureConvert (m : LModule) : M σ LModule := do
  let baseCodes := m.funs.foldl (·.insert ·.fid) (∅ : CodeSet) |>.insert m.main.fid
  let (gCodes, outFuns) <-
    m.funs.foldlM (init := (baseCodes, #[])) fun (gCodes, outFuns) f => do
      let (f', lifted) <- closureConvertFun gCodes f
      let outFuns := outFuns.push f'
      return lifted.foldl (init := (gCodes, outFuns)) fun a lf =>
        (a.1.insert lf.fid, a.2.push lf)
  let (main', liftedMain) <- closureConvertFun gCodes m.main
  -- `seq2 f as bs` is `map f as ++ map f bs` but in one go.
  let funs := Array.seq2 (fun lf => {lf with body := optimizeLam lf.body}) outFuns liftedMain
  let main := {main' with body := optimizeLam main'.body}
  return {funs, main}
end

namespace Incremental
structure CCState where
  gensym : Nat
  gCodes : CC.CodeSet
deriving Inhabited

@[inline] def seedWith (st : CCState) (ids : Array Name) : CCState :=
  {st with gCodes := ids.foldl .insert st.gCodes}
@[inline] def seedModule (st : CCState) (m : LModule) : CCState :=
  {st with gCodes := m.funs.foldl (·.insert ·.fid) st.gCodes |>.insert m.main.fid}

def stepFuns (st : CCState) (funs : Array LFun) : (CCState × Array LFun) :=
  let ((gCodes, out), gensym, _) :=
    runST fun _ => (do
      funs.foldlM (init := (st.gCodes, #[])) fun (g, acc) f => do
        let (f, lifted) <- IR.closureConvertFun g f
        let optf := {f with body := IR.optimizeLam f.body}
        let optLifted := lifted.map fun (f : LFun) => {f with body := IR.optimizeLam f.body}
        let g := optLifted.foldl (Std.TreeSet.insert · $ LFun.fid ·) (g.insert f.fid)
        pure (g, (acc : Array LFun).push optf ++ optLifted)).run (st.gensym, ∅)
  ({gensym, gCodes}, out)

def stepExpr (st : CCState) (e : LExpr) : CCState × LExpr × Array LFun :=
  let ((e, lifted), gensym, _) := runST fun _ => (IR.CC.ccExpr st.gCodes e).run (st.gensym, ∅)
  let lifted := lifted.map fun f => {f with body := IR.optimizeLam f.body}
  let gCodes := lifted.foldl (·.insert ·.fid) st.gCodes
  ({gensym, gCodes}, e, lifted)
end Incremental

end IR
