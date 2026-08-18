import Tigris.typing.ttypes

/-! This module simply assigns new mvs to user-supplied binders (TV.named)
    produced by parser, run before typechecking for each TopDecl.
    the counter is seeded from Env.nextTV and continued by CState.next.
    but the map name |-> tv is fresh every call
    since binders are scoped to their declaration.

In short, the counter threading looks like this:

                                  ·---------- <- ---------·
                                  |                       |   ||
                                  ↓                       ↑   ||  (Eliminated)
Env.nextTV (init, 0)   -->   Env.nextTV -> FreshenM -> CState ||  -> FState.
                                  ↑            ↓              ||          \
                                  |            |              ||           \
                                  ·---- <- ----·                            \
                                         \            FState no more carries a counter. We've eliminated its
                                          \           scheme instantiation therefore unification and seeding.
                                           \
                        REPL's #synth query also get freshened.

Since substates (locally to the pass) do not interact with each other, they
update the global Env, we then seed the next substates with the new Env.

The kind system has a separate counter in KindEnv, directly. Though since
we assign default (Type) kvars at parsing time (which has its own counter),
we must merge the two counters, by bumping at declaration-kind inference once:

                                                          max(declared kvars) + 1
PEnv.nxtK (for unannotated) --> TyDecl.param (storing)  --> inferParamKinds
                                                                    |
                                                                    | bump
                                                                    ↓
                                                                 KindEnv

kinds stored in the Env are zonked kvar-free with defaulting rules defaultKV,
so the parser's kvars never persist past the declaration.
-/

abbrev FreshenM σ := StateRefT (Nat × Std.HashMap String TV) (ST σ)

variable {σ}

def freshenTV : TV -> FreshenM σ TV
  | .named s => do
    let (n, m) <- get
    match m[s]? with
    | some tv => return tv
    | none =>
      modify fun (n, m) => (n + 1, m.insert s (.mv n (some s)))
      return .mv n (some s)
  | tv => return tv

/-- a binder: always a fresh mv carrying the source name, shadowing any outer
binder of the same name (binders are scoped to their forall/tylam) -/
def freshenBinder : TV -> FreshenM σ TV
  | .named s => do
    let (n, m) <- get
    let tv := .mv n (some s)
    set (n + 1, m.insert s tv)
    return tv
  | tv => return tv

mutual
partial def freshenT : MLType -> FreshenM σ MLType
  | .TVar v => .TVar <$> freshenTV v
  | t@(.TCon _) => return t
  | a ->' b => (· ->' ·) <$> freshenT a <*> freshenT b
  | a ×'' b => (· ×'' ·) <$> freshenT a <*> freshenT b
  | .TApp h as => .mkApp <$> freshenT h <*> as.mapM freshenT
  | .TyLam x body => do
    let (_, m) <- get
    let x' <- freshenBinder x
    let body' <- freshenT body
    let (n', _) <- get
    set (n', m) -- the binder is scoped to the tylam
    return .TyLam x' body'
  | .TSch sch => .TSch <$> freshenS sch

partial def freshenP : Pred -> FreshenM σ Pred
  | {cls, args} => Pred.mk cls <$> args.mapM freshenT

partial def freshenS : Scheme -> FreshenM σ Scheme
  | .Forall tvs ps t => do
    let (_, m) <- get
    let tvs' <- tvs.mapM freshenBinder
    let ps' <- ps.mapM freshenP
    let t' <- freshenT t
    let (n', _) <- get
    set (n', m) -- the binders are scoped to the forall
    return .Forall tvs' ps' t'

partial def freshenE : Expr -> FreshenM σ Expr
  | c@(.CI ..) | c@(.CS ..) | c@(.CB ..) | c@(.CUnit) | c@(.Var ..) => return c
  | .App e₁ e₂ => .App <$> freshenE e₁ <*> freshenE e₂
  | .Cond c t e => .Cond <$> freshenE c <*> freshenE t <*> freshenE e
  | .Let ae e₂ => .Let <$> ae.mapM (fun (s, e) => (s, ·) <$> freshenE e) <*> freshenE e₂
  | .Fix e => .Fix <$> freshenE e
  | .Fixcomb e => .Fixcomb <$> freshenE e
  | .Fun a e => .Fun a <$> freshenE e
  | .Prod' e₁ e₂ => .Prod' <$> freshenE e₁ <*> freshenE e₂
  | .Match aginst discr =>
    .Match <$> aginst.mapM freshenE <*> discr.mapM (fun (ps, e) => (ps, ·) <$> freshenE e)
  | .Ascribe e ty => .Ascribe <$> freshenE e <*> freshenT ty
end

def freshenTyDecl (ty : TyDecl) : FreshenM σ TyDecl := do
  let param <- ty.param.mapM fun (tv, k) => (·, k) <$> freshenTV tv
  let ctors <- ty.ctors.mapM fun (n, fields, ar) =>
    (n, ·, ar) <$> fields.mapM (fun (f, t) => (f, ·) <$> freshenT t)
  let rhs? <- match ty.rhs with
    | some rhs => some <$> freshenT rhs
    | none => pure none
  return {ty with param, ctors, rhs := rhs?}

def freshenTopDecl : TopDecl -> FreshenM σ TopDecl
  | .idBind group => .idBind <$> group.mapM (fun (s, e) => (s, ·) <$> freshenE e)
  | .patBind (pat, e) => .patBind <$> (pat, ·) <$> freshenE e
  | .tyBind ty => .tyBind <$> freshenTyDecl ty
  | .extBind s n sch => .extBind s n <$> freshenS sch
  | .instBind inst => do
    let ctxPreds <- inst.ctxPreds.mapM freshenP
    let args <- inst.args.mapM freshenT
    let methods <- inst.methods.mapM (fun (n, e) => (n, ·) <$> freshenE e)
    return .instBind {inst with ctxPreds, args, methods}
