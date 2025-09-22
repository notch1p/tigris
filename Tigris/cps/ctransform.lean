import Tigris.cps.cps
import Tigris.core.transform
import Tigris.cps.copt

namespace CPS open IR (M Rhs LExpr Stmt Tail LFun LModule)
variable {σ}
@[inline] def rn (ρ : Ren) (x : CName) : CName := ρ.getD x x
nonrec def fresh (h := "cps") : M σ CName := IR.fresh h

def lowerPureRhs (ρ : Ren) : Rhs -> CRhs
  | .prim op args    => .prim op (args.map (rn ρ))
  | .proj s i        => .proj (rn ρ s) i
  | .mkPair a b      => .mkPair (rn ρ a) (rn ρ b)
  | .mkConstr t fs   => .mkConstr t (fs.map (rn ρ))
  | .isConstr s t ar => .isConstr (rn ρ s) t ar
  | .call _ _ => panic! "calls shouldn't be handled here"

def lowerValue (ρ : Ren) : IR.Value -> CRhs
  | .var x       => .alias (rn ρ x)
  | .cst k       => .const k
  | .constr t fs => .mkConstr t (fs.map (rn ρ))
  | .lam ..      => panic! "unexpected lambda after CC"


mutual
partial def cpsBinds (ρ : Ren) (binds : Array Stmt) (tail : Tail) (kret : CName) : M σ CExpr :=
  go 0 ρ where
  go i ρ := do
    if h : i < binds.size then
      match binds[i] with
      | .let1 x (.call f a) =>
        let v <- fresh "v"
        let kid <- fresh "k"
        let rest <- go (i + 1) (ρ.insert x v)
        return .letKont kid v rest $ .tail $
          .appFun (rn ρ f) (rn ρ a) kid
      | .let1 x r =>
        let rhs := lowerPureRhs ρ r
        .let1 x rhs <$> go (i + 1) ρ
    else cpsTail ρ tail kret

partial def cpsTail (ρ : Ren) : Tail -> CName -> M σ CExpr
  | .ret x, kret => return .tail $ .appKont kret $ rn ρ x
  | .app f a, kret => return .tail $ .appFun (rn ρ f) (rn ρ a) kret
  | .cond c t e, kret => do
    let t <- cpsExpr ρ t kret
    let e <- cpsExpr ρ e kret
    return .tail $ .ite (rn ρ c) t e
  | .switchConst s cases d?, kret => do
    let cases <- cases.mapM fun (k, b) =>
      (k, ·) <$> cpsExpr ρ b kret
    let d <- d?.mapM (cpsExpr ρ · kret)
    return .tail $ .switchConst (rn ρ s) cases d
  | .switchCtor s cases d?, kret => do
    let cases <- cases.mapM fun (c, ar, b) =>
      (c, ar, ·) <$> cpsExpr ρ b kret
    let d <- d?.mapM (cpsExpr ρ · kret)
    return .tail $ .switchCtor (rn ρ s) cases d

partial def cpsExpr (ρ : Ren) : LExpr -> CName -> M σ CExpr
  | .seq binds tail, kret =>
    cpsBinds ρ binds tail kret
  | .letVal x (.var y) b, kret =>
    cpsExpr (ρ.insert x (rn ρ y)) b kret
  | .letVal x v b, kret =>
    let rhs := lowerValue ρ v
    .let1 x rhs <$> cpsExpr ρ b kret
  | .letRhs x (.call f a) b, kret => do
    let v <- fresh "v"
    let kid <- fresh "k"
    let cont <- cpsExpr (ρ.insert x v) b kret
    return .letKont kid v cont $ .tail $ .appFun (rn ρ f) (rn ρ a) kid
  | .letRhs x r b, kret =>
    let rhs := lowerPureRhs ρ r
    .let1 x rhs <$> cpsExpr ρ b kret
  | .letRec funs b , kret => do
    let funs <- funs.mapM fun {fid, param, body} => do
      let k <- fresh "k"
      let body <- cpsExpr ∅ body k
      return ⟨fid, param, k, body⟩
    .letRec funs <$> cpsExpr ρ b kret
end

def cpsFun : LFun -> M σ CFun
  | {fid, param, body} =>
    letI k := "k"
    CFun.mk fid param k <$> cpsExpr ∅ body k

def cpsModule : LModule -> M σ CModule
  | {funs, main} =>
    CModule.mk <$> funs.mapM cpsFun <*> cpsFun main
    -- |> Functor.map CPS.optimizeCModule

@[inline] def toCPS (m : LModule) : CModule :=
  runST fun _ => cpsModule m |>.run' 0

def addEntrypoint (m : CModule) (useUnit? := true) : CModule :=
  let startFid := "__start"
  let payload := "p0"
  let kIgn    := "_k"
  let haltKid := "__halt"
  let v       := "v"
  let argName := "arg0"
  let argBind : CExpr -> CExpr :=
    if useUnit? then fun body => .let1 argName (.const .unit) body
    else fun body => .let1 argName (.alias payload) body
  let entryBody :=
    .letKont haltKid v (.tail $ (.halt v))
      $ argBind
      $ .tail
      $ .appFun m.main.fid argName haltKid
  let startFun : CFun := ⟨startFid, payload, kIgn, entryBody⟩
  ⟨m.funs.push m.main, startFun⟩

end CPS
