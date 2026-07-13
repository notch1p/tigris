import Tigris.oldcps.cps
import Tigris.oldcore2.transform
import Tigris.oldcps.copt

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

def shapeOfCRhs (Γ : ShapeMap) : CRhs -> Shape
  | .prim ..        => .unknown
  | .isConstr ..    => .unknown
  | .const _        => .unknown
  | .mkPair _ _     => .pair
  | .mkConstr t fs  => .ctor t fs.size
  | .alias y        => Γ.getD y .unknown
  | .proj s i =>
    match Γ.getD s .unknown with
    | .ctor "𝐂" _ => if i == 0 then .fn else .unknown
    | _ => .unknown

mutual
partial def cpsBinds
  (ρ : Ren) (Γ : ShapeMap)
  (binds : Array Stmt) (tail : Tail) (kret : CName) : M σ CExpr :=
  go 0 ρ Γ where
  go i ρ Γ := do
    if h : i < binds.size then
      match binds[i] with
      | .let1 x (.call f a) =>
        let v <- fresh "v"
        let kid <- fresh "k"
        -- The call result's shape was set on `x` by ftransform / lift.
        let vSh <- IR.getShape x
        IR.setShape v vSh
        let rest <- go (i + 1) (ρ.insert x v) (Γ.insert v vSh)
        return .letKont kid v rest $ .tail $
          .appFun (rn ρ f) (rn ρ a) kid
      | .let1 x r =>
        let rhs := lowerPureRhs ρ r
        let sh := shapeOfCRhs Γ rhs
        IR.setShape x sh
        .let1 x sh rhs <$> go (i + 1) ρ (Γ.insert x sh)
    else cpsTail ρ Γ tail kret

partial def cpsTail (ρ : Ren) (Γ : ShapeMap) : Tail -> CName -> M σ CExpr
  | .matchFail pat, _ => return .tail $ .matchFail pat
  | .ret x, kret => return .tail $ .appKont kret $ rn ρ x
  | .app f a, kret => return .tail $ .appFun (rn ρ f) (rn ρ a) kret
  | .cond c t e, kret => do
    let t <- cpsExpr ρ Γ t kret
    let e <- cpsExpr ρ Γ e kret
    return .tail $ .ite (rn ρ c) t e
  | .switchConst s cases d?, kret => do
    let cases <- cases.mapM fun (k, b) =>
      (k, ·) <$> cpsExpr ρ Γ b kret
    let d <- d?.mapM (cpsExpr ρ Γ · kret)
    return .tail $ .switchConst (rn ρ s) cases d
  | .switchCtor s cases d?, kret => do
    let s' := rn ρ s
    let cases <- cases.mapM fun (c, ar, b) =>
      let Γ' := Γ.insert s' (.ctor c ar)
      (c, ar, ·) <$> cpsExpr ρ Γ' b kret
    let d <- d?.mapM (cpsExpr ρ Γ · kret)
    return .tail $ .switchCtor s' cases d

partial def cpsExpr (ρ : Ren) (Γ : ShapeMap) : LExpr -> CName -> M σ CExpr
  | .seq binds tail, kret =>
    cpsBinds ρ Γ binds tail kret
  | .letVal x (.var y) b, kret =>
    let y' := rn ρ y
    let Γ' := Γ.insert x (Γ.getD y' .unknown)
    cpsExpr (ρ.insert x y') Γ' b kret
  | .letVal x v b, kret => do
    let rhs := lowerValue ρ v
    let sh := shapeOfCRhs Γ rhs
    let preset <- IR.getShape x
    let sh := if preset == .unknown then sh else preset
    IR.setShape x sh
    .let1 x sh rhs <$> cpsExpr ρ (Γ.insert x sh) b kret
  | .letRhs x (.call f a) b, kret => do
    let v <- fresh "v"
    let kid <- fresh "k"
    -- Inherit the call-result shape recorded on `x` by ftransform.
    let xSh <- IR.getShape x
    IR.setShape v xSh
    let cont <- cpsExpr (ρ.insert x v) (Γ.insert v xSh) b kret
    return .letKont kid v cont $ .tail $ .appFun (rn ρ f) (rn ρ a) kid
  | .letRhs x r b, kret => do
    let rhs := lowerPureRhs ρ r
    let sh := shapeOfCRhs Γ rhs
    let preset <- IR.getShape x
    let sh := if preset == .unknown then sh else preset
    IR.setShape x sh
    .let1 x sh rhs <$> cpsExpr ρ (Γ.insert x sh) b kret
  | .letRec funs b , kret => do
    let funs <- funs.mapM fun (f : LFun) => do
      let k <- fresh "k"
      let pSh := f.paramShape
      -- seed shape env with the param's shape inside fbody
      let Γf : ShapeMap := Std.HashMap.insert ∅ f.param pSh
      let body <- cpsExpr ∅ Γf f.body k
      return {fid := f.fid, payloadParam := f.param, payloadShape := pSh, kontParam := k, body}
    .letRec funs <$> cpsExpr ρ Γ b kret
end

def cpsFun (f : LFun) : M σ CFun := do
  let k := "k"
  let pSh := f.paramShape
  let Γ : ShapeMap := Std.HashMap.insert ∅ f.param pSh
  let body <- cpsExpr ∅ Γ f.body k
  return {fid := f.fid, payloadParam := f.param, payloadShape := pSh, kontParam := k, body}

def cpsModule : LModule -> M σ CModule
  | {funs, main, ..} =>
    CModule.mk <$> funs.mapM cpsFun <*> cpsFun main
    |> Functor.map CPS.optimizeCModule

@[inline] def toCPS (m : LModule) : CModule :=
  runST fun _ => cpsModule m |>.run' (0, ∅, m.shapes)

def addEntrypoint (m : CModule) (useUnit? := true) : CModule :=
  let startFid := "__start"
  let payload := "p0"
  let kIgn    := "_k"
  let haltKid := "__halt"
  let v       := "v"
  let argName := "arg0"
  let argBind : CExpr -> CExpr :=
    if useUnit? then fun body => .let1 argName .unknown (.const .unit) body
    else fun body => .let1 argName .unknown (.alias payload) body
  let entryBody :=
    .letKont haltKid v (.tail $ (.halt v))
      $ argBind
      $ .tail
      $ .appFun m.main.fid argName haltKid
  let startFun : CFun :=
    {fid := startFid, payloadParam := payload, payloadShape := .unknown
    , kontParam := kIgn, body := entryBody}
  ⟨m.funs.push m.main, startFun⟩

end CPS
