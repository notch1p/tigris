import Tigris.parsing.types
import Tigris.core.matchApp
import Tigris.interpreter.entrypoint
import Tigris.typing.typing
import Tigris.core.anf
import Tigris.core.opt

namespace CPS open Expr Pattern

abbrev M σ := StateRefT Nat (ST σ)

@[inline] def fresh (h := "x") : M σ Name := modifyGet fun n => (h ++ toString n, n + 1)
@[inline] def freshLbl (h := "L") : M σ Label := fresh h
@[inline] def freshFun (h := "f") : M σ Label := fresh h

def fvs (B : Std.HashSet String := ∅) : Expr -> Std.HashSet String
  | CI _ | CB _ | CS _ | CUnit => ∅
  | Var x => if x ∈ B then ∅ else {x}
  | App f a => fvs B f ∪ fvs B a
  | Prod' l r => fvs B l ∪ fvs B r
  | Cond c t e => fvs B c ∪ fvs B t ∪ fvs B e
  | Let x e₁ e₂ => fvs B e₁ ∪ fvs (B.insert x) e₂
  | Fix (.Fun x body) | Fixcomb (.Fun x body) => fvs (B.insert x) body
  | Fix e | Fixcomb e => fvs B e
  | .Fun x b => fvs (B.insert x) b
  | Ascribe e _ => fvs B e
  | .Match es rows =>
    let fb := es.foldl (init := ∅) (· ∪ fvs B ·)
    let rec addPat (b : Std.HashSet String) (p : Pattern) : Std.HashSet String :=
      match p with
      | .PVar x => b.insert x
      | .PWild => b
      | .PConst _ => b
      | .PProd' p q => addPat (addPat b p) q
      | .PCtor _ args => args.foldl addPat b
    rows.attach.foldl (init := fb) fun a {val, property} =>
      let ps := val.1; let rhs := val.2
      have : sizeOf val.snd < 1 + sizeOf es + sizeOf rows := by
        have h₁ := Nat.lt_trans (prod_sizeOf_lt val).2 (Array.sizeOf_lt_of_mem property)
        omega
      a ∪ fvs (ps.foldl addPat B) rhs
termination_by e => e

structure FunBuilder where
  fid       : Name
  params    : Array Name
  entry     : Label
  curLbl    : Label
  curParams : Array Name
  curBody   : Array Stmt := #[]
  blocks    : Array Block := #[]
  funs      : Array Fun := #[]
deriving Repr

abbrev BuildM σ := StateRefT FunBuilder (M σ)

@[inline] abbrev liftSig : M σ α -> BuildM σ α := liftM

@[inline] def emit (s : Stmt) : BuildM σ Unit := modify fun b =>
  {b with curBody := b.curBody.push s}
@[inline] def endBlock (t : Term) : BuildM σ Unit :=
  modify fun b@{blocks, curLbl, curParams, curBody,..} =>
    let blocks := blocks.push ⟨curLbl, curParams, curBody, t⟩
    {b with blocks, curBody := #[]}
@[inline] def newBlock (curLbl : Label) (curParams : Array Name) : BuildM σ Unit :=
  modify fun b => {b with curLbl, curParams, curBody := #[]}

def bindRhs (rhs : Rhs) (h := "t") : BuildM σ Name := do
  let x <- liftSig $ fresh h
  emit (.let1 x rhs)
  return x

@[inline] def atomOfConst : Expr -> Option Atom
  | CI i => some ∘ .cst ∘ .int  $ i
  | CB b => some ∘ .cst ∘ .bool $ b
  | CS s => some ∘ .cst ∘ .str  $ s
  | CUnit => some $ .cst .unit
  | _ => none

def realizeSel (roots : Array Name) : Sel -> BuildM σ Name
  | .base i => pure roots[i]!
  | .field s i => do
    let v <- realizeSel roots s
    bindRhs (.proj v i) s!"p{i}"

abbrev Env := Std.TreeMap String Name
@[inline]
def captureList (fv : Std.HashSet String) (exclude : Std.HashSet String) (ρ : Env) : Array (String × Name) :=
  ρ.foldl
    (init := #[])
    (fun acc k v => if fv.contains k && !exclude.contains k then acc.push (k, v) else acc)

mutual
-- lifting closure
partial def emitFunction
  (fid : Name)
  (caps : Array (String × Name))
  (argName : String)
  (selfName? : Option String)
  (body : Expr)
  (kSite : Name)
  : BuildM σ Unit := do
  let capFormalNames : Array Name := caps.map (fun (n, _) => s!"env_{n}")
  let argFormal : Name := s!"{argName}"
  let kFormal   : Name := s!"k"
  let entryLbl  <- liftSig <| freshLbl (fid ++ "_entry")

  let initInner : FunBuilder :=
    { fid := fid
    , params := capFormalNames ++ #[argFormal, kFormal]
    , entry := entryLbl
    , curLbl := entryLbl
    , curParams := capFormalNames ++ #[argFormal, kFormal]
    , curBody := #[]
    , blocks := #[]
    , funs := #[]}

  let (_, inner) <- liftSig $ (do
    let sz := Nat.min capFormalNames.size caps.size
    have : sz <= capFormalNames.size := Nat.min_le_left ..
    have : sz <= caps.size := Nat.min_le_right ..
    let rhoBody :=
      (sz.fold (init := (∅ : Env)) fun i h (a : Env) =>
        a.insert caps[i].1 capFormalNames[i]).insert argName argFormal
    let rhoBody <-
      match selfName? with
      | some selfN =>
        let selfValName <- bindRhs (.mkClosure fid capFormalNames) "self"
        pure $ rhoBody.insert selfN selfValName
      | none => pure rhoBody

    compileWithEnv body rhoBody kFormal
  ).run initInner

  modify fun (b : FunBuilder) =>
    let f : Fun :=
        { fid    := fid
        , params := inner.params
        , blocks := inner.blocks
        , entry  := inner.entry}
    {b with funs := b.funs ++ inner.funs.push f}

  -- materialize the closure with actual captured values and pass to kSite.
  let envActuals : Array Name := caps.map (·.2)
  let clo <- bindRhs (.mkClosure fid envActuals) "clo"
  endBlock (.appCont kSite (.var clo))

partial def compileWithEnv (e : Expr) (ρ : Env) (k : Name) : BuildM σ Unit := do
  match e with
  | .Var x => endBlock (.appCont k (.var (ρ.getD x x)))

  | .CI i => endBlock (.appCont k (.cst (.int i)))
  | .CB b => endBlock (.appCont k (.cst (.bool b)))
  | .CS s => endBlock (.appCont k (.cst (.str s)))
  | .CUnit => endBlock (.appCont k (.cst .unit))

  | .App (.Var fv) (.Var av) =>
    let f := ρ.getD fv fv
    let a := ρ.getD av av
    endBlock (.appFun f a k)

  | .App f a => do
    let lblF <- liftSig <| freshLbl "KF"
    let kF   <- bindRhs (.mkKont lblF #[]) "kF"
    compileWithEnv f ρ kF
    newBlock lblF #[]
    let vparam <- liftSig <| fresh "vf"
    modify fun b => {b with curParams := #[vparam]}
    let lblA <- liftSig <| freshLbl "KA"
    let kA   <- bindRhs (.mkKont lblA #[]) "kA"
    compileWithEnv a ρ kA
    newBlock lblA #[]
    let aparam <- liftSig <| fresh "va"
    modify fun b => {b with curParams := #[aparam]}
    endBlock (.appFun vparam aparam k)

  | .Prod' l r => do
    let lblL <- liftSig <| freshLbl "KL"
    let kL   <- bindRhs (.mkKont lblL #[]) "kL"
    compileWithEnv l ρ kL
    newBlock lblL #[]
    let lv <- liftSig <| fresh "lv"; modify fun b => {b with curParams := #[lv]}
    let lblR <- liftSig <| freshLbl "KR"
    let kR   <- bindRhs (.mkKont lblR #[]) "kR"
    compileWithEnv r ρ kR
    newBlock lblR #[]
    let rv <- liftSig <| fresh "rv"; modify fun b => {b with curParams := #[rv]}
    let p <- bindRhs (.mkPair lv rv) "p"
    endBlock (.appCont k (.var p))

  | .Let x e₁ e₂ => do
    let lbl <- liftSig <| freshLbl "let"
    let k1  <- bindRhs (.mkKont lbl #[]) "k1"
    compileWithEnv e₁ ρ k1
    newBlock lbl #[x]
    compileWithEnv e₂ (ρ.insert x x) k

  | .Cond c t e' => do
    let lblC <- liftSig <| freshLbl "KC"
    let kC   <- bindRhs (.mkKont lblC #[]) "kC"
    compileWithEnv c ρ kC
    newBlock lblC #[]
    let cv <- liftSig <| fresh "cv"; modify fun b => {b with curParams := #[cv]}
    let lt <- liftSig <| freshLbl "then"
    let le <- liftSig <| freshLbl "else"
    endBlock (.ifGoto cv lt le)
    newBlock lt #[]
    compileWithEnv t ρ k
    newBlock le #[]
    compileWithEnv e' ρ k

  | .Fix (.Fun fname fbody) | .Fixcomb (.Fun fname fbody) =>
    let fv := fvs ∅ e
    let exclude := Std.HashSet.insert ∅ fname
    let caps := captureList fv exclude ρ
    match fbody with
    | .Fun x body =>
      emitFunction (fid := fname) (caps := caps) (argName := x) (selfName? := some fname)
                   (body := body) (kSite := k)
    | _ =>
      emitFunction (fid := fname) (caps := caps) (argName := "arg") (selfName? := some fname)
                   (body := fbody) (kSite := k)
  | .Fix e | .Fixcomb e =>
    compileWithEnv e ρ k

  | .Fun x body =>
    let fv := fvs ∅ e
    let exclude := Std.HashSet.insert ∅ x
    let caps := captureList fv exclude ρ
    let fid  <- liftSig <| freshFun "lam"
    emitFunction (fid := fid) (caps := caps) (argName := x) (selfName? := none)
                 (body := body) (kSite := k)

  | .Ascribe e _ =>
    compileWithEnv e ρ k

  | .Match es rows =>
    compileMatchDT es rows ρ k
partial def compileMatchDT (es : Array Expr) (rows : Array (Array Pattern × Expr)) (ρ : Env) (k : Name) : BuildM σ Unit := do
  let mut scrs : Array Name := #[]
  for e in es do
    let lbl <- liftSig <| freshLbl "KS"
    let kS  <- bindRhs (.mkKont lbl #[]) "kS"
    compileWithEnv e ρ kS
    newBlock lbl #[]
    let v <- liftSig <| fresh "s"
    modify fun b => {b with curParams := #[v]}
    scrs := scrs.push v
  let cols : Array Sel := Array.ofFn (Sel.base ∘ Fin.toNat (n := scrs.size))

  let rws : Array RowState :=
    rows.map (fun (ps, rhs) => RowState.mk ps rhs #[])

  let dt := buildTree cols rws
  lowerTree dt scrs cols ρ k

partial def lowerTree (t : DTree) (roots : Array Name) (cols : Array Sel) (ρ : Env) (k : Name) : BuildM σ Unit := do
  match t with
  | .fail =>
    endBlock (.appCont k (.cst .unit))
  | .leaf row =>
    (compileWithEnv row.rhs · k) =<< row.binds.foldlM (init := ρ) fun ρ (x, s) =>
      ρ.insert x <$> realizeSel roots s

  | .splitProd j next =>
    let s := cols[j]!
    let cols' := cols[0:j] ++ #[Sel.field s 0, Sel.field s 1] ++ cols[j+1:]
    lowerTree next roots cols' ρ k

  | .testConst j branches defs? =>
    let sv <- realizeSel roots cols[j]!
    let rec go (i : Nat) : BuildM σ Unit := do
      if h : i < branches.size then
        let (tc, sub) := branches[i]
        let (op, atom) :=
          match tc with
          | .PInt n  => (PrimOp.eqInt, Atom.cst (.int n))
          | .PBool b => (PrimOp.eqBool, Atom.cst (.bool b))
          | .PStr s  => (PrimOp.eqStr, Atom.cst (.str s))
          | .PUnit   => (PrimOp.eqInt, Atom.cst (.int 0))
        let c <- bindRhs (.prim op #[.var sv, atom]) "cmp"
        let lthen <- liftSig <| freshLbl "k_then"
        let lelse <- liftSig <| freshLbl "k_else"
        endBlock (.ifGoto c lthen lelse)
        newBlock lthen #[]
        let cols' := cols.eraseIdx! j
        lowerTree sub roots cols' ρ k
        newBlock lelse #[]
        go (i+1)
      else
        match defs? with
        | some defsub =>
          let cols' := cols.eraseIdx! j
          lowerTree defsub roots cols' ρ k
        | none =>
          -- fallthrough fail
          let d <- bindRhs (.prim .add #[.cst (.int 0), .cst (.int 0)]) "dead"
          endBlock (.appCont k (.cst .unit))
    go 0

  | .testCtor j branches defs? =>
    let sv <- realizeSel roots cols[j]!
    let (alts, caseWork) <- branches.foldlM (init := (#[], #[]))
      fun ( (alts : Array (Name × Nat × Label × Array Name))
          , (caseWork : Array (Label × (BuildM σ Unit))))
          (cname, ar, subtree) => do
        let lbl <- liftSig <| freshLbl s!"case_{cname}"
        letI cols' :=
          cols[0:j]
          ++ Array.ofFn (Sel.field cols[j]! ∘ Fin.toNat (n := ar))
          ++ cols[j+1:]
        pure
          ( alts.push (cname, ar, lbl, #[])
          , caseWork.push (lbl, lowerTree subtree roots cols' ρ k))
    let defLbl? <-
      match defs? with
      | some subtree =>
        let lbl <- liftSig <| freshLbl "case_default"
        let cols' := cols.eraseIdx! j
        let work := lowerTree subtree roots cols' ρ k
        pure (some (lbl, work))
      | none => pure none
    let defTerm? :=
      defLbl?.map fun (l, _) => (l, #[])
    endBlock (.switchCtor sv alts defTerm?)
    for (lbl, work) in caseWork do
      newBlock lbl #[]
      work
    match defLbl? with
    | some (lbl, work) =>
      newBlock lbl #[]
      work
    | none => pure ()

end

def compileToMain (e : Expr) : M σ Module := do
  let e := runST fun _ => ANF.normalize e |>.run' 0
  let entry <- freshLbl "main_entry"
  let k <- fresh "k"
  let init : FunBuilder :=
    { fid := "main"
    , params := #[k]
    , entry := entry
    , curLbl := entry
    , curParams := #[k]
    , curBody := #[]
    , blocks := #[]
    , funs := #[]}
  let (_, st) <-
    (do
      let lblH <- liftSig <| freshLbl "haltK"
      let kH   <- bindRhs (.mkKont lblH #[]) "kH"
      compileWithEnv e ∅ kH
      newBlock lblH #[]
      let r <- liftSig <| fresh "res";
      modify fun (b : FunBuilder) => {b with curParams := #[r]}
      endBlock (.halt r)
    ).run init

  let mainFun := { fid := "main"
                 , params := #[k]
                 , blocks := st.blocks
                 , entry := entry}
  pure (optModule ⟨st.funs, mainFun⟩)

def compile1 (s : String) (PE : PEnv) (E : _root_.Env) : IO Unit := do
  try
    let e <- IO.ofExcept $ Parsing.parse s PE
    let (_, l) <- IO.ofExcept $ MLType.runInfer1 e E
    let (m, _) := runST fun _ => compileToMain e |>.run 0
    IO.print l
    IO.println $ (Std.Format.pretty ∘ fmtModule) m
  catch e => IO.println (Logging.error $ toString e)

end CPS
open CPS in
def compileTop (decls : Array Parsing.TopDecl) : M σ Module := do
  let entry <- freshLbl "main_entry"
  let k <- fresh "k"
  let init : FunBuilder :=
    { fid := "main"
    , params := #[k]
    , entry := entry
    , curLbl := entry
    , curParams := #[k]
    , curBody := #[]
    , blocks := #[]
    , funs := #[] }
  let (_, {funs, blocks,..}) <- StateRefT'.run (s := init) $ show BuildM σ Unit from do
    let lblH <- liftSig $ freshLbl "haltK"
    let kH <- bindRhs (.mkKont lblH #[]) "kH"
    let (ρ, lastName?) <- decls.foldlM (init := show CPS.Env × Option Name from (∅, none))
      fun a@(ρ, _) d => do
        match d with
        | .inr _ => return a
        | .inl (id, e) =>
          let eANF := runST fun _ => ANF.normalize e |>.run' 0
          let lbl <- liftSig $ freshLbl s!"top_{id}"
          let kTop <- bindRhs (.mkKont lbl #[]) s!"k_{id}"
          compileWithEnv eANF ρ kTop
          newBlock lbl #[]
          modify fun b => {b with curParams := #[id]}
          return (ρ.insert id id, some id)
    if let some v := ρ.get? "main" <|> lastName? then
      endBlock (.appCont kH (.var v))
    else endBlock (.appCont kH (.cst .unit))

    newBlock lblH #[]
    let r <- liftSig $ fresh "res"
    modify fun b => {b with curParams := #[r]}
    endBlock (.halt r)

  let mainFun : Fun :=
    {fid := "main", params := #[k], blocks, entry}
  return (optModule ⟨funs, mainFun⟩)
