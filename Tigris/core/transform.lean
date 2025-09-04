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

/-- A defunctionalized continuation case:
  - tag: constructor name used to encode this continuation
  - payloadKeys: variable names (source-level names) captured in order in the payload
  - targetLbl: static label to jump to when applying this continuation
  - targetArgs: original argument atoms (variables by name, constants) to pass to targetLbl, plus the result (which we’ll append at apply-time)
-/
structure KCase where
  tag        : Name
  payloadKeys : Array String
  targetLbl  : Label
  targetArgs : Array Atom
deriving Repr, Inhabited

structure FunBuilder where
  fid       : Name
  params    : Array Name
  entry     : Label
  curLbl    : Label
  curParams : Array Name
  curBody   : Array Stmt := #[]
  blocks    : Array Block := #[]
  funs      : Array Fun := #[]
  kcases    : Array KCase := #[]
  retBridges : Std.HashSet Label := ∅
deriving Repr

abbrev BuildM σ := StateRefT FunBuilder (M σ)

variable {σ}

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

abbrev Cont := Label × Array Atom

def boundVarsOfPatterns (ps : Array Pattern) : Std.HashSet String :=
  ps.foldl add ∅ where
  add (s : Std.HashSet String) : Pattern -> Std.HashSet String
  | .PVar x      => s.insert x
  | .PWild       => s
  | .PConst _    => s
  | .PProd' p q  => add (add s p) q
  | .PCtor _ as  => as.foldl add s

private def makeContValue (kSite : Cont) (ρ : Env) : BuildM σ Name := do
  let (kLbl, kAs) := kSite
  let rb <- get
  let isRetBridge := rb.retBridges.contains kLbl
  if isRetBridge && kAs.isEmpty then
    pure (ρ.getD "k" "k")
  else
    let varPairs0 : Array (String × Name) :=
      kAs.foldl (init := #[]) (fun acc a =>
        match a with
        | .var x => acc.push (x, ρ.getD x x)
        | .cst _ => acc)
    let (varPairs, _) :=
      varPairs0.foldl (init := (#[], (∅ : Std.HashSet String))) (fun (acc, seen) (nm, v) =>
        if seen.contains nm then (acc, seen) else (acc.push (nm, v), seen.insert nm))
    let tag <- liftSig <| freshFun "K"
    let envActuals : Array Name := varPairs.map (·.2)
    let kVal <- bindRhs (.mkConstr tag envActuals) "k"
    modify fun b =>
      let kc : KCase := { tag := tag, payloadKeys := varPairs.map (·.1), targetLbl := kLbl, targetArgs := kAs }
      { b with kcases := b.kcases.push kc }
    pure kVal

private def buildKApply (kcases : Array KCase) : M σ Fun := do
  let fid := "kapply"
  let entry <- freshLbl "kapply_entry"
  let (_, st) <- StateRefT'.run (s := ({ fid := fid
                                         , params := #["k","ret"]
                                         , entry := entry
                                         , curLbl := entry
                                         , curParams := #["k","ret"]
                                         , curBody := #[]
                                         , blocks := #[]
                                         , funs := #[]
                                         , kcases := #[] } : FunBuilder)) do
    -- Switch on k; pass along (k, ret) to each case handler
    let alts : Array (Name × Nat × Label × Array Name) <- do
      kcases.foldlM (init := #[]) fun acc kc => do
        let caseLbl <- liftSig <| freshLbl s!"k_case_{kc.tag}"
        pure $ acc.push (kc.tag, kc.payloadKeys.size, caseLbl, #["k","ret"])
    endBlock (.switchCtor "k" alts none)
    -- Emit handlers: extract payload fields and jump to targetLbl with targetArgs ++ [ret]
    kcases.forM fun kc => do
      let caseLbl := s!"k_case_{kc.tag}"
      newBlock caseLbl #["k","ret"]
      -- extract payload fields from k
      let roots := #["k"]
      let payloadVals <- kc.payloadKeys.foldlM (init := #[]) fun a _ => do
        let i := a.size
        let v <- realizeSel roots (.field (.base 0) i)
        pure (a.push v)
      -- build args to target label by mapping targetArgs atoms
      let args : Array Atom :=
        kc.targetArgs.map (fun
          | .var x =>
              match kc.payloadKeys.idxOf? x with
              | some idx => .var payloadVals[idx]!
              | none     => .var x -- fallback (should not happen)
          | .cst k => .cst k)
      endBlock (.goto kc.targetLbl (args.push (.var "ret")))
  pure { fid := fid, params := #["k","ret"], blocks := st.blocks, entry := entry }

private def primOfName : Name -> Option PrimOp
  | "add" => some .add | "sub" => some .sub
  | "mul" => some .mul | "div" => some .div
  | _     => none

private def matchBinaryPrim : Expr -> Option (PrimOp × Expr × Expr)
  | .App (.App (.Var f) x) y =>
      match primOfName f with
      | some op => some (op, x, y)
      | none    => none
  | _ => none

mutual
-- lifting closure
partial def emitFunction
  (fid : Name)
  (caps : Array (String × Name))
  (argName : String)
  (selfName? : Option String)
  (body : Expr)
  (kSite : Cont)
  : BuildM σ Unit := do
  let (kLbl, kAs) := kSite
  let kVarCaps : Array (String × Name) :=
    kAs.foldl (init := #[]) (fun acc a =>
      match a with
      | .var x => acc.push (x, x)
      | .cst _ => acc)
  let addIfNew (seen : Std.HashSet String) (acc : Array (String × Name)) (p : String × Name)
    : (Array (String × Name) × Std.HashSet String) :=
    let (nm, _) := p
    if seen.contains nm then (acc, seen) else (acc.push p, seen.insert nm)
  let (capsAll, _) :=
    let (acc, seen) := caps.foldl (init := (#[], (∅ : Std.HashSet String))) fun (acc, seen) c =>
      addIfNew seen acc c
    kVarCaps.foldl (init := (acc, seen)) fun (acc, seen) kv =>
      addIfNew seen acc kv

  let capFormalNames : Array Name := capsAll.map (fun (n, _) => s!"env_{n}")
  let argFormal : Name := s!"{argName}"
  let kFormal   : Name := "k"
  let entryLbl  <- liftSig <| freshLbl (fid ++ "_entry")
  let retBridge <- liftSig <| freshLbl (fid ++ "_ret")

  let initInner : FunBuilder :=
    { fid := fid
    , params := (capFormalNames.push argFormal).push kFormal
    , entry := entryLbl
    , curLbl := entryLbl
    , curParams := (capFormalNames.push argFormal).push kFormal
    , curBody := #[]
    , blocks := #[]
    , funs := #[]
    , kcases := #[] }

  let (_, inner) <- liftSig $ (do
    let sz := Nat.min capFormalNames.size capsAll.size
    have : sz <= capFormalNames.size := Nat.min_le_left ..
    have : sz <= capsAll.size := Nat.min_le_right ..
    let rhoBody :=
      ((sz.fold (init := (∅ : Env)) fun i _ (a : Env) =>
        a.insert capsAll[i].1 capFormalNames[i]).insert argName argFormal).insert "k" kFormal
    let rhoBody <-
      match selfName? with
      | some selfN =>
        let selfValName <- bindRhs (.mkClosure fid capFormalNames) "self"
        pure $ rhoBody.insert selfN selfValName
      | none => pure rhoBody

    compileWithEnv body rhoBody (retBridge, #[])

    newBlock retBridge #[]
    let rv <- liftSig <| fresh "ret"
    modify fun (b : FunBuilder) => { b with curParams := #[rv] }
    endBlock (.goto "kapply_entry" #[.var "k", .var rv])
  ).run initInner

  modify fun (b : FunBuilder) =>
    let f : Fun :=
        { fid := fid
        , params := inner.params
        , blocks := inner.blocks
        , entry := inner.entry}
    {b with funs := b.funs ++ inner.funs.push f
          , kcases := b.kcases ++ inner.kcases
          , retBridges := b.retBridges.insert retBridge}

  let envActuals : Array Name := capsAll.map (·.2)
  let clo <- bindRhs (.mkClosure fid envActuals) "clo"
  endBlock (.goto kLbl (kAs.push (.var clo)))

partial def compileWithEnv
  (e : Expr) (ρ : Env) (kCont : Cont) : BuildM σ Unit := do

  match matchBinaryPrim e with
  | some (op, x, y) => do
      let lX <- liftSig <| freshLbl "KPX"; compileWithEnv x ρ (lX, #[])
      newBlock lX #[]
      let vx <- liftSig <| fresh "vx"; modify fun b => { b with curParams := #[vx] }
      let lY <- liftSig <| freshLbl "KPY"; compileWithEnv y ρ (lY, #[])
      newBlock lY #[]
      let vy <- liftSig <| fresh "vy"; modify fun b => { b with curParams := #[vy] }
      let r <- bindRhs (.prim op #[.var vx, .var vy]) "p"
      let (kLbl, kAs) := kCont
      endBlock (.goto kLbl (kAs.push (.var r)))
      return ()
  | none => pure ()

  let (kLbl, kAs) := kCont
  match e with
  | .Var x =>
    endBlock (.goto kLbl (kAs.push (.var (ρ.getD x x))))

  | .CI i    => endBlock (.goto kLbl (kAs.push (.cst (.int i))))
  | .CB b    => endBlock (.goto kLbl (kAs.push (.cst (.bool b))))
  | .CS s    => endBlock (.goto kLbl (kAs.push (.cst (.str s))))
  | .CUnit   => endBlock (.goto kLbl (kAs.push (.cst .unit)))

  | .App (.Var fv) (.Var av) => -- direct CALL if both are variables
    let kVal <- makeContValue (kLbl, kAs) ρ
    let f := ρ.getD fv fv
    let a := ρ.getD av av
    endBlock (.appFun f a kVal)

  | .App f a => do
    let lF <- liftSig <| freshLbl "KF"
    let lA <- liftSig <| freshLbl "KA"

    compileWithEnv f ρ (lF, #[])
    newBlock lF #[]
    let vf <- liftSig <| fresh "vf"
    modify fun b => { b with curParams := #[vf] }

    compileWithEnv a ρ (lA, #[])
    newBlock lA #[]
    let va <- liftSig <| fresh "va"
    modify fun b => { b with curParams := #[va] }

    let kVal <- makeContValue (kLbl, kAs) ρ

    endBlock (.appFun vf va kVal)

  | .Prod' l r => do
    let lL <- liftSig <| freshLbl "KL"
    let rL <- liftSig <| freshLbl "KR"
    compileWithEnv l ρ (lL, #[])
    newBlock lL #[]
    let lv <- liftSig <| fresh "lv"; modify fun b => { b with curParams := #[lv] }
    compileWithEnv r ρ (rL, #[])
    newBlock rL #[]
    let rv <- liftSig <| fresh "rv"; modify fun b => { b with curParams := #[rv] }
    let p <- bindRhs (.mkPair lv rv) "p"
    endBlock (.goto kLbl (kAs.push (.var p)))

  | .Let x e₁ e₂ => do
    let l <- liftSig <| freshLbl "let"
    let fv2 := fvs ∅ e₂
    let exclude := Std.HashSet.insert ∅ x
    let caps := captureList fv2 exclude ρ
    let capFormals := caps.map (·.1)
    let capActuals := caps.map $ Atom.var ∘ Prod.snd

    let varsFromKAs : Array Name :=
      kAs.foldl (init := #[]) (fun acc atom =>
        match atom with
        | .var n => acc.push n
        | .cst _ => acc)

    let (allFormals, _) :=
      (capFormals ++ varsFromKAs).foldl
        (init := (#[], (∅ : Std.HashSet Name)))
        (fun (acc, seen) n =>
          if seen.contains n then (acc, seen) else (acc.push n, seen.insert n))
    let extraActuals := varsFromKAs.map Atom.var
    compileWithEnv e₁ ρ (l, capActuals ++ extraActuals)
    newBlock l (allFormals.push x)

    let ρ' :=
      let ρx := ρ.insert x x
      allFormals.foldl (init := ρx) (fun acc n => acc.insert n n)

    compileWithEnv e₂ ρ' (kLbl, kAs)

  | .Cond c t e' => do
    let lc <- liftSig <| freshLbl "KC"
    compileWithEnv c ρ (lc, #[])
    newBlock lc #[]
    let cv <- liftSig <| fresh "cv"; modify fun b => { b with curParams := #[cv] }
    let lt <- liftSig <| freshLbl "then"
    let le <- liftSig <| freshLbl "else"
    endBlock (.ifGoto cv lt le)
    newBlock lt #[]
    compileWithEnv t ρ (kLbl, kAs)
    newBlock le #[]
    compileWithEnv e' ρ (kLbl, kAs)

  | .Fix (.Fun fname fbody) | .Fixcomb (.Fun fname fbody) =>
    let fv := fvs ∅ e
    let exclude := Std.HashSet.insert ∅ fname
    let caps := captureList fv exclude ρ
    match fbody with
    | .Fun x body =>
      emitFunction (fid := fname) (caps := caps) (argName := x) (selfName? := some fname)
                   (body := body) (kSite := (kLbl, kAs))
    | _ =>
      emitFunction (fid := fname) (caps := caps) (argName := "arg") (selfName? := some fname)
                   (body := fbody) (kSite := (kLbl, kAs))
  | .Fix e | .Fixcomb e =>
    compileWithEnv e ρ (kLbl, kAs)

  | .Fun x body =>
    let fv := fvs ∅ e
    let exclude := Std.HashSet.insert ∅ x
    let caps := captureList fv exclude ρ
    let fid  <- liftSig <| freshFun "lam"
    emitFunction (fid := fid) (caps := caps) (argName := x) (selfName? := none)
                 (body := body) (kSite := (kLbl, kAs))

  | .Ascribe e _ =>
    compileWithEnv e ρ (kLbl, kAs)

  | .Match es rows =>
    -- BT for simple backtracking automata; DT for decision tree
    compileMatchBT es rows ρ (kLbl, kAs)

partial def compileMatchBT
  (es : Array Expr)
  (rows : Array (Array Pattern × Expr))
  (ρ : Env) (kCont : Cont) : BuildM σ Unit := do

  let varsFromKAs : Array Name :=
    kCont.snd.foldl (init := #[]) (fun acc a =>
      match a with
      | .var x => acc.push x
      | .cst _ => acc)

  let namesFromRows : Array Name :=
    let step (accSeen : Array Name × Std.HashSet Name) (row : Array Pattern × Expr) :=
      let (pats, rhs) := row
      let bs := boundVarsOfPatterns pats
      let fvRow := fvs bs rhs
      let caps := captureList fvRow ∅ ρ
      let ns   := caps.map (·.2)
      ns.foldl (init := accSeen) (fun (acc, seen) n =>
        if seen.contains n then (acc, seen) else (acc.push n, seen.insert n))
    rows.foldl step (#[], (∅ : Std.HashSet Name)) |>.fst

  let (kParams, _) :=
    (varsFromKAs ++ namesFromRows).foldl
      (init := (#[], (∅ : Std.HashSet Name)))
      fun (acc, seen) n => 
        if seen.contains n then (acc, seen) else (acc.push n, seen.insert n)

  let kArgAtoms := kParams.map Atom.var

  let scrs <- es.foldlM (init := #[]) fun scrs e => do
    let lbl <- liftSig <| freshLbl "KS"
    compileWithEnv e ρ (lbl, kArgAtoms)
    newBlock lbl kParams
    let v <- liftSig <| fresh "s"
    modify fun b => {b with curParams := kParams.push v}
    return scrs.push v

  let baseCols : Array Sel := Array.ofFn (Sel.base ∘ Fin.toNat (n := scrs.size))

  let dispatch <- liftSig $ freshLbl "match_dispatch"
  endBlock (.goto dispatch $ kArgAtoms ++ scrs.map Atom.var)

  let (dP, dPA) <- liftSig $
    scrs.size.foldM (init := (#[], #[])) fun _ _ (dP, dPA) =>
      fresh "s" >>= fun s => return (dP.push s, dPA.push (Atom.var s))

  let failLbl <- liftSig <| freshLbl "match_fail"
  let (kLbl, kAs) := kCont

  let (_, firstRowLbl?) <-
    rows.size.foldRevM (init := (failLbl, none)) fun i _ (nextFail, firstRowLbl?) => do
      let thisLbl <- liftSig <| freshLbl s!"row_{i}"
      let rowScrParams <- liftSig $
        scrs.size.foldM (init := #[]) fun _ _ a => a.push <$> fresh "s"
      let rowParams := kParams ++ rowScrParams
      newBlock thisLbl rowParams
      let (pats, rhs) := rows[i]
      matchRowBT kParams rowScrParams baseCols pats ρ nextFail (kLbl, kAs) rhs
      return (thisLbl, some thisLbl)

  newBlock dispatch (kParams ++ dP)
  match firstRowLbl? with
  | some l => endBlock (.goto l $ kArgAtoms ++ dPA)
  | none   => endBlock (.goto failLbl $ kArgAtoms ++ dPA)

  newBlock failLbl $ kParams ++ dP
  endBlock (.goto kLbl (kAs.push (.cst .unit)))

partial def matchRowBT
  (kParams : Array Name)
  (roots : Array Name)
  (cols  : Array Sel)
  (pats  : Array Pattern)
  (ρ     : Env)
  (onFail : Label)
  (kCont : Cont)
  (rhs    : Expr)
  : BuildM σ Unit := do

  if pats.isEmpty then
    compileWithEnv rhs ρ kCont
  else
    let j := 0
    match pats[0]! with
    | .PWild =>
      let cols' := cols.eraseIdx! j
      let pats' := pats.eraseIdx! j
      matchRowBT kParams roots cols' pats' ρ onFail kCont rhs
    | .PVar x =>
      let v <- realizeSel roots cols[0]!
      let ρ' := ρ.insert x v
      let cols' := cols.eraseIdx! j
      let pats' := pats.eraseIdx! j
      matchRowBT kParams roots cols' pats' ρ' onFail kCont rhs
    | .PConst tc =>
      let sv <- realizeSel roots cols[0]!
      let (op, atom) :=
        match tc with
        | .PInt n  => (PrimOp.eqInt,  Atom.cst (.int n))
        | .PBool b => (PrimOp.eqBool, Atom.cst (.bool b))
        | .PStr s  => (PrimOp.eqStr,  Atom.cst (.str s))
        | .PUnit   => (PrimOp.eqInt,  Atom.cst (.int 0))
      let c <- bindRhs (.prim op #[.var sv, atom]) "cmp"
      let thenLbl <- liftSig <| freshLbl "bt_then"
      let kr := kParams ++ roots
      endBlock (.ifGoto c thenLbl onFail kr kr)
      newBlock thenLbl kr
      let cols' := cols.eraseIdx! j
      let pats' := pats.eraseIdx! j
      matchRowBT kParams roots cols' pats' ρ onFail kCont rhs
    | .PProd' p1 p2 =>
      let s := cols[0]!
      let cols' := #[Sel.field s 0, Sel.field s 1] ++ cols[1:]
      let pats' := #[p1, p2] ++ pats[1:]
      matchRowBT kParams roots cols' pats' ρ onFail kCont rhs
    | .PCtor c args =>
      let sv <- realizeSel roots cols[0]!
      let contLbl <- liftSig $ freshLbl s!"bt_ctor_{c}"
      let kr := kParams ++ roots
      let alts : Array (Name × Nat × Label × Array Name) :=
        #[(c, args.size, contLbl, kr)]
      endBlock (.switchCtor sv alts (some (onFail, kr)))
      newBlock contLbl kr
      let cols' :=
        Array.ofFn (Sel.field cols[0]! ∘ Fin.toNat (n := args.size)) ++ cols[1:]
      let pats' := args ++ pats[1:]
      matchRowBT kParams roots cols' pats' ρ onFail kCont rhs

end

private def collectTopPatBinds (p : Pattern) (s : Sel) : Array (String × Sel) :=
  go p s where
  go : Pattern -> Sel -> Array (String × Sel)
  | .PVar x, sel      => #[(x, sel)]
  | .PWild, _         => #[]
  | .PConst _, _      => #[]
  | .PProd' p q, sel  => go p (.field sel 0) ++ go q (.field sel 1)
  | .PCtor _ as, sel  =>
      as.size.fold (init := #[]) fun i _ acc =>
        acc ++ go as[i] (.field sel i)

partial def lowerTopPatBind
  (scr : Name)                      -- the evaluated RHS value
  (pat : Pattern)
  (succLbl : Label)                 -- success continuation label
  (succParams : Array Name)
  (failLbl : Label)                 -- failure label
  : BuildM σ Unit := do
  let roots := #[scr]
  let binds := collectTopPatBinds pat (.base 0)

  let rec go (work : List (Sel × Pattern)) : BuildM σ Unit := do
    match work with
    | [] =>
      let args <- binds.foldlM (init := #[]) fun a (_, sel) =>
        (a.push ∘ .var) <$> realizeSel roots sel
      endBlock (.goto succLbl args)
    | (sel, p) :: rest =>
      match p with
      | .PWild =>
        go rest
      | .PVar _ =>
        go rest
      | .PConst tc =>
        let sv <- realizeSel roots sel
        let (op, k) :=
          match tc with
          | .PInt n  => (PrimOp.eqInt,  Atom.cst (.int n))
          | .PBool b => (PrimOp.eqBool, Atom.cst (.bool b))
          | .PStr s  => (PrimOp.eqStr,  Atom.cst (.str s))
          | .PUnit   => (PrimOp.eqInt,  Atom.cst (.int 0))
        let c <- bindRhs (.prim op #[.var sv, k]) "cmp"
        let thenLbl <- liftSig <| freshLbl "top_then"
        endBlock (.ifGoto c thenLbl failLbl)
        newBlock thenLbl succParams
        go rest
      | .PProd' p q =>
        go ((Sel.field sel 0, p) :: (Sel.field sel 1, q) :: rest)
      | .PCtor cn as =>
        let sv <- realizeSel roots sel
        let contLbl <- liftSig <| freshLbl s!"top_ctor_{cn}"
        let alts : Array (Name × Nat × Label × Array Name) :=
          #[(cn, as.size, contLbl, #[])]
        endBlock (.switchCtor sv alts (some (failLbl, #[])))
        newBlock contLbl succParams
        let rest' :=
          as.size.foldRev (init := [])
            (fun i _ a => (Sel.field sel i, as[i]) :: a)
          ++ rest
        go rest'

  go [(Sel.base 0, pat)]

private def emitTopBinding
  (lhsPat : Pattern) (rhs : Expr)
  (ρr : ST.Ref σ Env) (lblH : Label) : BuildM σ Unit := do
  let eANF := runST fun _ => ANF.normalize rhs |>.run' 0
  let ρ <- ρr.get
  let evalLbl <- liftSig <| freshLbl "top_eval"
  compileWithEnv eANF ρ (evalLbl, #[])
  newBlock evalLbl #[]
  let scr <- liftSig <| fresh "s"
  modify fun b => { b with curParams := #[scr] }

  let failLbl <- liftSig <| freshLbl "bind_fail"

  let binds := collectTopPatBinds lhsPat (.base 0)
  let succParams : Array Name := binds.map (fun (x, _) => x)
  let succLbl <- liftSig <| freshLbl "bind_ok"

  lowerTopPatBind scr lhsPat succLbl succParams failLbl

  newBlock failLbl #[]
  endBlock (.goto lblH #[Atom.cst .unit])

  newBlock succLbl succParams
  ρr.modify fun ρ =>
    succParams.foldl (init := ρ) (fun acc x => acc.insert x x)

def compileToMain (e : Expr) : M σ Module := do
  let e := runST fun _ => ANF.normalize e |>.run' 0
  let entry <- freshLbl "main_entry"
  let init : FunBuilder :=
    { fid := "main"
    , params := #[]
    , entry := entry
    , curLbl := entry
    , curParams := #[]
    , curBody := #[]
    , blocks := #[]
    , funs := #[]
    , kcases := #[]}
  let (_, st) <- StateRefT'.run (s := init) do
    let lblH <- liftSig <| freshLbl "haltK"
    compileWithEnv e ∅ (lblH, #[])
    newBlock lblH #[]
    let r <- liftSig <| fresh "res"
    modify fun (b : FunBuilder) => { b with curParams := #[r] }
    endBlock (.halt r)

  -- build global kapply dispatcher
  let kapplyFun <- buildKApply st.kcases

  let mainFun := { fid := "main"
                 , params := #[]
                 , blocks := st.blocks
                 , entry := entry}
  pure (optModule ⟨st.funs.push kapplyFun, mainFun⟩)

def compile1 (s : String) (PE : PEnv) (E : _root_.Env) : IO Unit := do
  try
    let e <- IO.ofExcept $ Parsing.parse s PE
    let (_, l) <- IO.ofExcept $ MLType.runInfer1 e E
    let (m, _) := runST fun _ => compileToMain e |>.run 0
    IO.print l
    IO.println $ (Std.Format.pretty (width := 80) ∘ fmtModule) m
  catch e => IO.println (Logging.error $ toString e)

end CPS
open CPS in
def compileTop (decls : Array TopDecl) : M σ Module := do
  let entry <- freshLbl "main_entry"
  let init : FunBuilder :=
    { fid := "main"
    , params := #[]
    , entry := entry
    , curLbl := entry
    , curParams := #[]
    , curBody := #[]
    , blocks := #[]
    , funs := #[]
    , kcases := #[]}

  let (_, st) <- StateRefT'.run (s := init) do
    let lblH <- liftSig <| freshLbl "haltK" -- final label

    -- Thread an environment of top-level bound names
    let ρ : ST.Ref σ CPS.Env <- .mkRef ∅
    let lastName? : ST.Ref σ (Option Name) <- .mkRef none

    for d in decls do
      match d with
      | .tyBind _ => pure ()
      | .patBind (pat, e) => emitTopBinding pat e ρ lblH
      | .idBind (id, e) =>
        if !id.startsWith "(" then
          let eANF := runST fun _ => ANF.normalize e |>.run' 0
          let lbl <- liftSig <| freshLbl s!"top_{id}"
          (compileWithEnv eANF · (lbl, #[])) =<< ρ.get
          newBlock lbl #[]
          modify fun (b : FunBuilder) => {b with curParams := #[id]}
          ρ.modify fun ρ => ρ.insert id id
          lastName?.set $ some id
    let ρ <- ρ.get
    let lastName? <- lastName?.get
    match ρ.get? "main" <|> lastName? with
    | some v => endBlock (.goto lblH #[Atom.var v])
    | none   => endBlock (.goto lblH #[Atom.cst .unit])

    newBlock lblH #[]
    let r <- liftSig <| fresh "res"
    modify fun (b : FunBuilder) => {b with curParams := #[r]}
    endBlock (.halt r)

  -- build global kapply dispatcher
  let kapplyFun <- buildKApply st.kcases

  let mainFun : Fun :=
    {fid := "main", params := #[], blocks := st.blocks, entry := entry}
  pure (optModule ⟨st.funs.push kapplyFun, mainFun⟩)
