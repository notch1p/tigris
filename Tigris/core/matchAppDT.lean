/-- decision tree compiler, not actually used. prefer backtracking automata.
partial def compileMatchDT
  (es : Array Expr) (rows : Array (Array Pattern × Expr)) (ρ : Env) (kCont : Cont) : BuildM σ Unit := do
  let mut scrs : Array Name := #[]
  for e in es do
    let lbl <- liftSig <| freshLbl "KS"
    compileWithEnv e ρ (lbl, #[])
    newBlock lbl #[]
    let v <- liftSig <| fresh "s"
    modify fun b => { b with curParams := #[v] }
    scrs := scrs.push v
  let cols : Array Sel := Array.ofFn (Sel.base ∘ Fin.toNat (n := scrs.size))
  let rws : Array RowState := rows.map (fun (ps, rhs) => RowState.mk ps rhs #[])
  let dt := buildTree cols rws
  lowerTree dt scrs cols ρ kCont

partial def lowerTree (t : DTree) (roots : Array Name) (cols : Array Sel) (ρ : Env) (kCont : Cont) : BuildM σ Unit := do
  let (kLbl, kAs) := kCont
  match t with
  | .fail =>
    endBlock (.goto kLbl (kAs.push (.cst .unit)))
  | .leaf row =>
    (compileWithEnv row.rhs · (kLbl, kAs)) =<< row.binds.foldlM (init := ρ) fun ρ (x, s) =>
      ρ.insert x <$> realizeSel roots s

  | .splitProd j next =>
    let s := cols[j]!
    let cols' := cols[0:j] ++ #[Sel.field s 0, Sel.field s 1] ++ cols[j+1:]
    lowerTree next roots cols' ρ (kLbl, kAs)

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
        lowerTree sub roots cols' ρ (kLbl, kAs)
        newBlock lelse #[]
        go (i+1)
      else
        match defs? with
        | some defsub =>
          let cols' := cols.eraseIdx! j
          lowerTree defsub roots cols' ρ (kLbl, kAs)
        | none =>
          endBlock (.goto kLbl (kAs.push (.cst .unit)))
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
          , caseWork.push (lbl, lowerTree subtree roots cols' ρ (kLbl, kAs)))
    let defLbl? <-
      match defs? with
      | some subtree =>
        let lbl <- liftSig <| freshLbl "case_default"
        let cols' := cols.eraseIdx! j
        let work := lowerTree subtree roots cols' ρ (kLbl, kAs)
        pure (some (lbl, work))
      | none => pure none
    let defTerm? := defLbl?.map (fun (l, _) => (l, #[]))
    endBlock (.switchCtor sv alts defTerm?)
    for (lbl, work) in caseWork do
      newBlock lbl #[]
      work
    match defLbl? with
    | some (lbl, work) =>
      newBlock lbl #[]
      work
    | none => pure ()
-/
partial def dummyMatcherDT := ()