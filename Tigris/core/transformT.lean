/-!
  type-directed pattern matching compilation. see also [exhaust.lean](typing/exhaust.lean)
partial def lowerMatchDT'
  (lookup : TyLookup)
  (scrTys : Array MLType)
  (scrs   : Array Name)
  (rows   : Array (Array Pattern × Expr))
  (ρ      : Env)
  (k      : Name -> M σ LExpr)
  : M σ LExpr := do
  let u <- fresh "u"
  let kont <- k u
  let fallback : LExpr := .letVal u (.cst .unit) kont
  let cols := Array.ofFn (Sel.base ∘ @Fin.toNat scrs.size)
  let rstates := rows.map fun (pats, rhs) => {pats, rhs}
  let dt := buildTree cols rstates
  lowerDTTyped lookup cols (scrTys.map some) scrs dt ρ (fun x => pure (.seq #[] (.ret x))) fallback

partial def lowerDTTyped
  (lookup : TyLookup)
  (cols   : Array Sel)
  (tys    : Array (Option MLType))
  (roots  : Array Name)
  (dt     : DTree)
  (ρ      : Env)
  (k      : Name -> M σ LExpr)
  (onFail : LExpr)
  : M σ LExpr := do
  match dt with
  | .fail => return onFail
  | .leaf row =>
    bindPatBinds roots row.binds ρ (lowerE row.rhs · k)

  | .splitProd j next =>
    let s := cols[j]!
    let cols' := cols.replaceAt j #[Sel.field s 0, Sel.field s 1]
    let tys' :=
      match tys[j]! with
      | some (.TProd a b) => tys.replaceAt j #[some a, some b]
      | _                 => tys.replaceAt j #[none, none]
    lowerDTTyped lookup cols' tys' roots next ρ k onFail

  | .testConst j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      let caseIRs <- cases.mapM fun (tc, sub) => do
        let br <- lowerDTTyped lookup (cols.eraseIdx! j) (tys.eraseIdx! j) roots sub ρ k onFail
        pure (constOnly tc, br)
      let present : Std.HashSet TConst :=
        cases.foldl (·.insert ·.1) ∅
      let needDef := not (constCasesExhaustive tys[j]! present) ||
                     d?.isSome
      let defIR? <-
        if d?.isSome then
          some <$> lowerDTTyped lookup (cols.eraseIdx! j) (tys.eraseIdx! j) roots d?.get! ρ k onFail
        else if needDef then
          pure (some onFail)
        else
          pure none
      return .seq #[] (.switchConst sv caseIRs defIR?)

  | .testCtor j cases d? =>
    realizeSel roots cols[j]! fun sv => do
      -- build branches with refined types when available
      let acc <-
        cases.foldlM (init := #[]) fun acc (cname, ar, sub) => do
          let cols := cols.replaceAt j $ .ofFn (Sel.field cols[j]! ∘ @Fin.toNat ar)
          let tys := match refineTypesForCtor lookup tys[j]! cname with
                     | some fts => tys.replaceAt j (fts.map some)
                     | none => tys.replaceAt j (.replicate ar none)
          let br <- lowerDTTyped lookup cols tys roots sub ρ k onFail
          pure $ acc.push (cname, ar, br)
      let present : Std.HashSet (String × Nat) :=
        cases.foldl (init := ∅) fun s (c, ar, _) => s.insert (c, ar)
      let needDef := not (ctorCasesExhaustive lookup tys[j]! present) ||
                     d?.isSome
      let defIR? <-
        if d?.isSome then
          some <$> lowerDTTyped lookup (cols.eraseIdx! j) (tys.eraseIdx! j) roots d?.get! ρ k onFail
        else if needDef then
          pure (some onFail)
        else
          pure none
      return .seq #[] (.switchCtor sv acc defIR?)
-/
