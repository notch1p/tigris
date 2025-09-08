import Tigris.parsing.types

inductive Sel where
  | base (idx : Nat)
  | field (s : Sel) (idx : Nat)
deriving Repr, Inhabited

structure RowState where
  pats : Array Pattern
  rhs  : TExpr
  binds: Array (String × Sel) := #[]
deriving Repr, Inhabited

@[inline] private def Array.replaceAt (xs : Array α) (j : Nat) (ys : Array α) : Array α :=
  xs[0:j] ++ ys ++ xs[j+1:]

inductive DTree where
  | fail
  | leaf (row : RowState)
  | testConst (j : Nat) (branches : Array (TConst × DTree)) (default? : Option DTree)
  | testCtor  (j : Nat) (branches : Array (String × Nat × DTree)) (default? : Option DTree)
  | splitProd (j : Nat) (next : DTree)
deriving Repr, Inhabited

def specDefault (cols : Subarray Sel) (j : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := r.pats.eraseIdx! j
    match p with
    | .PVar x =>
      let b := r.binds.push (x, cols[j]!)
      acc.push {r with pats := rest, binds := b}
    | .PWild =>
      acc.push {r with pats := rest}
    | _ => acc

def specCtor (cols : Subarray Sel) (j : Nat) (c : String) (ar : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    match p with
    | .PCtor c' args =>
      if c' == c && args.size == ar then
        acc.push {r with pats := r.pats.replaceAt j args}
      else acc
    | .PVar x =>
      let shaped := Array.replicate ar Pattern.PWild
      acc.push {r with pats := r.pats.replaceAt j shaped, binds := r.binds.push (x, cols[j]!)}
    | .PWild =>
      let shaped := Array.replicate ar Pattern.PWild
      acc.push {r with pats := r.pats.replaceAt j shaped}
    | _ => acc

def specProd (j : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    match p with
    | .PProd' p q =>
      acc.push {r with pats := r.pats.replaceAt j #[p, q]}
    | .PVar _ | .PWild =>
      acc.push {r with pats := r.pats.replaceAt j #[Pattern.PWild, Pattern.PWild]}
    | _ => acc

def specConst (cols : Subarray Sel) (j : Nat) (k : TConst) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := r.pats.eraseIdx! j
    match p with
    | .PConst k' =>
      if k' == k then acc.push {r with pats := rest} else acc
    | .PVar x =>
      acc.push {r with pats := rest, binds := r.binds.push (x, cols[j]!)}
    | .PWild =>
      acc.push {r with pats := rest}
    | _ => acc

def pickColumn (rows : Array RowState) : Option Nat :=
  let arity := if rows.isEmpty then 0 else rows[0]!.pats.size
  let rec go (j : Nat) : Option Nat :=
    if j >= arity then none
    else
      let hasNonTrivial :=
        rows.any fun r =>
          match r.pats[j]! with
          | .PCtor .. | .PProd' .. | .PConst _ => true
          | _ => false
      if hasNonTrivial then some j else go j.succ
  go 0

partial def buildTree (cols : Array Sel) (rows : Array RowState) : DTree :=
  if rows.isEmpty then
    .fail
  else
    if rows[0]!.pats.isEmpty then
      .leaf rows[0]!
    else
      match pickColumn rows with
      | none =>
        let rec dropAll (cols : Subarray Sel) (rows : Array RowState) :=
          if cols.isEmpty then rows
          else
            let rows' := specDefault cols 0 rows
            let cols' := cols[1:]
            dropAll cols' rows'
        let rows' := dropAll cols.toSubarray rows
        if rows'.isEmpty then .fail else .leaf rows'[0]!
      | some j =>
        let hasProd := rows.any fun r => match r.pats[j]! with
                                         | .PProd' .. => true | _ => false
        if hasProd then
          .splitProd j $ buildTree
            (let s := cols[j]!; cols.replaceAt j #[.field s 0, .field s 1])
            (specProd j rows)
        else
          let ctors : Std.HashSet (String × Nat) :=
            rows.foldl (init := ∅) fun acc r =>
              match r.pats[j]! with
              | .PCtor c as => acc.insert (c, as.size)
              | _ => acc
          let consts : Std.HashSet TConst :=
            rows.foldl (init := ∅) fun acc r =>
              match r.pats[j]! with
              | .PConst k => acc.insert k
              | _ => acc
          if !ctors.isEmpty then
            let cases :=
              ctors.fold (init := #[]) fun a (c, ar) =>
                let cols' := cols.replaceAt j (.ofFn $ Sel.field cols[j]! ∘ @Fin.toNat ar)
                let rows' := specCtor cols.toSubarray j c ar rows
                a.push (c, ar, buildTree cols' rows')
            let haveDefault := rows.any fun r => match r.pats[j]! with
                                                 | .PVar _ | .PWild => true
                                                 | _ => false
            let defTree? :=
              if haveDefault then
                let rows' := specDefault cols.toSubarray j rows
                let cols' := cols.eraseIdx! j
                some (buildTree cols' rows')
              else none
            .testCtor j cases defTree?
          else
            if !consts.isEmpty then
              let cases :=
                consts.fold (init := #[]) fun a k =>
                  let cols' := cols.eraseIdx! j
                  let rows' := specConst cols.toSubarray j k rows
                  a.push (k, buildTree cols' rows')
              let haveDefault := rows.any fun r => match r.pats[j]! with
                                                   | .PVar _ | .PWild => true
                                                   | _ => false
              let defTree? :=
                if haveDefault then
                  let rows' := specDefault cols.toSubarray j rows
                  let cols' := cols.eraseIdx! j
                  some (buildTree cols' rows')
                else none
              .testConst j cases defTree?
            else
              let rows' := specDefault cols.toSubarray j rows
              let cols' := cols.eraseIdx! j
              buildTree cols' rows'
