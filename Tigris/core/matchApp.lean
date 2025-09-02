import Tigris.parsing.types
import Tigris.core.ir

namespace CPS
inductive Sel where
  | base (idx : Nat)
  | field (s : Sel) (idx : Nat)
deriving Repr, Inhabited

structure RowState where
  pats : Array Pattern
  rhs  : Expr
  binds: Array (String × Sel) := #[]
deriving Repr, Inhabited

inductive DTree where
  | fail
  | leaf (row : RowState)
  | testConst (j : Nat) (branches : Array (TConst × DTree)) (default? : Option DTree)
  | testCtor  (j : Nat) (branches : Array (Name × Nat × DTree)) (default? : Option DTree)
  | splitProd (j : Nat) (next : DTree)
deriving Repr, Inhabited

def specDefault (cols : Array Sel) (j : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := (r.pats.extract 0 j) ++ (r.pats.extract j.succ r.pats.size)
    match p with
    | .PVar x =>
      let b := r.binds.push (x, cols[j]!)
      acc.push {r with pats := rest, binds := b}
    | .PWild =>
      acc.push {r with pats := rest}
    | _ => acc

def specCtor (cols : Array Sel) (j : Nat) (c : Name) (ar : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := (r.pats.extract 0 j) ++ (r.pats.extract (j+1) r.pats.size)
    match p with
    | .PCtor c' args =>
      if c' == c && args.size == ar then
        acc.push {r with pats := args ++ rest}
      else acc
    | .PVar x =>
      let shaped := (Array.replicate ar Pattern.PWild) ++ rest
      acc.push {r with pats := shaped, binds := r.binds.push (x, cols[j]!)}
    | .PWild =>
      let shaped := (Array.replicate ar Pattern.PWild) ++ rest
      acc.push {r with pats := shaped}
    | _ => acc

def specProd (j : Nat) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := (r.pats.extract 0 j) ++ (r.pats.extract j.succ r.pats.size)
    match p with
    | .PProd' p1 p2 =>
      acc.push {r with pats := #[p1, p2] ++ rest}
    | .PVar _ | .PWild =>
      acc.push {r with pats := #[Pattern.PWild, Pattern.PWild] ++ rest}
    | _ => acc

def specConst (cols : Array Sel) (j : Nat) (k : TConst) (rows : Array RowState) : Array RowState :=
  rows.foldl (init := #[]) fun acc r =>
    let p := r.pats[j]!
    let rest := (r.pats.extract 0 j) ++ (r.pats.extract j.succ r.pats.size)
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
        let rec dropAll (cols : Array Sel) (rows : Array RowState) :=
          if cols.isEmpty then rows
          else
            let rows' := specDefault cols 0 rows
            let cols' := cols.extract 1 cols.size
            dropAll cols' rows'
        let rows' := dropAll cols rows
        if rows'.isEmpty then .fail else .leaf rows'[0]!
      | some j =>
        let hasProd := rows.any (fun r => match r.pats[j]! with | .PProd' .. => true | _ => false)
        if hasProd then
          .splitProd j (buildTree (let s := cols[j]!
                                   let cols' := (cols.extract 0 j) ++ #[Sel.field s 0, Sel.field s 1] ++ (cols.extract (j+1) cols.size)
                                   cols')
                                 (specProd j rows))
        else
          let ctors : Std.HashSet (Name × Nat) :=
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
              ctors.toList.map (fun (c, ar) =>
                let cols' := (cols.extract 0 j) ++
                             Array.ofFn (fun (i : Fin ar) => Sel.field cols[j]! i) ++
                             (cols.extract (j+1) cols.size)
                let rows' := specCtor cols j c ar rows
                (c, ar, buildTree cols' rows'))
                |>.toArray
            let haveDefault := rows.any (fun r => match r.pats[j]! with | .PVar _ | .PWild => true | _ => false)
            let defTree? :=
              if haveDefault then
                let rows' := specDefault cols j rows
                let cols' := (cols.extract 0 j) ++ (cols.extract (j+1) cols.size)
                some (buildTree cols' rows')
              else none
            .testCtor j cases defTree?
          else
            if !consts.isEmpty then
              let cases :=
                consts.toList.map (fun k =>
                  let cols' := (cols.extract 0 j) ++ (cols.extract (j+1) cols.size)
                  let rows' := specConst cols j k rows
                  (k, buildTree cols' rows'))
                  |>.toArray
              let haveDefault := rows.any (fun r => match r.pats[j]! with | .PVar _ | .PWild => true | _ => false)
              let defTree? :=
                if haveDefault then
                  let rows' := specDefault cols j rows
                  let cols' := (cols.extract 0 j) ++ (cols.extract (j+1) cols.size)
                  some (buildTree cols' rows')
                else none
              .testConst j cases defTree?
            else
              let rows' := specDefault cols j rows
              let cols' := (cols.extract 0 j) ++ (cols.extract (j+1) cols.size)
              buildTree cols' rows'

end CPS
