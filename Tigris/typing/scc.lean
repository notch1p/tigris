import Tigris.typing.ttypes

namespace ConstraintInfer open MLType Rewritable Pattern Expr
open Std

/-!
# Binding-group dependency analysis (SCC)

Used for `let ... and ...` group. We split it into SCCs, typing checking in topo order
letting a later binding reference an earlier one. each component is generalized independently.
letrec self-reference has the form Fix (Fun ..), so it never appears as a free
variable; only mutual references can form edges. -/

/-- Deliverately conservative for nested non-recursive let RHS.
This is an overapproximation of the dependency graph which isn't _really_ harmful. -/
def fvOf (bound : Std.HashSet String) : Expr -> Std.HashSet String
  | .Var s        => if bound.contains s then ∅ else {s}
  | .CI _ | .CS _ | .CB _ | .CUnit => ∅
  | .App a b | .Prod' a b => fvOf bound a ∪ fvOf bound b
  | .Cond a b c   => fvOf bound a ∪ fvOf bound b ∪ fvOf bound c
  | .Fun x e      => fvOf (bound.insert x) e
  | .Fix e | .Fixcomb e | .Ascribe e _ => fvOf bound e
  | .Let ae e2 =>
    let names := ae.foldl (·.insert ·.1) bound
    (ae.attach.foldl (fun acc ⟨b, H⟩ =>
      match h : b with
      | (s, rhs) =>
        have : sizeOf b < sizeOf ae := Array.sizeOf_lt_of_mem $ h ▸ H
        have : sizeOf rhs < sizeOf b := h ▸ prod_sizeOf_lt_snd s rhs
        acc ∪ fvOf bound rhs) ∅) ∪ fvOf names e2
  | .Match against branches =>
    let a0 := against.foldl (· ∪ fvOf bound ·) ∅
    branches.attach.foldl (fun acc ⟨ps, H⟩ =>
      match h : ps with
      | (pats, rhs) =>
        have := Array.sizeOf_lt_of_mem $ h ▸ H
        have := h ▸ prod_sizeOf_lt_snd pats rhs
        let bnd := pats.foldl (fun b p => p.vars.foldl (·.insert ·) b) bound
        acc ∪ fvOf bnd rhs) a0
termination_by e => e

private structure TjS where
  index : Nat := 0
  idx   : Std.HashMap Nat Nat := ∅
  low   : Std.HashMap Nat Nat := ∅
  onStk : Std.HashSet Nat := ∅
  stack : List Nat := []
  sccs  : Array (Array Nat) := #[]

private def popUntil : List Nat -> Nat -> Array Nat -> List Nat × Array Nat
  | [],      _, acc => ([], acc)
  | x :: xs, v, acc => if x == v then (xs, acc.push x) else popUntil xs v (acc.push x)

/-- Strongly-connected components of adj, **dependencies first**, Tarjan over Kosaraju. See
> Tarjan, Robert. "Depth-first search and linear graph algorithms." SIAM journal on computing 1.2 (1972): 146-160.
-/
partial def sccsOf (adj : Array (Array Nat)) : ST σ $ Array $ Array Nat := do
  let ref : ST.Ref σ TjS <- ST.mkRef ({} : TjS)
  let rec strongconnect (adj : Array (Array Nat)) (v : Nat) : ST σ Unit := do
    ref.modify fun s => { s with idx := s.idx.insert v s.index
                                 low := s.low.insert v s.index
                                 index := s.index + 1
                                 stack := v :: s.stack
                                 onStk := s.onStk.insert v}
    for w in adj[v]! do
      let {idx, onStk,..} <- ref.get
      if !idx.contains w then                                -- unvisited: recurse
        strongconnect adj w
        ref.modify fun s => {s with low := s.low.insert v (min s.low[v]! s.low[w]!)}
      else if onStk.contains w then                          -- visited & on stack: back-edge
        ref.modify fun s => {s with low := s.low.insert v (min s.low[v]! s.idx[w]!)}

    let s <- ref.get
    if s.low[v]! == s.idx[v]! then
      let (rest, comp) := popUntil s.stack v #[]
      ref.modify fun s => {s with stack := rest, onStk := comp.foldl .erase s.onStk, sccs := s.sccs.push comp}

  for v in [0 : adj.size] do
    let st <- ref.get
    unless st.idx.contains v do
      strongconnect adj v

  TjS.sccs <$> ref.get

/-- Order a binding group into SCCs (dependency-first). -/
def depOrder (binds : Array (String × Expr)) : Array (Array (String × Expr)) :=
  Array.map (·.map (binds[·]!)) $ runST fun _ => sccsOf adj
where
  idxOf : Std.HashMap String Nat := binds.zipIdx.foldl (fun m (b, i) => m.insert b.1 i) ∅
  adj   : Array (Array Nat)      := binds.map fun (_, rhs) =>
    fvOf ∅ rhs |>.fold
      (fun a nm => match idxOf[nm]? with | some j => a.push j | none => a)
      #[]
end ConstraintInfer
