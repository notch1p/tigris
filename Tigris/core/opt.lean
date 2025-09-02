import Tigris.core.ir

namespace CPS open Std
abbrev UseMap := HashMap Name Nat

@[inline] def UseMap.bump (m : UseMap) (x : Name) : UseMap :=
  if x.isEmpty then m
  else m.alter x fun
                 | some n => some $ n + 1
                 | none => some 1
@[always_inline, inline] def UseMap.bumpMany (m : UseMap) (xs : Array Name) : UseMap :=
  xs.foldl bump m
@[inline] def UseMap.bumpAtom (m : UseMap) : Atom -> UseMap
  | .var x => m.bump x
  | .cst _ => m

private def countRhs (m : UseMap) : Rhs -> UseMap
  | .prim _ args => args.foldl .bumpAtom m
  | .proj src _ => m.bump src
  | .mkPair x y => m.bump x |>.bump y
  | .mkConstr _ as => m.bumpMany as
  | .isConstr src .. => m.bump src
  | .mkClosure _ e => m.bumpMany e
  | .mkKont _ e => m.bumpMany e

private def countTerm (m : UseMap) : Term -> UseMap
  | .appFun f arg k => m.bump f |>.bump arg |>.bump k
  | .appKnown _ e a k => m.bump a |>.bumpMany e |>.bump k
  | .appCont k v => m.bump k |>.bumpAtom v
  | .ifGoto cond _ _ t e =>
    m.bump cond |>.bumpMany t |>.bumpMany e
  | .switchCtor scrut alts defs? =>
    let m := m.bump scrut
    let m := alts.foldl (init := m) fun a (_, _, _, as) => a.bumpMany as
    match defs? with
    | some (_, as) => m.bumpMany as
    | none => m
  | .halt v => m.bump v

def usesOfBlock (b : Block) : UseMap :=
  letI m := b.body.foldl (init := ({} : UseMap)) fun a (.let1 _ rhs) =>
    countRhs a rhs
  countTerm m b.term

def elim1 (u : UseMap) (b : Block) : Block :=
  letI body := b.body.filter (fun (.let1 x _) => u.getD x 0 > 0)
  {b with body}

partial def elimFix (b : Block) : Block :=
  let u := usesOfBlock b
  let b' := elim1 u b
  if b'.body.size == b.body.size then b else elimFix b'

def rwKnown (b : Block) : Block :=
  match b.term with
  | .appFun f arg k =>
    letI pred | .let1 x _ => x == f
    if let some idx := b.body.findIdx? pred then
      let u := usesOfBlock b
      if u.getD f 0 == 1 then
        let term := .appKnown
          (match b.body[idx]! with | .let1 _ (.mkClosure fid _) => fid | _ => "unknown")
          (match b.body[idx]! with | .let1 _ (.mkClosure _ env) => env | _ => #[])
          arg k
        {b with term}
      else b
    else b
  | _ => b

def optBlock (b : Block) : Block := rwKnown b |> elimFix
def optFun (f : Fun) : Fun := {f with blocks := f.blocks.map optBlock}
def optModule (m : Module) : Module := {funs := m.funs.map optFun, main := optFun m.main}
attribute [always_inline, inline] optBlock optFun optModule
