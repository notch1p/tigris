import Tigris.core.ir

-- DCE, closure conversion, defunctionalization, goto merging

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
  | .goto _ args => m.bumpMany args
  | .halt v => m.bump v

def usesOfFun (f : Fun) : UseMap :=
  f.blocks.foldl (init := ({} : UseMap)) fun m b =>
    letI m := b.body.foldl (init := m) fun a (.let1 _ rhs) =>
      countRhs a rhs
    countTerm m b.term

def rwKnown (b : Block) : Block :=
  match b.term with
  | .appFun f arg k =>
    if let some idx := b.body.findIdx? fun | .let1 x (.mkClosure _ _) => x == f
                                           | _ => false
    then
      -- perform the rewrite; DCE will clean the dead binding if unused later
      let fid := match b.body[idx]! with | .let1 _ (.mkClosure fid _) => fid | _ => "unknown"
      let env := match b.body[idx]! with | .let1 _ (.mkClosure _ env) => env | _ => #[]
      {b with term := .appKnown fid env arg k}
    else b
  | _ => b

abbrev KontMap := Std.HashMap Name (Label × Array Name)

def collectKonts (f : Fun) : KontMap :=
  f.blocks.foldl (init := (∅ : KontMap)) fun acc blk =>
    blk.body.foldl (init := acc) fun a s =>
      match s with
      | .let1 x (.mkKont l env) => a.insert x (l, env)
      | _ => a

def defunContBlock (konts : KontMap) (b : Block) : Block :=
  match b.term with
  | .appCont k (.var v) =>
    match konts.get? k with
    | some (lbl, env) => {b with term := .goto lbl (env.push v)}
    | none => b
  | _ => b

def defunContFun (f : Fun) : Fun :=
  letI km := collectKonts f
  {f with blocks := f.blocks.map (defunContBlock km)}

partial def dceFun (f : Fun) : Fun :=
  let u := usesOfFun f
  let blocks' :=
    f.blocks.map fun b =>
      let body := b.body.filter fun (.let1 x _) => u.getD x 0 > 0
      {b with body}
  let f' : Fun := {f with blocks := blocks'}
  if f'.blocks == f.blocks then f else dceFun f'

abbrev TrampMap := Std.HashMap Label Label

def buildTramp (f : Fun) : TrampMap :=
  f.blocks.foldl (init := (∅ : TrampMap)) fun m b =>
    match b.body.isEmpty, b.term with
    | true, .goto l args =>
      if args == b.params then m.insert b.label l else m
    | _, _ => m

partial def resolveTramp (tm : TrampMap) (l : Label) : Label :=
  match tm.get? l with
  | some l' => resolveTramp tm l'
  | none => l

def remapLabelsInTerm (tm : TrampMap) : Term -> Term
  | .ifGoto c t e athen aelse => .ifGoto c (resolveTramp tm t) (resolveTramp tm e) athen aelse
  | .switchCtor s alts d? =>
    let alts' := alts.map (fun (c, ar, l, as) => (c, ar, resolveTramp tm l, as))
    let d?' := d?.map (fun (l, as) => (resolveTramp tm l, as))
    .switchCtor s alts' d?'
  | .goto l as => .goto (resolveTramp tm l) as
  | t => t
@[inline] def remapLabelsInStmt (tm : TrampMap) : Stmt -> Stmt
  | .let1 x (.mkKont l env) => .let1 x (.mkKont (resolveTramp tm l) env)
  | s => s
def mergeEmptyGoto (f : Fun) : Fun :=
  let tm := buildTramp f
  if tm.isEmpty then f else
    let blocks1 :=
      f.blocks.map (fun b =>
        let body' := b.body.map (remapLabelsInStmt tm)
        let term' := remapLabelsInTerm tm b.term
        {b with body := body', term := term'})
    -- drop trampoline blocks
    let keep := blocks1.filter (fun b => tm.get? b.label |>.isNone)
    {f with blocks := keep}

def optFun (f : Fun) : Fun :=
  let f1 := defunContFun f                            -- defunK
  let f2 := {f1 with blocks := f1.blocks.map rwKnown} -- known-call-rw
  let f3 := dceFun f2                                 -- DCE
  let f4 := mergeEmptyGoto f3                         -- merge goto
  dceFun f4                                           -- DCE
def optModule (m : Module) : Module := {funs := m.funs.map optFun, main := optFun m.main}
attribute [always_inline, inline] optFun optModule defunContFun
