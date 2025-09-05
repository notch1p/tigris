import Tigris.core.ir

namespace CPS open Std
abbrev UseMap := HashMap Name Nat

@[inline] def UseMap.bump (m : UseMap) (x : Name) : UseMap :=
  if x.isEmpty then m else m.alter x (fun | some n => some (n+1) | none => some 1)
@[inline] def UseMap.bumpMany (m : UseMap) (xs : Array Name) : UseMap :=
  xs.foldl (init := m) (fun a x => a.bump x)
@[inline] def UseMap.bumpAtom (m : UseMap) : Atom -> UseMap
  | .var x => m.bump x
  | .cst _ => m

private def countRhs (m : UseMap) : Rhs -> UseMap
  | .prim _ args => args.foldl UseMap.bumpAtom m
  | .proj src _  => m.bump src
  | .mkPair x y  => (m.bump x).bump y
  | .mkConstr _ as => m.bumpMany as
  | .isConstr src .. => m.bump src
  | .mkClosure _ e => m.bumpMany e

private def countTerm (m : UseMap) : Term -> UseMap
  | .appFun f arg k =>
      (m.bump f).bump arg |>.bump k
  | .appKnown _ env arg k =>
      (m.bumpMany env).bump arg |>.bump k
  | .ret k v =>
      (m.bump k).bump v
  | .ifGoto cond _ _ t e =>
      (m.bump cond).bumpMany t |>.bumpMany e
  | .switchCtor scrut alts defs? =>
      let m := m.bump scrut
      let m := alts.foldl (init := m) (fun a (_,_,_,as) => a.bumpMany as)
      match defs? with
      | some (_, as) => m.bumpMany as
      | none => m
  | .goto _ args =>
      args.foldl UseMap.bumpAtom m
  | .halt v => m.bump v

def usesOfFun (f : Fun) : UseMap :=
  f.blocks.foldl (init := (∅ : UseMap)) fun m b =>
    let m := b.body.foldl (init := m) (fun a (.let1 _ rhs) => countRhs a rhs)
    countTerm m b.term

abbrev CloMap := HashMap Name (Name × Array Name)

def collectClosures (f : Fun) : CloMap :=
  f.blocks.foldl (init := (∅ : CloMap)) fun m b =>
    b.body.foldl (init := m) (fun a s =>
      match s with
      | .let1 x (.mkClosure fid env) => a.insert x (fid, env)
      | _ => a)

def rewriteKnownFun (cm : CloMap) (b : Block) : Block :=
  match b.term with
  | .appFun f arg k =>
    match cm.get? f with
    | some (fid, env) => {b with term := .appKnown fid env arg k}
    | none => b
  | _ => b

partial def dceFun (f : Fun) : Fun :=
  let u := usesOfFun f
  let blocks' :=
    f.blocks.map (fun b =>
      let body' := b.body.filter (fun (.let1 x _) => u.getD x 0 > 0)
      {b with body := body'})
  letI f' := {f with blocks := blocks'}
  if f'.blocks == f.blocks then f else dceFun f'

abbrev TrampMap := HashMap Label Label

def argsAreParams (args : Array Atom) (params : Array Name) : Bool :=
  if args.size != params.size then false
  else Id.run do
    for a in args, p in params do
      match a with
      | .var x =>
        if x != p then return false
      | .cst _ => return false
    return true

def buildTramp (f : Fun) : TrampMap :=
  let labelSet : Std.HashSet Label :=
    f.blocks.foldl (·.insert ∘ Block.label) ∅
  f.blocks.foldl (init := (∅ : TrampMap)) fun m {body, label, params, term} =>
    match body.isEmpty, term with
    | true, .goto l args =>
      if l != label && argsAreParams args params && labelSet.contains l then
        m.insert label l
      else m
    | _, _ => m

partial def resolveTramp (tm : TrampMap) (l : Label) : Label :=
  match tm.get? l with
  | some l' => if l' == l then l else resolveTramp tm l'
  | none => l

def remapLabelsInTerm (tm : TrampMap) : Term -> Term
  | .appFun f arg k =>
      .appFun f arg k
  | .appKnown fid env arg k =>
      .appKnown fid env arg k
  | .ret k v => .ret k v
  | .ifGoto c t e athen aelse =>
      .ifGoto c (resolveTramp tm t) (resolveTramp tm e) athen aelse
  | .switchCtor s alts d? =>
    let alts' := alts.map (fun (c, ar, l, as) => (c, ar, resolveTramp tm l, as))
    let d?' := d?.map (fun (l, as) => (resolveTramp tm l, as))
    .switchCtor s alts' d?'
  | .goto l as =>
      .goto (resolveTramp tm l) as
  | .halt v => .halt v

def mergeEmptyGoto (f : Fun) : Fun :=
  let tm := buildTramp f
  if tm.isEmpty then f else
    let blocks1 :=
      f.blocks.map (fun b =>
        let body := b.body
        let term := remapLabelsInTerm tm b.term
        {b with body, term})
    let newEntry := resolveTramp tm f.entry
    let keep := blocks1.filter (·.label ∉ tm)
    {f with blocks := keep, entry := newEntry}

@[inline] def combineTramp (a b : TrampMap) : TrampMap :=
  b.fold HashMap.insert a
@[inline] def buildGlobalTramp (m : Module) : TrampMap :=
  m.funs.foldl (combineTramp · $ buildTramp ·) (buildTramp m.main)
@[inline] def remapLabelsInBlock (tm : TrampMap) (b : Block) : Block :=
  {b with term := remapLabelsInTerm tm b.term}

def remapLabelsInFun (tm : TrampMap) (f : Fun) : Fun :=
  letI blocks := f.blocks.map (remapLabelsInBlock tm)
  letI entry  := resolveTramp tm f.entry
  {f with blocks, entry}
def dropTrampsInFun (tm : TrampMap) (f : Fun) : Fun :=
  letI blocks := f.blocks.filter (·.label ∉ tm)
  {f with blocks}
def mergeEmptyGotoGlobal (m : Module) : Module :=
  let tm := buildGlobalTramp m
  if tm.isEmpty then m else
    let funs1 := m.funs.map (remapLabelsInFun tm)
    let main1 := remapLabelsInFun tm m.main
    let funs := funs1.map (dropTrampsInFun tm)
    let main := dropTrampsInFun tm main1
    {funs, main}

/--
  1. Rewrite CALL f ⋯ to CALLKNOWN ⋯ if f := mkClosure ⋯
  2. DCE
  3. Merge empty GOTO trampolines (per-fun)
  4. DCE
-/
def optFun (f : Fun) : Fun :=
  let cm := collectClosures f
  let f2 := {f with blocks := f.blocks.map (rewriteKnownFun cm)}
  let f3 := dceFun f2
  let f4 := mergeEmptyGoto f3
  dceFun f4

@[inherit_doc optFun] def optModule (m : Module) : Module :=
  let tm0 := buildGlobalTramp m
  let m1 : Module := ⟨m.funs.map optFun, optFun m.main⟩
  let m2 :=
    if tm0.isEmpty then m1 else
      letI funs1 := m1.funs.map (remapLabelsInFun tm0)
      letI main1 := remapLabelsInFun tm0 m1.main
      letI funs2 := funs1.map (dropTrampsInFun tm0)
      letI main2 := dropTrampsInFun tm0 main1
      {funs := funs2, main := main2}
  ⟨m2.funs.map dceFun, dceFun m2.main⟩

end CPS
