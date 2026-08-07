import Tigris.codegen.cltypes
import Tigris.TCNF.entrypoint

namespace TCNF.CL open Std

def emitLit : TConst -> Sexp
  | .PInt i      => .int i
  | .PBool true  => .sym "t"
  | .PStr s      => .str s
  | _            => .sym "nil" -- unit/false

/-- A value-position fvar: a bare top-level function is boxed into a clos;
everything else (locals, 0-arity globals) is just its symbol. -/
def emitAtom (a : Atom) : CGM Sexp := do
  match a with
  | .lit k   => return emitLit k
  | .erased  => return .sym "nil"
  | .fvar x  =>
    match <- declArity? x with
    | some ar =>
      let symx <- .sym <$> valSym x
      if ar >= 1
      then return .list #[.sym "%clos", .list #[.sym "function", symx], .int ar]
      else return symx
    | none => .sym <$> valSym x

def mkApply : Sexp -> Array Sexp -> Sexp := (.list $ #[·] ++ ·)

@[inline] def atoms (as : Array Atom) : CGM (Array Sexp) := as.mapM emitAtom

/--
- `(%clos <fn> m)` where `fn` fixes `fixed` and takes `m` fresh caller args;
- `(%clos #'head m)` if empty `fixed`
-/
def mkClosureV (headSym : String) (fixed : Array Sexp) (m : Nat) : CGM Sexp := do
  if fixed.isEmpty then
    return .list #[.sym "%clos", .list #[.sym "function", .sym headSym], .int m]
  else
    let gs <- m.foldM (fun _ _ a => a.push <$> Sexp.sym <$> freshG) #[]
    let call := mkApply (.sym headSym) (fixed ++ gs)
    return .list #[.sym "%clos", .list #[.sym "lambda", .list gs, call], .int m]

/-- `(gapply<n> h as*)`. -/
def emitGeneric (h : FVarId) (as : Array Atom) : CGM Sexp := do
  let n := as.size
  if n == 0 then return .sym (<- valSym h)

  noteArity n
  let a  <- emitAtom $ .fvar h
  let as <- atoms as
  return .list $ #[.sym s!"gapply{n}", a] ++ as

def emitValue (v : LetValue .postCC) : CGM Sexp := do
  match v with
  | .lit k    => return emitLit k
  | .pair p q => return .list #[.sym "cons", <- emitAtom p, <- emitAtom q]
  | .proj i s =>                              -- product: pairs are conses
    let ss <- valSym s
    match i with
    | 0 => return .list #[.sym "car", .sym ss]
    | 1 => return .list #[.sym "cdr", .sym ss]
    | i => return .list #[.sym "nth", .int i, .sym ss]        -- pairs nest; >=2 unexpected
  | .field c i s  => return .list #[.sym (fieldAcc c i), .sym (<- valSym s)]  -- struct/dict accessor
  | .ctor t as    => mkApply (.sym (mkSym t)) <$> atoms as
  | .prim op as   => mkApply (.sym (primFn op)) <$> atoms as
  | .extern nm as =>                                                          -- direct foreign call
    if as.isEmpty then return .sym nm                                         -- 0-ary: foreign value
    else mkApply (.sym nm) <$> atoms as
  | .isCtor s t _ => return .list $ #[.sym (predSym t), .sym (<- valSym s)]
  | .app h as =>
    if h == matchFailFVar then
      return .list #[.sym "error", .sym "'match-failure", .sym ":discr", mkApply (.sym "list") (<- atoms as)]
    declArity? h >>= fun
    | some ar => if ar >= 1 && ar == as.size
                 then mkApply <$> .sym <$> valSym h <*> atoms as -- direct call
                 else emitGeneric h as
    | none    => emitGeneric h as
  | .pap h as =>
    match <- declArity? h with
    | some ar => mkClosureV (<- valSym h) (<- atoms as) (ar - as.size)         -- known partial
    | none    => emitGeneric h as                                            -- unknown -> curry via %apply-slow
  | .mkClos code env _ =>
    let full := (<- declArity? code).getD env.size
    mkClosureV (<- valSym code) (<- atoms env) (full - env.size)

def peelLets : Code .postCC -> List (LetDecl .postCC) × Code .postCC
  | .let d k => let (ds, r) := peelLets k; (d :: ds, r)
  | c        => ([], c)

mutual
partial def emitCode (c : Code .postCC) : CGM Sexp := do
  match c with
  | .let .. =>
    let (binds, rest) := peelLets c
    let binds := binds.toArray
    let emitBinds (ds : Subarray (LetDecl .postCC)) : CGM (Array Sexp) :=
      ds.foldlM (init := #[]) fun acc d => do
        let f <- valSym d.fvarId
        let a <- emitValue d.value
        return acc.push $ Sexp.list #[.sym f, a]
    -- reduces `let* xₙ = eₙ in xₙ` to `eₙ` for a group of n bindings.
    -- Mostly to work around SBCL's naive tailcall. See also comments in examples/fact.tig.
    match rest, binds.back? with
    | .ret (.fvar r), some last =>
      if r == last.fvarId then
        let bs   <- emitBinds binds[:binds.size - 1]
        let tail <- emitValue last.value
        return if bs.isEmpty then tail else .list #[.sym "let*", .list bs, tail]
      else
        return .list #[.sym "let*", .list (<- emitBinds binds.toSubarray), <- emitCode rest]
    | _, _ =>
      return .list #[.sym "let*", .list (<- emitBinds binds.toSubarray), <- emitCode rest]
  | .jp d k =>
    let ps <- d.params.mapM fun p => Sexp.sym <$> valSym p.fvarId
    let bodyS <- emitCode d.body
    let lf := Sexp.list #[.sym (<- valSym d.fvarId), .list ps, bodyS]
    return .list #[.sym "labels", .list #[lf], <- emitCode k]
  | .jmp j as => mkApply <$> .sym <$> valSym j <*> atoms as
  | .cases discr _ alts => emitCases discr alts
  | .ret v => emitAtom v
  | .unreach _ => return .list #[.sym "error", .str "unreachable"]

partial def emitCases (discr : FVarId) (alts : Array (Alt .postCC)) : CGM Sexp := do
  let d <- valSym discr
  let mut default? : Option Sexp := none
  let mut ctorAlts  : Array (String × Array Param × Code .postCC) := #[]
  let mut constAlts : Array (TConst × Code .postCC) := #[]
  for a in alts do
    match a with
    | .ctor t ps k => ctorAlts  := ctorAlts.push (t, ps, k)
    | .const c k   => constAlts := constAlts.push (c, k)
    | .default k   => default?  <- some <$> emitCode k
  if h : ctorAlts.size ≠ 0 then
    let (tycon, _, _) := (<- ctorInfo? ctorAlts[0].1).getD ("", 0, 0)
    let clauses <- ctorAlts.mapM fun (t, ps, k) => do
      let (_, tagIdx, _) := (<- ctorInfo? t).getD ("", 0, 0)
      let body <- emitCode k
      let binds <- ps.mapIdxM fun i p => do
        return Sexp.list #[.sym (<- valSym p.fvarId), .list #[.sym (fieldAcc t i), .sym d]]
      let clauseBody := if binds.isEmpty then body else Sexp.list #[.sym "let*", .list binds, body]
      return Sexp.list #[.int tagIdx, clauseBody]
    let clauses := match default? with
      | some db => clauses.push (.list #[.sym "t", db])
      | none    => clauses
    return .list (#[.sym "case", .list #[.sym (tagAcc tycon), .sym d]] ++ clauses)
  else
    match constAlts[0]?.map Prod.fst with
    | some TConst.PUnit => -- has to provide qualified name here. weird
      constAlts.mapM (emitCode ∘ Prod.snd) <&> fun clauses =>
        match clauses[0]?, default? with
        | some body, _  => body
        | none, some db => db
        | none, none    => .list #[.sym "error", .str "empty-cases"]
    | some (.PBool _) =>
      let mut tB? : Option Sexp := none
      let mut fB? : Option Sexp := none
      for (c, k) in constAlts do
        match c with
        | .PBool true  => tB? <- some <$> emitCode k
        | .PBool false => fB? <- some <$> emitCode k
        | _ => pure ()
      let noMatchE := Sexp.list #[.sym "error", .str "nonexhaustive"]
      let tB := tB? <|> default? |>.getD noMatchE
      let fB := fB? <|> default? |>.getD noMatchE
      return .list #[.sym "if", .sym d, tB, fB]
    | some (.PStr _) =>
      let clauses <- constAlts.mapM fun (c, k) => do
        let cs := match c with | .PStr s => s | _ => ""
        return Sexp.list #[.list #[.sym "%string=", .sym d, .str cs], <- emitCode k]
      let clauses := match default? with | some db => clauses.push (.list #[.sym "t", db]) | none => clauses
      return .list (#[.sym "cond"] ++ clauses)
    | some (.PInt _) =>
      let clauses <- constAlts.mapM fun (c, k) => do
        let ci := match c with | .PInt i => i | _ => 0
        return Sexp.list #[.int ci, <- emitCode k]
      let clauses := match default? with | some db => clauses.push (.list #[.sym "t", db]) | none => clauses
      return .list (#[.sym "case", .sym d] ++ clauses)
    | _ => return default?.getD (.list #[.sym "error", .str "empty-cases"])

end
open Std.Format

def emitDecl (d : Decl .postCC) : CGM Sexp := do
  let nm <- valSym d.fvarId
  let body <- emitCode d.body
  if d.arity >= 1 then
    let ps <- d.params.mapM fun p => Sexp.sym <$> valSym p.fvarId
    return .list #[.sym "defun", .sym nm, .list ps, body]
  else
    return .list #[.sym "defparameter", .sym nm, body]

/--
- `(declaim (ftype (function (args*) ret) f))` per defun;
- `(declaim (type T v))` per defparameter;
- a purely T ftype is dropped as useless.
-/
def emitDeclaims (m : Module .postCC) : CGM (Array Sexp) := do
  let {tys, ..} <- read
  let mut out : Array Sexp := #[]

  for d in m.decls.push m.main do
    let nm <- valSym d.fvarId
    if d.arity >= 1 then
      let argTs := d.params.map fun p => clType tys p.ty |>.getD "t"
      let (allArgs, fin) := d.ty.decomposeArr'
      let retTy := allArgs.drop d.params.size |>.foldr .TArr fin
      let retT  := clType tys retTy |>.getD "t"

      if argTs.all (· == "t") && retT == "t" then continue          -- no information

      let fnForm := Sexp.list #[.sym "function", .list (argTs.map Sexp.sym), .sym retT]
      out := out.push $ .list #[.sym "declaim", .list #[.sym "ftype", fnForm, .sym nm]]

    else
      if let some t := clType tys d.ty then
        out := out.push $ .list #[.sym "declaim", .list #[.sym "type", .sym t, .sym nm]]
  return out

/-- functions first, then values, then `main` -/
def emitModule (m : Module .postCC) (entry? := true) : CGM CLModule := do
  let mut funs : Array Sexp := #[]
  let mut vals : Array Sexp := #[]
  for d in m.decls do
    if d.arity >= 1
    then funs <- funs.push <$> emitDecl d
    else vals <- vals.push <$> emitDecl d
  let main <- emitDecl m.main
  let tail : Array Sexp <-
    if m.main.arity == 0 && entry? then
      pure #[.list #[.sym "format", .sym "t", .str "~S~%", .sym (<- valSym m.main.fvarId)]]
    else pure #[]
  let declaims <- emitDeclaims m
  return {funs, vals, main, tail, declaims}

def emitStructs (tyDecl : TyMap) : Array Sexp :=
  let tys := structTyNames tyDecl
  tyDecl.fold (init := #[]) fun acc tycon td =>
    if isBuiltinTy tycon || td.ctors.isEmpty || td.isNewtype then acc   -- newtypes collapse; no struct
    else
      let parent := Sexp.list #[.sym "defstruct",
        .list #[.sym (parentSym tycon),
                .list #[.sym ":conc-name", .sym s!"|{tycon}/|"],
                .list #[.sym ":constructor", .sym "nil"],
                .list #[.sym ":predicate", .sym "nil"]],
        .list #[.sym "|tag|", .int 0, .sym ":type", .list #[.sym "unsigned-byte", .int 8]]]
      let children := td.ctors.size.fold (init := #[]) fun i _ cs =>
        let (cname, fields, _) := td.ctors[i]
        let fields := fields.toArray
        let slotNames := fields.size.fold (fun i _ a => a.push $ .sym $ s!"|f{i}|") #[]
        -- concrete scalar fields carry `:type` which propagates through the slot accessor
        let slots := fields.mapIdx fun j (_, fty) =>
          let nm := Sexp.sym s!"|f{j}|"
          match (clType tys fty).bind fun t => (slotDefault? t).map (·, t) with
          | some (dflt, t) => Sexp.list #[nm, dflt, .sym ":type", .sym t]
          | none           => Sexp.list #[nm, .sym "nil"]
        let hdr :=
          .list #[.sym (ctorStruct cname),
            .list #[.sym ":include", .sym (parentSym tycon), .list #[.sym "|tag|", .int i]],
            .list #[.sym ":conc-name", .sym s!"|{cname}/|"],
            .list #[.sym ":constructor", .sym (mkSym cname), .list slotNames],
            .list #[.sym ":predicate", .sym (predSym cname)]]
        cs.push $ .list $ #[.sym "defstruct", hdr] ++ slots
      (acc.push parent) ++ children

def genGapply (n : Nat) : Sexp :=
  let args := (Array.range n).map fun i => Sexp.sym s!"a{i+1}"
  .list #[.sym "defun", .sym s!"gapply{n}", .list (#[Sexp.sym "c"] ++ args),
    .list #[.sym "if",
      .list #[.sym "eql", .list #[.sym "clos-arity", .sym "c"], .int n],
      .list (#[Sexp.sym "funcall", .list #[.sym "clos-fn", .sym "c"]] ++ args),
      .list #[.sym "%apply-slow", .sym "c", .list (#[Sexp.sym "list"] ++ args)]]]

partial def collectNames (c : Code .postCC) (acc : HashMap FVarId String) : HashMap FVarId String :=
  match c with
  | .let d k => collectNames k (acc.insert d.fvarId d.binderName)
  | .jp d k =>
    let acc := d.params.foldl (fun a p => a.insert p.fvarId p.binderName) (acc.insert d.fvarId d.binderName)
    collectNames k (collectNames d.body acc)
  | .cases _ _ alts =>
    alts.foldl (fun a alt =>
      collectNames alt.getCode (alt.getParams.foldl (fun a p => a.insert p.fvarId p.binderName) a)) acc
  | _ => acc

def mkCtx (m : Module .postCC) (tyDecl : TyMap) : Ctx := Id.run do
  let mut names     : HashMap FVarId String := ∅
  let mut declArity : HashMap FVarId Nat    := ∅
  for {fvarId, name, params, arity, body,..} in m.decls.push m.main do
    names     := collectNames body <|
      params.foldl (fun a p => a.insert p.fvarId p.binderName) (names.insert fvarId name)
    declArity := declArity.insert fvarId arity

  let mut ctorInfo : HashMap String (String × Nat × Nat) := ∅
  for (tycon, td) in tyDecl do
    if !isBuiltinTy tycon then
      for h : i in [0 : td.ctors.size] do
        let (cname, fields, _) := td.ctors[i]
        ctorInfo := ctorInfo.insert cname (tycon, i, fields.length)
  return {names, declArity, ctorInfo, tys := structTyNames tyDecl}

def compileToCL
  (m : Module .postCC)
  (tyDecl : TyMap)
  (speed   := 1)
  (safety  := 3)
  (debug   := 1)
  (entry?  := true)
  (runtime := some "runtime.lisp") : IO Format := do
  let ({funs, vals, main, tail, declaims}, st) <- emitModule m entry? (mkCtx m tyDecl) |>.run {}
  let structForms := emitStructs tyDecl
  let gapplyForms := st.genArities.toArray.qsort (· < ·) |>.map genGapply
  return joinSep' (sep := line ++ line) $    -- inline ++ for 1 linebreak
    #[.text "; Prelude\n" ++ .text (preludeCL speed safety debug runtime)]
    ++ sect "; struct" structForms
    ++ sect "; gapply" gapplyForms
    ++ sect "; ftype"  declaims
    ++ #[.text "; body" ++ line ++ span (funs ++ vals ++ #[main] ++ tail)]
where
  sect hdr fs : Array Format := if fs.isEmpty then #[] else #[.text hdr ++ "\n" ++ span fs]
  span fs : Format := joinSep' fs (line ++ line)

/-- source -> CL -/
def compileSource (src : String) : LowerM Format := do
  let (_, topdecl) <- Parsing.parseModuleIR src initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let mod <- lowerModuleCCOpt fdecls ctors E.tyDecl
  liftEIO $ compileToCL mod E.tyDecl

def checkCL (s : String) : LowerM Unit := do
  liftEIO <| IO.println <| (<- compileSource s).pretty 80

/-- source -> CL files -/
def emitToFile (src : String) (path : System.FilePath) : LowerM Unit := do
  liftEIO $ IO.FS.writeFile path (Format.pretty (<- compileSource src))

section Test
private def t (s : String) : IO Unit := (checkCL s).toIO IO.userError
private def load (s : System.FilePath) : IO Unit := IO.FS.readFile s >>= EIO.toIO .userError ∘ checkCL
private def ex (f : System.FilePath) : System.FilePath := "examples" / f.addExtension "tig"
end Test

end TCNF.CL
