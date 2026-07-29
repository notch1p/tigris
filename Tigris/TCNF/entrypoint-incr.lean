import Tigris.TCNF.entrypoint

namespace TCNF open Compiler CC Opt
namespace Incremental
/-!
Note that, in this section, most lowering helpers accepting an Array Decl only apply to single binding group.
Not the whole module's decl. Otherwise it defeats the very purpose of _being incremental_.
-/

structure IncrState where
  /-- ρ₀ -/
  topNames : FVarEnv := ∅
  globals  : FVSet   := ∅
  kmap     : KMap    := ∅
  ariMap   : AriMap  := ∅
  closMap  : ClosMap := ∅
  lifted   : Array (Decl .postCC) := #[]
abbrev IncrementalM := StateRefT IncrState CompilerM

section Lowering
def lowerTop1 (decl : TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : IncrementalM (Array $ Decl .preCC) := do
  let (fieldTys, ctorTyParams) := ctorTypeInfo tyDecls
  modifyThe NFState ({· with ctors, fieldTys, ctorTyParams, tyDecl := tyDecls})
  let {topNames,..} <- get
  let topNames <- collectTopNames.collect1 decl |>.foldlM (fun ρ nm => (ρ.insert nm ·) <$> internExtern nm) topNames
  let allDecls <- (lowerTopDecl topNames) decl
  modify ({· with topNames})
  return allDecls

def lowerTop (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : IncrementalM (Array $ Decl .preCC) := decls.flatMapM (lowerTop1 · ctors tyDecls)

def checkModI (s : String) : LowerM Unit := prog |>.run' {} |>.run' {}
where prog : IncrementalM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, log, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  liftEIO $ IO.print log
  let decls <- fdecls.flatMapM (lowerTop1 · ctors E.tyDecl)
  liftEIO $ println! Std.ToFormat.format decls
  |>.pretty (width := 80)

end Lowering

section CC
def ccDecls (decls : Array $ Decl .preCC) : IncrementalM Unit :=
  decls.forM ccDecl where
ccDecl decl := do
  let (globals, lifted) <- modifyGet fun s@{globals, lifted,..} =>
    let globals := globals.insert decl.fvarId
    ((globals, lifted), {s with globals})
  let go := TCNF.CC.ccDecl decl
  let (res, lifted') <- go.run {globals} |>.run lifted
  modify fun s => {s with lifted := lifted'.push res}

def lowerTopCC decls ctors tyDecls := (lowerTop decls ctors tyDecls >>= ccDecls) *> IncrState.lifted <$> get

def checkCCI (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (decls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let ds := decls.size

  let rec go i lifted is nfs globals (h : i <= ds) :=
    match h' : i with
    | 0 => return lifted
    | n + 1 => do
      let ((decls, is), nfs) <- lowerTop1 decls[ds - i] ctors E.tyDecl |>.run is |>.run nfs
      let globals := nfs.externNames.fold (fun s k _ => s.insert k) globals
      let (_, {lifted := lifted',..}) <- ccDecls decls |>.run {is with globals} |>.run' nfs
      go n (lifted ++ lifted') is nfs globals $ Nat.le_of_succ_le h

  let lifted <- go ds #[] {} {} ({matchFailFVar} : FVSet) Nat.le.refl
  liftEIO $ println! Std.ToFormat.format lifted |>.pretty (width := 80)
end CC

section Opt
def optimize1 (nt : Std.HashSet String) (d : Array $ Decl .postCC) : IncrementalM $ Array $ Decl .postCC := do
  let km₀ <- modifyGet fun s@{globals, kmap,..} =>
    let kmap := d.foldl (seedKM.seed1 globals) kmap
    (kmap, {s with kmap})

  let d := d.map $ cfoldDecl nt km₀
  let (ari, gclos) <- modifyGet fun s@{globals, ariMap, closMap,..} => Id.run do
    let mut ariMap  := ariMap
    let mut closMap := closMap

    for d in d do
      ariMap  := seedMaps.seedAri ariMap d
      closMap := seedMaps.seedClos globals closMap ariMap d
    ((ariMap, closMap), {s with ariMap, closMap})

  return d.map $ kocDecl ari gclos

/--
A demonstration of incremental lowering. Note that for convenience the frontend
is not incremental here. Realistically the frontend is the easiest part as their
environments are explicit in the signature. Now implementing REPL targeting IR or
lower is viable performance-wise.

TODO: TCNF direct evaluator/proper VM based REPL.

For the latter we can implement the push/enter model from Peyton Jones' STG.
-/
def checkKOCI (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E@{tyDecl,..}, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (decls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let ds := decls.size
  let newtypes := newtypeCtors tyDecl

  let rec go i lifted is nfs globals (h : i <= ds) :=
    match h' : i with
    | 0 => return lifted
    | n + 1 => do
      let ((decls, is), nfs) <- lowerTop1 decls[ds - i] ctors tyDecl |>.run is |>.run nfs
      let globals := nfs.externNames.fold (fun s k _ => s.insert k) globals
      let ((_, is@{lifted := lifted',..}), nfs) <- ccDecls decls |>.run {is with globals} |>.run nfs
      let lifted' <- optimize1 newtypes lifted' |>.run' is |>.run' nfs
      go n lifted' is nfs globals $ Nat.le_of_succ_le h

  let lifted <- go ds #[] {} {} ({matchFailFVar} : FVSet) Nat.le.refl
  liftEIO $ println! Std.ToFormat.format lifted |>.pretty (width := 80)
end Opt
end Incremental
end TCNF
