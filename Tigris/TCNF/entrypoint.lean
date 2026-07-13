import Tigris.TCNF.nflift
import Tigris.TCNF.nftransform
import Tigris.TCNF.nfopt

namespace TCNF open Compiler CC Opt

section Lowering
/-- Lower a whole module (`inferToplevelF` output) to `Module .preCC`. `tyDecls`
supplies constructor field types (for precise binder types); pass `∅` to skip. -/
def lowerModule (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : CompilerM (Module .preCC) := do
  let (fieldTys, ctorTyParams) := ctorTypeInfo tyDecls
  modify ({· with ctors, fieldTys, ctorTyParams, tyDecl := tyDecls})
  let ρ₀ <- collectTopNames decls |>.foldlM (fun ρ nm => (ρ.insert nm ·) <$> internExtern nm) ∅
  let allDecls <- decls.flatMapM (lowerTopDecl ρ₀)
  let main <- match allDecls.findRev? (·.name == "main") with
    | some m => pure m
    | none   => do
      let fv <- internExtern "main"
      pure {fvarId := fv, name := "main", params := #[], ty := MLType.tUnit, body := .ret $ .lit .PUnit}
  return {decls := allDecls.eraseP (·.name == "main"), main}

def lowerModuleTop (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : LowerM (Module .preCC) := lowerModule decls ctors tyDecls |>.run' {}

def checkModF (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, log, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  liftEIO $ IO.print log
  let mod <- lowerModuleTop fdecls ctors E.tyDecl
  liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 60)

/-- Lower a single closed `FExpr` (types stripped) to `Code .preCC`. -/
def lowerToCode (ctors : Std.HashMap String Nat) (e : FExpr) : LowerM CodePre :=
  lower (stripTy e) ∅ .ret |>.run' {ctors}
end Lowering

section CC
/-- Closure-convert a whole module. -/
def ccModule (m : Module .preCC) : CompilerM (Module .postCC) := do
  let {externNames := extern,..} <- get
  let globals : FVSet :=
    let g₀ : FVSet := extern.fold (fun s k _ => s.insert k) {matchFailFVar}
    m.decls.foldl (·.insert ·.fvarId) g₀ |>.insert m.main.fvarId
  let go := (·, ·) <$> m.decls.mapM ccDecl <*> ccDecl m.main
  let (res, lifted) <- go.run {globals} |>.run #[]
  return {decls := res.1 ++ lifted, main := res.2}

/-- Lower a module and closure-convert it in one shared `CompilerM` run. -/
def lowerModuleCC (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : LowerM (Module .postCC) :=
  (lowerModule decls ctors tyDecls >>= ccModule) |>.run' {}

def checkCC (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let mod <- lowerModuleCC fdecls ctors E.tyDecl
  liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 60)
end CC

section Opt
/-- KOC + Constant Folding + dead-closure elimination over a module. -/
def optimizeModule (nt : Std.HashSet String) (m : Module .postCC) : Module .postCC :=
  -- Pass 1: newtype erasure + constant folding
  let globals : FVSet := m.decls.push m.main |>.foldl (·.insert ·.fvarId) ∅
  let km₀ := seedKM globals m
  let m := {decls := m.decls.map (cfoldDecl nt km₀), main := cfoldDecl nt km₀ m.main}
  -- Pass 2: known-call + arity (Decl scoped) + DCE  (globals unchanged by cfold)
  let (ari, gclos) := seedMaps globals m
  {decls := m.decls.map (kocDecl ari gclos), main := kocDecl ari gclos m.main}

def lowerModuleCCOpt (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : LowerM (Module .postCC) :=
  optimizeModule (newtypeCtors tyDecls) <$> lowerModuleCC decls ctors tyDecls

def checkKOC (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let mod <- lowerModuleCCOpt fdecls ctors E.tyDecl
  liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 60)
end Opt
end TCNF
