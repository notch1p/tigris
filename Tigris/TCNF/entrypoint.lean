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
      pure { fvarId := fv
           , name   := "main"
           , params := #[]
           , ty     := MLType.tUnit
           , body   := .ret $ .lit .PUnit}
  return {decls := allDecls.eraseP (·.name == "main"), main}

def lowerModuleTop (decls : Array TopDeclF) (ctors : Std.HashMap String Nat) (tyDecls : TyMap)
  : LowerM (Module .preCC) := lowerModule decls ctors tyDecls |>.run' {}

def checkModF (s : String) (main? := true) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, log, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  liftEIO $ IO.print log
  let mod <- lowerModuleTop fdecls ctors E.tyDecl
  if main? then
    liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 80)
  else
    liftEIO $ println! Std.ToFormat.format mod.decls
    |>.pretty (width := 80)

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
  return {decls := lifted ++ res.1 , main := res.2}

/-- Lower a module and closure-convert it in one shared `CompilerM` run. -/
def lowerModuleCC decls ctors tyDecls := (lowerModule decls ctors tyDecls >>= ccModule) |>.run' {}

def checkCC (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let mod <- lowerModuleCC fdecls ctors E.tyDecl
  liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 80)
end CC

section Opt

/-- KOC + Constant Folding + dead-closure elimination over a module.

Note that we do not fuse pass 1 and 2 as the latter's state seeding requires
examining across toplevel decls from pass 1. Fusing them together can cause it
to miss some optimization chances.

Consider tests/cases/tc.tig, whose IR, when fused, is

```lean
let fn#18/2 (x6 : Int, y7 : Int) : Int → Int → Bool =
  let π#8 : Bool = EQⁱ(#6, #7); ret #8

let i_Eq_0#2/0 : Eq Int = let fn#5 : Int → Int → Bool = 𝐂⟦18⟧; ret #5

let rec sumTo#3/2 (n10 : Int, acc11 : Int) : Int → Int → Int =
  let app#13 : Bool = #2(#10, 0);
  ...             --  ^^^^^^^^^^ this is a generic call that was missed by KOC.
```

whereas if decoupled, gets correctly rewritten to `#18(#10, 0)`. Though, to avoid
recursing on the module multiple times, it is possible, and has been done in the
TCNF.Incremental module which fuses the whole IR pipline to some degree through careful factoring.

See TCNF.Incremental.checkKOCI specifically. While we cannot fuse pass 1 & 2 _per-single-let_,
we can certainly fuse them at _binding level_, which is already great since
bindings mostly consists of single let, and a `let...and` binding is almost
exclusively used just for mutual groups, which isn't common at all. Though
that helper is not widely tested, the above counterexample is resolved.
-/
def optimizeModule (nt : Std.HashSet String) (m : Module .postCC) : Module .postCC :=
  -- Pass 1: newtype erasure + constant folding
  let globals : FVSet := m.decls.push m.main |>.foldl (·.insert ·.fvarId) ∅
  let km₀ := seedKM globals m
  let m   := applyPass (cfoldDecl nt km₀) m
  let (ari, gclos) := seedMaps globals m -- seed from pass 1's module
  -- Pass 2: known-call + arity (Decl scoped) + DCE (globals unchanged by cfold)
  applyPass (kocDecl ari gclos) m

@[inherit_doc optimizeModule]
def lowerModuleCCOpt decls ctors tyDecls := optimizeModule (newtypeCtors tyDecls) <$> lowerModuleCC decls ctors tyDecls

@[inherit_doc optimizeModule]
def checkKOC (s : String) : LowerM Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let mod <- lowerModuleCCOpt fdecls ctors E.tyDecl
  liftEIO $ println! Std.ToFormat.format mod |>.pretty (width := 80)
end Opt
end TCNF
