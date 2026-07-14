import Tigris.oldcps.ctransform
import Tigris.codegen.sbcl
import Tigris.table
import Tigris.oldcore2.ftransform
import runtime
import Tigris.codegen.cl

open IO
open TCNF (lowerModule lowerModuleCCOpt)
open TCNF.CL (compileToCL)
open Std.ToFormat (format)

structure ArgParserFlag where
  lam?     : Bool := false
  lamcc?   : Bool := false
  tcnf?    : Bool := false
  tcnfcc?  : Bool := false
  tcnfopt? : Bool := false
  speed    : Nat  := 3
  debug    : Nat  := 0
  safety   : Nat  := 0
  entry?   : Bool := true
  lamcps?  : Bool := false
  legacy?  : Bool := false
  lambda?  : Bool := false
  sysf?    : Bool := false
  cl?      : Bool := true
  fasl?    : Bool := false
  objs     : Array String := #["ffi.lisp"]

def lowerIO : EIO String α -> IO α := EIO.toIO .userError
local macro "lowerIO!" act:term : term => ``(lowerIO $act)

def mkSBCL (ifile ofile sbcl : String) : Process.SpawnArgs where
  cmd := sbcl
  args := #[ "--noinform"
           , "--non-interactive"
           , "--eval"
           , s!"(compile-file {repr ifile} \
                  :block-compile t \
                  :output-file {repr ofile} \
                  :verbose t)"]

def spawnSBCL (ifile ofile : String) : IO Process.Output :=
  Option.getD (dflt := "sbcl") <$> getEnv "SBCL"
  >>= Process.output ∘ mkSBCL ifile ofile
def validate args := do
  if let some (spec, is, os) <- argParser {} [] [] args then
    if is.size = 0 then return none
    else if is.size < os.size then throwServerError s!"received {is.size} file(s) but need {os.size}"
    else
      let left :=
        let ext := if spec.fasl? then ".fasl" else ".lisp"
        is.foldl (Array.push · $ String.append · ext) #[] os.size
      return some (spec, is, os ++ left)
  else return none
where argParser (spec : ArgParserFlag) (is : List String) (os : List String)
  : List String -> IO (Option (ArgParserFlag × Array String × Array String))
  | [] => return some (spec, is.foldr (flip Array.push) #[], #[])
  | "-h" :: _   | "--help" :: _ => return none
  | "--lam" :: xs => argParser {spec with lam? := true} is os xs
  | "--legacy" :: xs => argParser {spec with legacy? := true} is os xs
  | "--lambda" :: xs | "--cwc" :: xs => argParser {spec with lambda? := true} is os xs
  | "--tcnf" :: xs => argParser {spec with tcnf? := true} is os xs
  | "--cc" :: xs => argParser {spec with tcnfcc? := true} is os xs
  | "--speed" :: x :: xs => argParser {spec with speed := x.toNat!} is os xs
  | "--debug" :: x :: xs => argParser {spec with debug := x.toNat!} is os xs
  | "--safety" :: x :: xs => argParser {spec with safety := x.toNat!} is os xs
  | "--opt" :: xs => argParser {spec with tcnfopt? := true} is os xs
  | "--sysf" :: xs => argParser {spec with sysf? := true} is os xs
  | "--lamcc" :: xs => argParser {spec with lamcc? := true} is os xs
  | "--lamcps" :: xs => argParser {spec with lamcps? := true} is os xs
  | "--fasl" :: xs => argParser {spec with fasl? := true} is os xs
  | "-ne" :: xs | "--no-entry" :: xs => argParser {spec with entry? := false} is os xs
  | "-l" :: x :: xs | "--link" :: x :: xs => argParser {spec with objs := spec.objs.push x} is os xs
  | "-nl" :: xs | "--no-lisp" :: xs => argParser {spec with cl? := false} is os xs
  | "-o" :: xs =>
    (spec, is.foldr (flip Array.push) #[], ·) <$> xs.foldlM (init := #[]) fun a s =>
      if s.startsWith "-"
      then throwServerError s!"flag {s} must come before positional vararg '-o'"
      else return a.push s
  | x :: xs => argParser spec (x :: is) os xs

def withTempFile' [Monad m] [MonadLiftT IO m] (f : FS.Handle -> System.FilePath -> m α)
  : m α := do
  let (handle, path) <- FS.createTempFile
  f handle path

def main (fp : List String) : IO Unit := do
  let PE := initState
  if let some ( { lam?, lamcc?, lambda?, lamcps?
                , tcnf?, tcnfcc?, tcnfopt?
                , speed, debug, safety
                , entry?
                , objs
                , cl?
                , sysf?
                , fasl?
                , legacy?}
              , is
              , os) <- validate fp then
    let workseq : Array $ Task $ Except Error Unit <- Array.foldlM2 (init := #[]) (xs := is) (ys := os) fun a i o =>
      a.push <$> asTask do
        try
          let s <- FS.readFile ⟨i⟩
          let (_, decls) <- Parsing.parseModuleIR s PE |>.toIO .userError
          if o.endsWith ".fasl" || fasl? then
            let temp <- withTempFile' fun h temp => do
              if lambda? then
                let (_, cc) <- do
                  let res <- inferToplevelC decls MLType.defaultE' |> ofExcept
                  let (decls, logger, ctors) <- inferToplevelF res |> ofExcept
                  print s!"{i}: "
                  print logger
                  pure $ IR.toLamModuleF decls ctors
                let mod := CPS.toCPS cc

                h.putStrLn runtime

                objs.forM fun obj =>
                  h.write =<< FS.readBinFile ⟨obj⟩

                let (_, funs, main, drv) := Codegen.CL.emitModule mod (addDriver := entry?)
                h.putStrLn "; hoisted functions"
                h.putStrLn funs
                h.putStrLn "; entrypoint"
                h.putStrLn main
                h.putStrLn "; driver"
                h.putStrLn drv
                h.putStrLn "; script-entrypoint"
                h.putStrLn "(|__start|)"
                h.flush
                pure temp

              else -- TCNF
                let cl <- do
                  let res@(_, {tyDecl,..}, _) <- inferToplevelC decls MLType.defaultE' |> ofExcept
                  let (decls, logger, ctors) <- inferToplevelF res |> ofExcept
                  print s!"{i}: "
                  print logger
                  let mod <- lowerIO! lowerModuleCCOpt decls ctors tyDecl
                  compileToCL mod tyDecl (speed   := speed)
                                         (safety  := safety)
                                         (debug   := debug)
                                         (entry?  := entry?)
                                         (runtime := none)

                h.putStrLn runtime
                objs.forM fun obj => (h.write =<< FS.readBinFile ⟨obj⟩) *> h.flush
                h.putStrLn $ cl.pretty 80
                h.flush
                pure temp

            FS.writeBinFile ⟨o⟩ ∅
            let os <- toString <$> FS.realPath (System.FilePath.mk o)
            let {exitCode, stdout, stderr} <- spawnSBCL temp.toString os
            print stderr
            print stdout
            unless exitCode == 0 do throwServerError s!"Process exited with {exitCode}"
            FS.removeFile temp

          else FS.withFile ⟨o⟩ .write fun h => do

            if lambda? || legacy? then
              let (ir, cc) <- do
                if legacy? then
                  let (decls, _, l) <- ofExcept $ MLType.inferToplevelT decls MLType.defaultE
                  print l
                  pure $ IR.toLamModuleT decls
                else
                  let res <- inferToplevelC decls MLType.defaultE' |> ofExcept
                  let (decls, logger, ctors) <- inferToplevelF res |> ofExcept
                  print logger
                  if sysf? then
                    h.putStrLn ";; == System F IR ==\n"
                    h.putStrLn $ Std.Format.pretty (width := 80) $ unexpandDeclsF decls
                  pure $ IR.toLamModuleF decls ctors

              let mod := CPS.toCPS cc

              if lam? then
                h.putStrLn ";; == Optimized IR ==\n"
                h.putStrLn $ Std.Format.pretty (width := 80) $ IR.fmtModule ir
              if lamcc? then
                h.putStrLn ";; == Optimized IR CC'd ==\n"
                h.putStrLn $ Std.Format.pretty (width := 80) $ IR.fmtModule cc
              if lamcps? then
                h.putStrLn ";; == CPS IR ==\n"
                h.putStrLn $ Std.Format.pretty (width := 80) $ CPS.fmtCModule mod

              h.putStrLn ";; == Runtime =="
              h.putStrLn "(load \"runtime.lisp\")\n"

              objs.forM fun obj =>
                h.putStrLn ";; == Linked Lisp Source ==" *>
                h.putStrLn s!"(load \"{obj}\")\n"

              if cl? then
                h.putStrLn ";; == Common Lisp ==\n"
                let (_, funs, main, drv) := Codegen.CL.emitModule mod (addDriver := entry?)
--                h.putStrLn "; package-defs"
--                h.putStrLn hd
                h.putStrLn "; hoisted functions"
                h.putStrLn funs
                h.putStrLn "; entrypoint"
                h.putStrLn main
                h.putStrLn "; driver"
                h.putStrLn drv

            else -- TCNF
              let res@(_, {tyDecl,..}, _) <- inferToplevelC decls MLType.defaultE' |> ofExcept
              let (decls, logger, ctors) <- inferToplevelF res |> ofExcept
              print s!"{i}: "
              print logger

              if not $ sysf? || tcnf? || tcnfcc? || tcnfopt? then
                -- for RC reasons we branch here.
                -- if no IR is requested (which is common),
                -- there's a higher chance that module transformations be linear,
                -- allowing destructive modifications thanks to Perceus GC
                let clmod <- compileToCL (tyDecl := tyDecl) (speed := speed)
                                         (safety := safety) (debug := debug) (entry? := entry?)
                  =<< lowerIO! lowerModuleCCOpt decls ctors tyDecl

                objs.forM fun obj =>
                  h.putStrLn ";; == Linked Lisp Source ==" *>
                  h.putStrLn s!"(load \"{obj}\")\n"

                h.putStrLn $ clmod.pretty 80
              else
                let (preCC , s) <- lowerIO! lowerModule decls ctors tyDecl |>.run {}
                let (postCC, s) <- lowerIO! TCNF.ccModule preCC |>.run s
                let optmod      := TCNF.optimizeModule (TCNF.newtypeCtors tyDecl) postCC
                let clmod       <- compileToCL optmod tyDecl speed safety debug entry?

                if sysf? then
                  h.putStrLn ";; == System F IR ==\n"
                  h.putStrLn $ unexpandDeclsF decls |>.pretty 80

                if tcnf? then
                  h.putStrLn ";; == TCNF IR ==\n"
                  h.putStrLn $ format preCC |>.pretty 80
                  h.flush

                if tcnfcc? then
                  h.putStrLn ";; == TCNF CC'd ==\n"
                  h.putStrLn $ format postCC |>.pretty 80
                  h.flush

                if tcnfopt? then
                  h.putStrLn ";; == TCNF CC & Optimize'd ==\n"
                  h.putStrLn $ format optmod |>.pretty 80
                  h.flush

                if cl? then
                  h.putStrLn ";; == Runtime =="
                  h.putStrLn "(load \"runtime.lisp\")\n"

                  objs.forM fun obj =>
                    h.putStrLn ";; == Linked Lisp Source ==" *>
                    h.putStrLn s!"(load \"{obj}\")\n" *>

                  h.putStrLn ";; == Common Lisp ==\n"
                  h.putStrLn $ clmod.pretty 80
                  h.flush

        catch e => println! Logging.error (toString e)
    workseq.forM fun task => do if let .error e <- wait task then println! e
  else
    println! "Tigris TCNF/Lambda IR/CL compiler"
    println! "USAGE:\n  tigrisl [FLAGS] <ifiles> [-o <ofiles>]"
    println! "FLAGS & ARGS:"
    IO.print $ PrettyPrint.tabulate
      "tigrisl"
      { align := (.left, .left)
      , header? := false
      , truncate := true
      , margin := 2}
      tiglHelpMsg
    println! "NOTES:"
    println! "- FASL target outputs standalone binary"
    println! "  by concatenating linked sources in specific order."
    println! "- LISP target load linked sources/runtime dynamically."
    println! "DISCUSSIONS:"
    println! "- TCNF is the new, robust IR that takes direct"
    println! "  inspiration from Lean's LCNF and GHC's STG"
    println! "  which also comes with a new codegen that takes"
    println! "  advantages of SBCL's type-hint based optimizations."
    println! "- Lambda is the old IR that is faithful to the eponymous"
    println! "  IR described in Appel's Compiling with Continuations"
    println! "  which also comes with a CPS pass."
    println! "- Both IR are ANF."
