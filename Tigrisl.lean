import Tigris.cps.ctransform
import Tigris.codegen.sbcl
import Tigris.table
import Tigris.core.ftransform

open IO

structure ArgParserFlag where
  lam?    : Bool := false
  lamcc?  : Bool := false
  entry?  : Bool := true
  cps?    : Bool := false
  legacy? : Bool := false
  sysf?   : Bool := false
  cl?     : Bool := true
  fasl?   : Bool := false
  ffi?    : Option String := "ffi.lisp"

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
  | "--sysf" :: xs => argParser {spec with sysf? := true} is os xs
  | "--cc" :: xs => argParser {spec with lamcc? := true} is os xs
  | "--cps" :: xs => argParser {spec with cps? := true} is os xs
  | "--fasl" :: xs => argParser {spec with fasl? := true} is os xs
  | "-ne" :: xs | "--no-entry" :: xs => argParser {spec with entry? := false} is os xs
  | "-lf" :: x :: xs | "--link-ffi" :: x :: xs => argParser {spec with ffi? := x} is os xs
  | "-nlf" :: xs | "--no-link-ffi" :: xs => argParser {spec with ffi? := none} is os xs
  | "-nel" :: xs | "--no-emit-lisp" :: xs => argParser {spec with ffi? := none} is os xs
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
  if let some ( { lam?
                , lamcc?
                , entry?
                , cps?
                , ffi?
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
              let (_, cc) <- do
                let res <- inferToplevelC decls MLType.defaultE' |> ofExcept
                let (decls, logger, ctors) <- inferToplevelF res |> ofExcept
                print logger
                pure $ IR.toLamModuleF decls ctors
              let mod := CPS.toCPS cc

              if let some ffip := ffi? then
                h.write =<< FS.readBinFile ffip

              h.putStrLn ";; == Common Lisp ==\n"
              let (_, funs, main, drv) := Codegen.CL.emitModule mod (addDriver := entry?)
              h.putStrLn "; hoisted functions"
              h.putStrLn funs
              h.putStrLn "; entrypoint"
              h.putStrLn main
              h.putStrLn "; driver"
              h.putStrLn drv
              pure temp

            FS.writeBinFile ⟨o⟩ ∅
            let os <- toString <$> FS.realPath (System.FilePath.mk o)
            let {exitCode, stdout, stderr} <- spawnSBCL temp.toString os
            print stderr
            print stdout
            unless exitCode == 0 do throwServerError s!"Process exited with {exitCode}"
            FS.removeFile temp

          else FS.withFile ⟨o⟩ .write fun h => do
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
            if cps? then
              h.putStrLn ";; == CPS IR ==\n"
              h.putStrLn $ Std.Format.pretty (width := 80) $ CPS.fmtCModule mod

            if let some ffip := ffi? then
              h.putStrLn ";; == external FFI ==\n"
              h.putStrLn s!"(load \"{ffip}\")\n"

            if cl? then
              h.putStrLn ";; == Common Lisp ==\n"
              let (_, funs, main, drv) := Codegen.CL.emitModule mod (addDriver := entry?)
--              h.putStrLn "; package-defs"
--              h.putStrLn hd
              h.putStrLn "; hoisted functions"
              h.putStrLn funs
              h.putStrLn "; entrypoint"
              h.putStrLn main
              h.putStrLn "; driver"
              h.putStrLn drv
        catch e => println! Logging.error (toString e)
    workseq.forM fun task => do if let .error e <- wait task then println! e
  else
    println! "Tigris IR₀/IR₁/CL compiler"
    println! "USAGE:\n  tigrisl [FLAGS] <ifiles> [-o <ofiles>]"
    println! "FLAGS & ARGS:"
    IO.print $ PrettyPrint.tabulate
      "tigrisl"
      {align := (.left, .left), header? := false}
      tiglHelpMsg

