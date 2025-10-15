import Tigris.cps.ctransform
import Tigris.codegen.sbcl
import Tigris.table
import Tigris.core.ftransform

structure ArgParserFlag where
  lam?    : Bool := false
  lamcc?  : Bool := false
  entry?  : Bool := true
  cps?    : Bool := false
  legacy? : Bool := false
  sysf?   : Bool := false
  cl?     : Bool := true
  ffi?    : Option String := "ffi.lisp"

def validate args := do
  if let some (spec, is, os) <- argParser {} [] [] args then
    if is.size = 0 then return none
    else if is.size < os.size then IO.throwServerError s!"received {is.size} file(s) but need {os.size}"
    else
      let left := is.foldl (Array.push · $ String.append · ".lisp") #[] os.size
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
  | "-ne" :: xs | "--no-entry" :: xs => argParser {spec with entry? := false} is os xs
  | "-lf" :: x :: xs | "--link-ffi" :: x :: xs =>
    argParser {spec with ffi? := x} is os xs
  | "-nlf" :: xs | "--no-link-ffi" :: xs => argParser {spec with ffi? := none} is os xs
  | "-nel" :: xs | "--no-emit-lisp" :: xs => argParser {spec with ffi? := none} is os xs
  | "-o" :: xs =>
    (spec, is.foldr (flip Array.push) #[], ·) <$> xs.foldrM (init := #[]) fun s a =>
      if s.startsWith "-"
      then IO.throwServerError s!"flag {s} must come before positional vararg '-o'"
      else return a.push s
  | x :: xs => argParser spec (x :: is) os xs
def main (fp : List String) : IO Unit := do
  let PE := initState
  if let some ( { lam?
                , lamcc?
                , entry?
                , cps?
                , ffi?
                , cl?
                , sysf?
                , legacy?}
              , is
              , os) <- validate fp then
    for i in is, o in os do
      try
        let s <- IO.FS.readFile i
        let (_, decls) <- Parsing.parseModuleIR s PE |>.toIO .userError
        IO.FS.withFile o .write fun h => do
          let (ir, cc) <- do
            if legacy? then
              let (decls, _, l) <- IO.ofExcept $ MLType.inferToplevelT decls MLType.defaultE
              IO.print l
              pure $ IR.toLamModuleT decls
            else
              let res <- inferToplevelC decls MLType.defaultE' |> IO.ofExcept
              let (decls, logger, ctors) <- inferToplevelF res |> IO.ofExcept
              IO.print logger
              if sysf? then
                h.putStrLn ";; == System F IR ==\n"
                h.putStrLn $ Std.Format.pretty (width := 80) $ unexpandDeclsF decls
              pure $ IR.toLamModuleF decls ctors

          let mod := CPS.toCPS cc

          if let some ffip := ffi? then
            h.putStrLn ";; == external FFI ==\n"
            h.putStrLn s!"(load \"{ffip}\")\n"

          if lam? then
            h.putStrLn ";; == Optimized IR ==\n"
            h.putStrLn $ Std.Format.pretty (width := 80) $ IR.fmtModule ir
          if lamcc? then
            h.putStrLn ";; == Optimized IR CC'd ==\n"
            h.putStrLn $ Std.Format.pretty (width := 80) $ IR.fmtModule cc
          if cps? then
            h.putStrLn ";; == CPS IR ==\n"
            h.putStrLn $ Std.Format.pretty (width := 80) $ CPS.fmtCModule mod

          if cl? then
            h.putStrLn ";; == Common Lisp ==\n"
            let (_, funs, main, drv) := Codegen.CL.emitModule mod (addDriver := entry?)
--            h.putStrLn "; package-defs"
--            h.putStrLn hd
            h.putStrLn "; hoisted functions"
            h.putStrLn funs
            h.putStrLn "; entrypoint"
            h.putStrLn main
            h.putStrLn "; driver"
            h.putStrLn drv

      catch e => println! Logging.error (toString e)
  else
    println! "Tigris IR₀/IR₁/CL compiler"
    println! "USAGE:\n  tigrisl [FLAGS] <ifiles> [-o <ofiles>]"
    println! "FLAGS & ARGS:"
    println! PrettyPrint.tabulate
      "tigrisl"
      {align := (.left, .left), header? := false}
      tiglHelpMsg

