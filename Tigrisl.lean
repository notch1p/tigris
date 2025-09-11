import Tigris.core.transform
import Tigris.table

def validate args := do
  if let some (ir?, is, os) <- argParser false [] [] args then
    if is.size = 0 then IO.throwServerError "no input files"
    else if is.size < os.size then IO.throwServerError s!"received {is.size} file(s) but need {os.size}"
    else
      let left := is.foldl (Array.push · $ String.append · ".ir") #[] os.size
      return some (ir?, is, os ++ left)
  else return none
where argParser (b : Bool) (is : List String) (os : List String)
  : List String -> IO (Option (Bool × Array String × Array String))
  | [] => return some (b, is.foldr (flip Array.push) #[], #[])
  | "-h" :: _ | "--help" :: _ => return none
  | "-l" :: xs | "--lam" :: xs => argParser true is os xs
  | "-o" :: xs =>
    (b, is.foldr (flip Array.push) #[], ·) <$> xs.foldrM (init := #[]) fun s a =>
      if s.startsWith "-"
      then IO.throwServerError s!"flag {s} must come before positional vararg '-o'"
      else return a.push s
  | x :: xs => argParser b (x :: is) os xs

def main (fp : List String) : IO Unit := do
  let PE := initState
  if let some (ir?, is, os) <- validate fp then
    for i in is, o in os do
      try
        let s <- IO.FS.readFile i
        let (_, decls) <- Parsing.parseModuleIR s PE |>.toIO .userError
        let (decls, _, l) <- IO.ofExcept $ MLType.inferToplevelT decls MLType.defaultE
        IO.print l
        IO.FS.withFile o .write fun h => do
          let (ir, cc) := IR.dumpLamModuleT decls

          if ir? then
            h.putStrLn "NB. == Optimized IR =="
            h.putStrLn $ Std.Format.pretty (width := 80) $ ir
            h.putStrLn "\nNB. == Above CC'd =="

          h.putStrLn $ Std.Format.pretty (width := 80) $ cc
      catch e => println! Logging.error (toString e)
  else
    println! "Tigris IR₀ compiler"
    println! "USAGE:\n  tigrisl [FLAGS] <ifiles> [-o <ofiles>]"
    println! "FLAGS & ARGS:"
    println! PrettyPrint.tabulate
      "tigrisl"
      {align := (.left, .left), header? := false}
      tiglHelpMsg
