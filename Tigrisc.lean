import Tigris.core.transform

def main (fp : List String) : IO Unit :=
  let PE := initState
  for path in fp do
    try
      let s <- IO.FS.readFile path
      let (_, decls) <- Parsing.parseModule' s PE |>.toIO .userError
      let m := runST fun _ => compileTop decls |>.run' 0
      IO.FS.withFile (path ++ ".ir") .write fun h =>
        h.putStr $ Std.Format.pretty ∘ CPS.fmtModule $ m
    catch e => println! Logging.error (toString e)
