import Tigris.coreL.transform

def main (fp : List String) : IO Unit :=
  let PE := initState
  for path in fp do
    try
      let s <- IO.FS.readFile path
      let (_, decls) <- Parsing.parseModuleIR s PE |>.toIO .userError
      let (_, l) <- IO.ofExcept $ MLType.inferToplevel decls MLType.defaultE
      IO.print l
      IO.FS.withFile (path ++ ".ir1") .write fun h =>
        h.putStr $ Std.Format.pretty (width := 80) $ IR.dumpLamModule decls
    catch e => println! Logging.error (toString e)
