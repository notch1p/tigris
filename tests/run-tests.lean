import Tigris.codegen.cl

open TCNF.CL

/-- Read + compile a source file end-to-end to CL text, or an error message. -/
def compileFile (path : System.FilePath) : IO (Except String String) := do
  try
    let src <- IO.FS.readFile path
    let fmt <- EIO.toIO .userError (compileSource src)
    return .ok fmt.pretty
  catch e => return .error (toString e)

def runSbcl (clText : String) : IO (Except String.Slice String.Slice) :=
  IO.FS.withTempFile fun h tmp => do
    h.putStr clText
    h.flush
    let out <- IO.Process.output
      { cmd := "sbcl"
        args := #["--script", tmp.toString] }
    if out.exitCode == 0 then return .ok out.stdout.trimAscii
    else return .error out.stderr.trimAscii

def hasSbcl : IO Bool := do
  try return (<- IO.Process.output { cmd := "sbcl", args := #["--version"] }).exitCode == 0
  catch _ => return false

def compileCases : List String :=
  [ "fact", "list", "opt", "fun", "op-let", "struct"
  , "typeclass4", "typeclass5", "typeclass6"
  , "hkt-dict-parametricity", "hkt-eager-specialize" ]

open System.FilePath renaming mk -> fp, fileStem -> fn in
def execCases : List (String × System.FilePath × String) :=
  [ (cases / "r1"         , r"(42 15 . 2)")
  , (cases / "tc"         , r"5050")
  , (cases / "seq"        , r"6")
  , (cases/ "expr"        , r"260")
  , (examples / "mutual"  , r"5")
  , (examples / "where"   , r"50")
  , (examples / "cont"    , r"42")
  , (examples / "fun"     , r"(40 . 60)")]
  |>.map fun (p, s) => (name p, p.addExtension "tig", s)
where examples := fp "examples"
      cases    := fp "tests" / "cases"
      name p   := fn p |>.getD p.toString
open IO (mkRef)

def main : IO Unit := do
  let pass <- mkRef 0
  let fail <- mkRef 0
  let stdout <- IO.getStdout
  let println s := IO.println s *> stdout.flush
  let eprintln s := IO.eprintln s *> stdout.flush


  println! "== compile =="
  waitAll =<< compileCases.mapM fun name =>
    .asTask $ compileFile s!"{execCases.examples}/{name}.tig" >>=
      fun        -- modify is atomic
      | .ok _ =>
        pass.modify .succ *> println s!"  ok\t{name}"
      | .error e =>
        fail.modify .succ *> eprintln s!"  X\t{name}: {e.take 160}"

  if <- hasSbcl then
    println! "== exec =="
    waitAll =<< execCases.mapM fun (name, path, expected) =>
      .asTask $ compileFile path >>=
        fun
        | .error e =>
          fail.modify .succ *> eprintln s!"  X\t{name}: compile: {e.take 160}"
        | .ok cl =>
          runSbcl cl >>=
            fun
            | .error e =>
              fail.modify .succ *> eprintln s!"  X\t{name}: {e.take 160}"
            | .ok got =>
              if got == expected then pass.modify .succ *> println s!"  ok\t{name} = {got}"
              else fail.modify .succ *> eprintln s!"  X\t{name}: expected {expected}, got {got}"
  else
    println! "== exec skipped (sbcl not found) =="

  let pass <- pass.get
  let fail <- fail.get
  println! "\n{pass} passed, {fail} failed"
  if fail > 0 then IO.Process.exit 1

where
  waitAll    {α} : List (Task α) -> IO Unit := (List.forM · waitIgnore)
  waitIgnore {α} : Task α -> IO Unit        := ignore ∘ IO.wait
  ignore     {α} : BaseIO α -> IO Unit      := (· $> ())
