import Tigris.codegen.cl

open TCNF.CL

@[extern "lean_mk_symlink"] opaque mk_symlink : @&String -> @&String -> IO Unit
def IO.FS.symlink := mk_symlink.on System.FilePath.toString

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
  [ "fact", "list", "opt", "op-let", "struct"
  , "typeclass4", "typeclass5", "typeclass6"
  , "hkt-dict-parametricity", "hkt-eager-specialize"
  , "poly-ref", "poly-ref-io", "poly-ref-io-safe"]

def normalizeMsg :=
  String.Slice.foldl
    (fun a c => if c.isWhitespace then a.push ' ' else a.push c)
    ""

/-- (stem, expected error substring): must fail to compile with an error
containing the substring. -/
def errorCases : List (String × String) :=
  [ ("kind-error-instance", "Kind mismatch")
  , ("kind-error-overapp", "Kind mismatch")
  , ("kind-error-juxta", "Kind mismatch") ]

open System.FilePath renaming mk -> fp, fileStem -> fn in
def execCases : List (String × System.FilePath × String) :=
  [ (cases/"r1"            , r"(42 15 . 2)")
  , (cases/"tc"            , r"5050")
  , (cases/"seq"           , r"6")
  , (cases/"expr"          , r"260")
  , (examples/"mutual"     , r"5")
  , (examples/"where"      , r"50")
  , (examples/"cont"       , r"42")
  , (examples/"fun"        , r"(40 . 60)")
  , (examples/"neg"        , r"-1")
  , (examples/"diamond"    , r"1")
  , (examples/"statem"     , r"(42 . 2)")
  , (examples/"recency"    , r"(101 . 5)")]
  |>.map fun (p, s) => (name p, p.addExtension "tig", s)
where examples := fp "examples"
      cases    := fp "tests" / "cases"
      name p   := fn p |>.getD p.toString
open IO (mkRef)

def main (paths : List String) : IO UInt32 := do
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
        fail.modify .succ *> eprintln s!"  X\t{name}: {normalizeMsg e}"

  println! "== errors =="
  waitAll =<< errorCases.mapM fun (name, expected) =>
    .asTask $ compileFile s!"{execCases.examples}/{name}.tig" >>=
      fun
      | .ok _ =>
        fail.modify .succ *> eprintln s!"  X\t{name}: expected error beginning with \"{expected}\", but got compiled"
      | .error e =>
        if e.startsWith expected then pass.modify .succ *> println s!"  ok\t{name}\t{normalizeMsg e}"
        else fail.modify .succ *> eprintln s!"  X\t{name}: expected error beginning with \"{expected}\", got {normalizeMsg e}"

  if <- hasSbcl then
    println! "== exec =="
    waitAll =<< execCases.mapM fun (name, path, expected) =>
      .asTask $ compileFile path >>=
        fun
        | .error e =>
          fail.modify .succ *> eprintln s!"  X\t{name}: {normalizeMsg e}"
        | .ok cl =>
          runSbcl cl >>=
            fun
            | .error e =>
              fail.modify .succ *> eprintln s!"  X\t{name}: {e}"
            | .ok got =>
              if got == expected then pass.modify .succ *> println s!"  ok\t{name}\t= {got}"
              else fail.modify .succ *> eprintln s!"  X\t{name}: expected {expected}, got {normalizeMsg got}"
  else
    println! "== exec skipped (sbcl not found) =="

  let pass <- pass.get
  let fail <- fail.get
  println! "\n{pass} passed, {fail} failed"
  if fail > 0 then return 1
  match paths with
  | bindir :: paths =>
    for p in paths do
      let artp := System.FilePath.join.on System.FilePath.mk bindir p
      println! "linking {artp} -> {p}"
      mk_symlink artp.toString p
    return 0
  | _ => return 0

where
  waitAll    {α} : List (Task α) -> IO Unit := (List.forM · waitIgnore)
  waitIgnore {α} : Task α -> IO Unit        := ignore ∘ IO.wait
  ignore     {α} : BaseIO α -> IO Unit      := (· $> ())
