import Tigris.codegen.cl
import tests.cases
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

section open String.Slice.Pos
def consecutive {s : String.Slice} (p : s.Pos) : s.Pos :=
  if h : p.IsAtEnd then p
  else
     if p.get h |>.isWhitespace then consecutive $ p.next h
     else p
termination_by p

theorem consecutive_le {s : String.Slice} {p : s.Pos}
  : p <= @consecutive s p :=
  if h : p |>.IsAtEnd then by simp[h, consecutive]
  else if h' : p |>.get h |>.isWhitespace
  then have induct : p.next h <= consecutive (p.next h) := consecutive_le
       have : consecutive p = consecutive (p.next h) := by simp [h, h', consecutive.eq_1 p]
       le_trans le_next $ this ▸ induct
  else by simp[h', consecutive]
termination_by p

/- tabulate -/
theorem consecutive_monotone {s : String.Slice} {p : s.Pos} {h : p ≠ s.endPos} {h' : p |>.get h |>.isWhitespace}
  : consecutive p <= consecutive (p.next h) := by
  unfold consecutive; simp[h, h']
  if h'' : p.next h = s.endPos then simp[h'']
  else if h''' : p.next h |>.get h'' |>.isWhitespace then
    have := consecutive_le (p := p.next h)
    have := consecutive_monotone (p := p.next h) (h' := h''')
    have : p <= p.next h := le_next
    grind
  else simp [h'', h''', consecutive]
termination_by p

/--
  similar to | x :: y :: xs => ... recursive_call (y :: xs), awkward but to satisfy termination checking
  normalizes consecutive blanks to just 1
-/
def normalizeMsg (s : String.Slice) : String.Slice := go s.startPos ""
where go p acc :=
  if h : p.IsAtEnd then acc else
    if h' : p.get h |>.isWhitespace then
      if h'' : p.next h |>.IsAtEnd then acc else
        if h''' : p.next h |>.get h'' |>.isWhitespace then

          have : p < consecutive ((p.next h).next h'') := by
            have : p < p.next h := lt_next
            have : p.next h <= consecutive (p.next h |>.next h'') :=
              le_trans (consecutive_le (p := p.next h))
                       (consecutive_monotone (p := p.next h) (h' := h'''))
            grind

          go (consecutive $ p.next h |>.next h'') (acc.push ' ')
        else go (p.next h |>.next h'') $ acc.push ' ' |>.push (p.next h |>.get h'')
    else go (p.next h) $ acc.push $ p.get h
  termination_by p
end

open IO (mkRef)
def main (paths : List String) : IO UInt32 := do
  let pass <- mkRef 0
  let fail <- mkRef 0
  let skip <- mkRef 0
  let stdout <- IO.getStdout
  let println s := IO.println s *> stdout.flush
  let eprintln s := IO.eprintln s *> stdout.flush

  let width := 15
  let pad name := PrettyPrint.pad $ width - name.length

  println "== compile =="
  waitAll =<< compileCases.mapM fun {name, path,..} =>
    .asTask $ compileFile path >>=
      fun        -- modify is atomic
      | .ok _ =>
        pass.modify .succ *> println s!" OK {name}"
      | .error e =>
        fail.modify .succ *> eprintln s!"  X {name}: {normalizeMsg e}"

  println "\n== errors =="
  waitAll =<< errorCases.mapM fun {name, path, expected,..} =>
    .asTask $ compileFile path >>=
      fun
      | .ok _ =>
        fail.modify .succ *> eprintln s!"  X {name}: expected error beginning with \"{expected}\", but got compiled"
      | .error e =>
        if e.startsWith expected
        then if e.length > 40
             then pass.modify .succ *> println s!" OK {name}{pad name}{normalizeMsg e |>.take 40}..."
             else pass.modify .succ *> println s!" OK {name}{pad name}{normalizeMsg e}"
        else fail.modify .succ *> eprintln s!"  X {name}: expected error beginning with \"{expected}\", got {normalizeMsg e}"

  println "\n== exec =="
  waitAll =<< execCases.mapM fun {name, path, expected,..} =>
    .asTask $ compileFile path >>=
      fun
      | .error e =>
        fail.modify .succ *> eprintln s!"  X {name}: {normalizeMsg e}"
      | .ok cl =>
        if expected.isEmpty
        then skip.modify .succ *> eprintln s!"  S {name}{pad name}refer to interpreter output instead"
        else
          runSbcl cl >>=
            fun
            | .error e =>
              fail.modify .succ *> eprintln s!"  X {name}: {normalizeMsg e}"
            | .ok got =>
              let got := normalizeMsg got
              if got == expected.toSlice
              then pass.modify .succ *> println s!" OK {name}{pad name}==> {got}"
              else fail.modify .succ *> eprintln s!"  X {name}: expected {expected}, got {normalizeMsg got}"

  println "\n== exec (Incremental Lowering; Interpreter: evalCEK) =="
  waitAll =<< execCases.mapM fun {name, path, interpreted := v',..} =>
    .asTask $ TCNF.Interpreter.checkFile path false >>=
      fun v =>
        if v == v' then
          let prefixS := s!" OK {name}{pad name}==>"
          pass.modify .succ *> println s!"{prefixS} {v.toFormat |>.pretty (column := prefixS.length + 1) (indent := prefixS.length + 1)}"
        else
          fail.modify .succ *> eprintln s!"X {name}: expected {v'}, got {v}"

  let pass <- pass.get
  let fail <- fail.get
  let skip <- skip.get
  println! "\n{pass} passed, {skip} skipped, {fail} failed"
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
  waitAll    {α} : Array (Task α) -> IO Unit := Array.forM waitIgnore
  waitIgnore {α} : Task α -> IO Unit         := ignore ∘ IO.wait
  ignore     {α} : BaseIO α -> IO Unit       := (· $> ())
