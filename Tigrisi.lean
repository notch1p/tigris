import Tigris.TCNF.interpreter.app
import Tigris.table
open IO TCNF.Interpreter.App Std PrettyPrint

abbrev REPLState := Option
                  $ Task
                  $ Except IO.Error
                  $ EvalState

def strip : String.Slice -> String.Slice :=
    .trimAsciiStart
  ∘ .dropEndWhile (pat := fun c => c.isWhitespace || c == ';')
  ∘ .dropWhile    (pat := not ∘ Char.isWhitespace)

def parsePred (s : String.Slice) (pe : PEnv) : IO (List TV × Pred × List Pred) :=
  match runST fun _ => parseInstScheme <* Parser.endOfInput |>.run s |>.run' (pe, "") with
  | Parser.Result.ok _ p => return p
  | Parser.Result.error _ e => throwServerError $ toString e
where parseInstScheme {σ} : TParser σ (List TV × Pred × List Pred) :=
  Parsing.PType.tyScheme >>= fun (.Forall vs preds ty) =>
    match ty.getRightmost with
    | .TApp (.TCon cname) args => return (vs, ⟨cname, args⟩, preds)
    | .TCon cname              => return (vs, ⟨cname, []⟩, preds)
    | ty => Parser.throwUnexpectedWithMessage (msg := s!"not a valid class: {ty} is not of form C a₁ ...")

def main (fs : List String) : IO Unit := do
  setStdoutBuf false

  unless fs.isEmpty do
    TCNF.Interpreter.main fs
    return

  letI motd := "A direct interpreter for the Tigris Language targeting Opt/CC'd TCNF.\n\
                For an outdated language specifications see docs/* or my thesis.\n\
                USAGE\n  \
                ⬝ tigrisi [..files]\n  \
                ⬝ Type #help;; to check available commands.\n  \
                ⬝ Exit with <C-d> or <C-z-Ret> (Windows).\n  \
                ⬝ Interrupt with <C-c> (doesn't work if\n    \
                  running through `lake exe`)"
  println! motd

  let mut prompt := "> "
  let mut buf := ""

  let stdin <- IO.getStdin
  let esRef : IO.Ref EvalState <- mkRef {}
  let rsRef : IO.Ref REPLState <- mkRef none

  let fd <- installSigintPipe

  if fd >= 0 then
    discard $ asTask (prio := .dedicated) do
      repeat do
        let r <- readFdByte fd
        if r <= 0 then pure ()
        else
          if let some t <- rsRef.get then
            IO.cancel t
          else pure ()

  repeat do
    let es <- esRef.get
    print prompt
    prompt := "- "

    let input <- stdin.getLine --readTtyLine
    if input.isEmpty then IO.Process.exit 0
    buf := buf ++ input |>.trimAsciiStart |>.toString
    if !input.trimAsciiEnd.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    if buf.startsWith "#h" then
      print $ tabulate (Text.mkBoldBlackWhite "Commands") {align := alignH} tigiMsg

    else if buf.startsWith "#f" then
      esRef.set {}
      println! "REPL environment has been flushed"
    else if buf.startsWith "#s" then
      try
        let sbuf := strip buf
        let (vs, p, ctx) <- parsePred sbuf es.PE
        if vs.isEmpty then
          let (.Ascribe (.Var inst) _) <- Resolve.resolvePred es.E p |> IO.ofExcept
                                         | throwServerError "#synth: impossible"
          println! inst
        else
          -- mirror inferInstanceDecl
          let sk := vs.foldl (fun s v => s.insert v (ConstraintInfer.mkSkol v)) (∅ : Subst)
          let inst <- Resolve.matchHead es.E {p with args := Rewritable.apply sk p.args }
                   |> IO.ofExcept
          let headTy := MLType.mkApp (.TCon p.cls) p.args
          let sch := .Forall vs ctx headTy
          let some isch := es.E.E[inst]? | throwServerError "#synth: impossible"
          let _ <- ConstraintInfer.unify (KindEnv.ofEnv es.E) (.TSch sch) (.TSch isch) |> IO.ofExcept
          let (fe, _) <- runInfer1F (.Var inst headTy) sch es.E |> IO.ofExcept
          println! format fe
      catch e => println! e
    else if buf.startsWith "#d" then
      let sbuf := strip buf
      let query :=
        if sbuf.startsWith "#"
        then es.is.globaldecls.get? (sbuf.drop 1 |>.toNat?.getD 0)
        else es.optDecls.find? sbuf.toString
      match query with
      | some d => println! format d
      | none   => println! s!"Unbound symbol/fvar {sbuf}"
    else if buf.startsWith "#t" || buf.startsWith "#c" then
      try
        let e <- Parsing.parse (buf.dropWhile $ not ∘ Char.isWhitespace) es.PE
              |> IO.ofExcept
        if buf.startsWith "#ta" then
          let (fe, _, _) <- runInferConstraintF e es.E |> IO.ofExcept
          println! format fe
        else
          let (_, s, _) <- runInferConstraintT e es.E |> IO.ofExcept
          println! format s
      catch e => println! e
    else if buf.startsWith "#a" then
      (Parsing.parseModule' (buf.dropWhile $ not ∘ Char.isWhitespace) es.PE |>.toIO') >>= fun
      | .ok (_, b)  => println! reprStr b
      | .error e    => println! Logging.error $ toString e
    else if buf.startsWith "#l" then
      try
        let sbuf <- FS.readFile $ toString $ strip buf
        let t <- asTask $ Prod.snd <$> (EIO.toIO .userError $ evaluate1 sbuf |>.run es)
        rsRef.set $ some t
        let st <- IO.ofExcept =<< wait t
        esRef.set st
      catch e =>
        println! e
        println! "Evaluation context is restored as there are errors.\n\
                  Fix those then #load again to update it."
      finally rsRef.set none
    else
      try
        let t <- asTask $ Prod.snd <$> (EIO.toIO .userError $ evaluate1 buf |>.run es)
        rsRef.set $ some t
        let st <- IO.ofExcept =<< wait t
        esRef.set st
      catch e => println! e
      finally rsRef.set none

    buf := ""
    prompt := "> "
