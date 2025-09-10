import Tigris

open PrettyPrint (tabulate)
open PrettyPrint.Text (mkBoldBlackWhite mkBold)
open MLType (defaultE)
open Interpreter (defaultVE)
open Parsing (parseModule parseModule')
open IO Std.ToFormat

abbrev EvalState := Option (Task (Except Error (CtorMap × PEnv × Env × VEnv)))

--@[extern "lean_read_stdin_line"]
--opaque readTtyLine : IO String

def main : IO Unit := do
  setStdoutBuf false

  let mut prompt := "> "
  let mut buf := ""

  let stdin <- getStdin
  let E <- mkRef defaultE
  let VE <- mkRef defaultVE
  let PE <- mkRef initState
  let CE : IO.Ref CtorMap <- mkRef $ defaultE.tyDecl.fold (init := ∅) fun a _ v =>
    a.insertMany (v.ctors.map fun (name, _, ar) => (name, ar))

  let EVS : IO.Ref EvalState <- mkRef none

  let fd <- installSigintPipe

  if fd >= 0 then
    discard $ asTask (prio := .dedicated) do
      repeat do
        let r <- readFdByte fd
        if r <= 0 then pure ()
        else
          if let some t <- EVS.get then
            IO.cancel t
          else pure ()

  letI motd := "A basic language using Hindley-Milner type system\n\
               with a naive (term-rewriting) interpreted implementation.\n\
               For language specifications see source.\n\
               USAGE\n  \
               ⬝ Type #help;; to check available commands.\n  \
               ⬝ Exit with <C-d> or <C-z-Ret> (Windows).\n  \
               ⬝ Interrupt with <C-c> (doesn't work if\n    \
                 running through `lake exe`)"
  println! motd

  repeat do
    let pe <- PE.get
    let e <- E.get
    let ve <- VE.get
    let ctorE <- CE.get

    print prompt
    prompt := "- "

    let input <- stdin.getLine --readTtyLine
    if input.isEmpty then IO.Process.exit 0
    buf := buf ++ input |>.trimLeft
    if !input.trimRight.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    /- help -/
    if buf.startsWith "#h" then
      print $ tabulate (mkBoldBlackWhite "Commands") {align := alignH} helpMsg
    /- flush -/
    else if buf.startsWith "#f" then
      PE.set initState *> VE.set defaultVE *> E.set defaultE
      println! Logging.note "REPL environment has been flushed"
    /- call $EDITOR/VISUAL -/
    else if buf.startsWith "#e" then
      let fp := buf.dropRightWhile (fun c => c.isWhitespace || c == ';') |>.splitOn " " |>.tail
      try
        let some editor <- (· <|> ·) <$> getEnv "VISUAL" <*> getEnv "EDITOR"
                        | throwServerError "env $EDITOR has not been set"
        let p <- Process.spawn {cmd := editor, args := fp.toArray}
        () <$ p.wait
      catch e => println! Logging.error $ toString e
    /- compiles to IR₀ -/
    else if buf.startsWith "#lam" then
      let sbuf := buf.extract ⟨4⟩ buf.endPos
      let runner :=
        if sbuf.startsWith "+raw" then IR.fmtLExpr ∘ IR.toLamT ctorE
        else if sbuf.startsWith "+cc" then IR.fmtModule ∘ IR.toLamModuleT1 ctorE
        else IR.fmtLExpr ∘ IR.toLamTO ctorE
      try
        let exp <- Parsing.parse (sbuf.dropWhile $ not ∘ Char.isWhitespace) pe |> ofExcept
        let (e, _, l) <- MLType.runInferT1 exp e |> ofExcept
        print l
        runner e |> IO.println
      catch e => println! Logging.error $ toString e
    /- dump typedtree -/
    else if buf.startsWith "#ta" then
      (Parsing.typeExpr (buf.dropWhile $ not ∘ Char.isWhitespace) pe e |>.toIO') >>= fun
      | .ok b  => println! reprStr b
      | .error e => println! Logging.error $ toString e
    /- typecheck w/o evaluation -/
    else if buf.startsWith "#t" then
      try
        let exp <- Parsing.parse (buf.dropWhile $ not ∘ Char.isWhitespace) pe |> ofExcept
        let (s, l) <- MLType.runInfer1 exp e |> ofExcept
        print l
        println! (format s) |>.pretty 160
      catch e => println! Logging.error $ toString e
    /- dump parsetree -/
    else if buf.startsWith "#a" then
      (parseModule' (buf.dropWhile $ not ∘ Char.isWhitespace) pe |>.toIO') >>= fun
      | .ok (_, b)  => println! reprStr b
      | .error e => println! Logging.error $ toString e
    /- dump REPL environemnt -/
    else if buf.startsWith "#d" then
      let args := buf.splitOn " " |>.filterMap fun s => s.toNat?
      let (x, y) := match args with | [] => (30, 40) | x :: y :: _ => (x, y) | x :: _ => (x, x)
      println $ tabulate (mkBoldBlackWhite "REPL Environment") {align := alignE} $ genTable e x y ve
      print $ tabulate
        (mkBoldBlackWhite "Operators" ++ mkBold "\n(virtually function application has max precedence)")
        {align := alignPE} $ genTableOp pe.ops
    /- load source files -/
    else if buf.startsWith "#l" then
      (buf.splitOn " ").tail |>.forM fun path => do
        if !path.isEmpty then
          try
            let fs <- FS.readFile $ path.dropRightWhile fun c => c.isWhitespace || c == ';'
            let t <- asTask (interpret pe e ve fs ctorE) 5
            EVS.set $ some t
            let (ctorE, PE', E', VE') <- ofExcept =<< (wait t |>.toIO)
            PE.set PE' *> E.set E' *> VE.set VE' *> CE.set ctorE
          catch e =>
            println! Logging.error $ toString e
            println! Logging.warn  $
              "Evaluation context is restored as there are errors.\n\
               Fix those then #load again to update it."
          finally EVS.set none
    /- synced evaluation -/
    else if buf.startsWith "#s" then
      try
        let (ctorE, PE', E', VE') <- interpret pe e ve (buf.dropWhile (not ∘ Char.isWhitespace)) ctorE
        PE.set PE' *> E.set E' *> VE.set VE' *> CE.set ctorE
      catch e => println! Logging.error $ toString e
    /- defaults to threaded evaluation -/
    else try
      let t <- asTask (interpret pe e ve buf ctorE) 5
      EVS.set $ some t
      let (ctorE, PE', E', VE') <- ofExcept =<< (wait t |>.toIO)
      PE.set PE' *> E.set E' *> VE.set VE' *> CE.set ctorE
    catch e => println! Logging.error $ toString e
    finally
      EVS.set none

    buf := ""
    prompt := "> "

