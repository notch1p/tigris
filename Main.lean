import Tigris

open PrettyPrint (tabulate)
open PrettyPrint.Text (mkBoldBlackWhite mkBold)
open MLType (defaultE)
open Interpreter (defaultVE)
open Parsing (parseModule parseModule')
open IO Std.ToFormat

def main : IO Unit := do
  setStdoutBuf false

  let mut prompt := "> "
  let mut buf := ""

  let stdin <- getStdin
  let E <- mkRef defaultE
  let VE <- mkRef defaultVE
  let PE <- mkRef initState
  letI motd := "A basic language using Hindley-Milner type system\n\
               with a naive (term-rewriting) interpreted implementation.\n\
               For language specifications see source.\n\
               Type #help;; to check available commands.\n\
               Exit with <C-c>/<C-d> or <C-z-Ret> (Windows)."
  println! motd

  repeat do
    let pe <- PE.get
    let e <- E.get
    let ve <- VE.get

    print prompt
    prompt := "- "

    let input <- FS.Stream.getLine stdin
    buf := buf ++ input |>.trimLeft

    if input.isEmpty then return ()
    if !input.trimRight.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    if buf.startsWith "#h" then
      print $ tabulate (mkBoldBlackWhite "Commands") {align := alignH} helpMsg
    else if buf.startsWith "#f" then
      PE.set initState *> VE.set defaultVE *> E.set defaultE
      println! Logging.note "REPL environment has been flushed"
    else if buf.startsWith "#e" then
      let fp := buf.dropRightWhile (fun c => c.isWhitespace || c == ';') |>.splitOn " " |>.tail
      try
        let some editor <- (· <|> ·) <$> getEnv "VISUAL" <*> getEnv "EDITOR"
                        | throwServerError "env $EDITOR has not been set"
        let p <- Process.spawn {cmd := editor, args := fp.toArray}
        () <$ p.wait
      catch e => println! Logging.error $ toString e
    else if buf.startsWith "#lam" then
      let sbuf := buf.extract ⟨4⟩ buf.endPos
      let runner :=
        if sbuf.startsWith "+raw" then IR.fmtLExpr ∘ IR.toLam1
        else if sbuf.startsWith "+cc" then IR.fmtModule ∘ IR.toLamModule1
        else IR.fmtLExpr ∘ IR.toLam1O
      try
        let exp <- Parsing.parse (sbuf.dropWhile $ not ∘ Char.isWhitespace) pe |> ofExcept
        let (_, l) <- MLType.runInfer1 exp e |> ofExcept
        print l
        runner exp |> IO.println
      catch e => println! Logging.error $ toString e
--      CPS.compile1 (buf.dropWhile $ not ∘ Char.isWhitespace) pe e
    else if buf.startsWith "#t" then
      try
        let exp <- Parsing.parse (buf.dropWhile $ not ∘ Char.isWhitespace) pe |> ofExcept
        let (s, l) <- MLType.runInfer1 exp e |> ofExcept
        print l
        println! (format s) |>.pretty 160
      catch e => println! Logging.error $ toString e
    else if buf.startsWith "#a" then
      (parseModule' (buf.dropWhile $ not ∘ Char.isWhitespace) pe |>.toIO') >>= fun
      | .ok (_, b)  => println! reprStr b
      | .error e => println! Logging.error $ toString e
    else if buf.startsWith "#d" then
      let args := buf.splitOn " " |>.filterMap fun s => s.toNat?
      let (x, y) := match args with | [] => (30, 40) | x :: y :: _ => (x, y) | x :: _ => (x, x)
      println $ tabulate (mkBoldBlackWhite "REPL Environment") {align := alignE} $ genTable e x y ve
      print $ tabulate
        (mkBoldBlackWhite "Operators" ++ mkBold "\n(virtually function application has max precedence)")
        {align := alignPE} $ genTableOp pe.ops
    else if buf.startsWith "#l" then
      (buf.splitOn " ").tail |>.forM fun path => do
        if !path.isEmpty then
          try
            let fs <- FS.readFile $ path.dropRightWhile fun c => c.isWhitespace || c == ';'
            let t <- asTask (interpret pe e ve fs) .dedicated
            let (PE', E', VE') <- ofExcept =<< (wait t |>.toIO)
            PE.set PE' *> E.set E' *> VE.set VE'
          catch e =>
            println! Logging.error $ toString e
            println! Logging.warn  $
              "Evaluation context is restored as there are errors.\n\
               Fix those then #load again to update it."
    else if buf.startsWith "#s" then
      try
        let (PE', E', VE') <- interpret pe e ve $ buf.dropWhile (not ∘ Char.isWhitespace)
        PE.set PE' *> E.set E' *> VE.set VE'
      catch e => println! Logging.error $ toString e
    else try
      let t <- asTask (interpret pe e ve buf) .dedicated
      let (PE', E', VE') <- ofExcept =<< (wait t |>.toIO)
      PE.set PE' *> E.set E' *> VE.set VE'
    catch e => println! Logging.error $ toString e

    buf := ""
    prompt := "> "
