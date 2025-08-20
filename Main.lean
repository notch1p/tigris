import Tigris

open PrettyPrint (tabulate)
open PrettyPrint.Text (mkBoldBlackWhite mkBold)
open MLType (defaultE)
open Interpreter (defaultVE)
open Parsing (parseModule parseModule')
open IO

def main : IO Unit := do
  setStdoutBuf false

  let motd := "A basic language using Hindley-Milner type system\n\
               with a naive (term-rewriting) interpreted implementation.\n\
               For language specifications see source.\n\
               Type #help;; to check available commands.\n\
               To exit press <C-d> (Unix) or <C-z> if on Windows."
  let mut prompt := "λ> "
  let mut buf := ""

  let stdin <- IO.getStdin
  let E <- mkRef defaultE
  let VE <- mkRef defaultVE
  let PE <- mkRef Parsing.initState
  println! motd

  repeat do
    let pe <- PE.get
    let e <- E.get
    let ve <- VE.get

    print prompt
    prompt := ".. "

    let input <- FS.Stream.getLine stdin
    buf := buf ++ input |>.trimLeft

    if input.isEmpty then return ()
    if !input.trimRight.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    if buf.startsWith "#help" then
      print $ tabulate (mkBoldBlackWhite "Commands") {align := alignH} helpMsg
    else if buf.startsWith "#c" || buf.startsWith "#t" then
      try
        let exp <- Parsing.parse (buf.dropWhile $ not ∘ Char.isWhitespace) pe |> ofExcept
        let (s, l) <- MLType.runInfer1 exp e |> ofExcept
        print l
        println! s.render
      catch e => println! e
    else if buf.startsWith "#a" then
      (parseModule' (buf.dropWhile $ not ∘ Char.isWhitespace) pe |>.toIO') >>= fun
      | .ok (_, b)  => println! reprStr b
      | .error e => println! e
    else if buf.startsWith "#d" then
      println $ tabulate (mkBoldBlackWhite "REPL Environment") {align := alignE} $ genTable e ve
      print $ tabulate
        (mkBoldBlackWhite "Operators" ++ mkBold "\n(virtually function application has max precedence)")
        {align := alignPE} $ genTableOp pe.ops
    else if buf.startsWith "#l" then
      (buf.splitOn " ").tail |>.forM fun path => do
        if !path.isEmpty then
          try
            let fs <- FS.readFile $ path.takeWhile fun c => c != ';' && !c.isWhitespace
            let (PE', E', VE') <- interpret pe e ve fs
            PE.set PE' *> E.set E' *> VE.set VE'
          catch e =>
            println! toString e
            println! Logging.warn $
              "Evaluation context is restored as there are errors.\n\
               Fix those then #load again to update it."
    else try
      let (PE', E', VE') <- interpret pe e ve buf
      PE.set PE' *> E.set E' *> VE.set VE'
    catch e => println! e

    buf := ""
    prompt := "λ> "
