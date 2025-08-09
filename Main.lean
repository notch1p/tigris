import Tigris

open PrettyPrint (tabulate)
open MLType (defaultE)
open Interpreter (defaultVE)
open Parsing (parseModule)
open IO

def main : IO Unit := do
  setStdoutBuf false

  let motd := "A basic language using Hindley-Milner type system\n\
               with a naive (term-rewriting) interpreted implementation.\n\
               For language specifications see source: Playbook/hm.lean\n\
               Type #help;; to check available commands.\n\
               To exit press <C-d> (Unix) or <C-z> if on Windows."
  let mut prompt := "λ> "
  let mut buf := ""

  let stdin <- IO.getStdin
  let E <- mkRef defaultE
  let VE <- mkRef defaultVE
  let PE <- mkRef Parsing.opTable
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
      print $ tabulate "Commands" {align := alignH} helpMsg
    else if buf.startsWith "#ast" then
      match (parseModule $ buf.drop 4).run pe with
      | .ok b _  => println! reprStr b
      | .error e _ => println! e
    else if buf.startsWith "#dump" then
      println $ tabulate "REPL Environment" {align := alignE}  $ genTable e ve
      print $ tabulate "Operators" {align := alignPE} $ genTableOp pe
    else if buf.startsWith "#load" then
      (buf.splitOn " ").tail |>.forM fun path => do
        if !path.isEmpty then
          try
            let fs <- FS.readFile $ path.takeWhile fun c => c != ';' && !c.isWhitespace
            println fs
            let (PE', E', VE') <- interpret pe e ve fs
            PE.set PE' *> E.set E' *> VE.set VE'
          catch e =>
            println! e;
            println!
              PrettyPrint.Text.bold
                "NOTE: Evaluation context is restore as there are errors.\n\
                 Fix those then #load again to update it." true
    else try
      let (PE', E', VE') <- interpret pe e ve buf
      PE.set PE' *> E.set E' *> VE.set VE'
    catch e => println! e

    buf := ""
    prompt := "λ> "
