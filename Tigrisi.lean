import Tigris.interpreter.lapp
open IO

abbrev EvalState := Option
                  $ Task
                  $ Except Error
                  $ LApp.REPLState × LInterpreter.Val × Scheme

def main : IO Unit := do
  setStdoutBuf false

  let mut prompt := "> "
  let mut buf := ""

  let stdin <- getStdin
  let replST <- mkRef LApp.initREPL
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

  repeat do
    let st <- replST.get

    print prompt
    prompt := "- "

    let input <- stdin.getLine --readTtyLine
    if input.isEmpty then IO.Process.exit 0
    buf := buf ++ input |>.trimLeft
    if !input.trimRight.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    try
      let t <- asTask (LApp.interpretI st buf) 5
      EVS.set $ some t
      let (st, v, sch) <- ofExcept =<< (wait t |>.toIO)
      replST.set st

      print v
      print " : "
      println sch

    catch e => println! Logging.error $ toString e
    finally
      EVS.set none

    buf := ""
    prompt := "> "
