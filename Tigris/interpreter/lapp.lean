import Tigris.interpreter.entrypoint
import Tigris.interpreter.leval
import Tigris.core.ftransform

structure EInterp where
  PE : PEnv
  E  : Env


def interpreterL (s : String) : IO Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState |>.toIO .userError
  let topdeclC <- inferToplevelC topdecl MLType.defaultE' |> IO.ofExcept
  let (topdeclF, logger, ctors) <- inferToplevelF topdeclC |> IO.ofExcept
  println! logger
  let (_, cc) := IR.toLamModuleF topdeclF ctors
  let val <- LInterpreter.evalModule cc |>.toIO $ .userError ∘ toString
  println! val


