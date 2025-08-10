import PP.dependentPP
import Tigris.parsing.types
import Tigris.typing.types
import Tigris.interpreter.types

open PrettyPrint Alignment

def EnvHeader := ["id", "type", "value"]
def alignE : Align EnvHeader := (left, left, right)
def genTable (E : Env) : VEnv -> TableOf EnvHeader
  | {env := VE} => E.keysArray.map fun k =>
    (k, toString $ E.get! k, toString $ VE.get! k)

def PEnvHeader := ["op", "prec", "assoc"]
def genTableOp (PE : OpTable) : TableOf PEnvHeader :=
  PE.fold (init := #[]) fun a sym {prec, assoc,..} =>
    a.push (sym, toString prec, toString assoc)
def alignPE : Align PEnvHeader := (left, right, left)

def HelpHeader := ["cmd", "info"]
def alignH : Align HelpHeader := (right,left)
def helpMsg : TableOf HelpHeader :=
  #[ ("#dump", "dump the REPL environment in table form")
   , ("#load <path>+", "load src from <path>+ (that doesn't contain spaces) into REPL")
   , ("#help", "show this help string")
   , ("#ast <exp|decl>", "display the parsetree of <exp> or <decl>")]

