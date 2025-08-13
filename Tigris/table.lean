import PP.dependentPP
import Tigris.parsing.types
import Tigris.typing.types
import Tigris.interpreter.types

open PrettyPrint Alignment
/-- truncate a string to length `n - 1`, extracting from both
    ends, separated by "..." (separator length included) -/
def truncate (n : Nat) (s : String) : String :=
  let n := if (n - 2) &&& 1 == 0 then n - 2 else n - 1
  if s.length > n + 2 then
    s.extract ⟨0⟩ ⟨n >>> 1⟩ ++ ".." ++ s.extract ⟨s.length - n >>> 1⟩ ⟨s.length⟩
  else s

def EnvHeader := ["id", "type", "value"]
def alignE : Align EnvHeader := (left, left, right)
def genTable (E : Env) : VEnv -> TableOf EnvHeader
  | {env := VE} => E.1.keysArray.map fun k =>
    (k, toString $ E.1.get! k, truncate 8 $ toString $ VE.get! k)

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
