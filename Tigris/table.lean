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

def EnvHeader : List Text.SString := ["id", "type", "value"].map fun s => ⟨s, {style := [.bold]}⟩
def alignE : Align EnvHeader := (left, left, right)
def genTable (E : Env) (widTy : Nat) (widVal : Nat) : VEnv -> TableOf EnvHeader
  | {env := VE} => E.1.keysArray.map fun (k : String) =>
    ( .str k
    , .str $ truncate widTy  $ toString $ E.1.get! k
    , .str $ truncate widVal $ toString $ VE.get!  k)

def PEnvHeader : List Text.SString := ["op", "prec", "assoc"].map fun s => ⟨s, {style := [.bold]}⟩
def genTableOp (PE : OpTable) : TableOf PEnvHeader :=
  PE.values.foldl (init := #[]) fun a {sym, prec, assoc,..} =>
    a.push
      ( .str sym
      , ⟨toString prec, [], .cyan, .defaultColor⟩
      , ⟨toString assoc, [], .magenta, .defaultColor⟩)
def alignPE : Align PEnvHeader := (left, right, left)

def HelpHeader : List Text.SString := ["cmd", "info"].map fun s => ⟨s, {style := [.bold]}⟩
def alignH : Align HelpHeader := (right,left)
def helpMsg : TableOf HelpHeader :=
  #[ ("#dump", "dump the REPL environment in table form")
   , ("#load <path>+", "load src from <path>+ (that doesn't contain spaces) into REPL")
   , ("#help", "show this help string")
   , ("#ast <exp|decl>", "display the parsetree of <exp> or <decl>")].map fun s => s.map .str .str
