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
  #[ (.str "#dump [x] [y]"      , .str "dump the REPL environment in table form")
   , (.str ""                   , .str "set truncate threshold for (type,val) = (x, y)")
   , (.str "#load <path>+"      , .str "load src from space-separated <path> into REPL")
   , (.str ""                   , .byl "<path> may not contain spaces or semicolon")
   , (.str "#sync <src>"        , .str "interpret <src> in the main thread")
   , (.str ""                   , .str "(input is evaluated in a separate thread by default)")
   , (.str ""                   , .str "due to limitations, stack overflow in a separate thread")
   , (.str ""                   , .byl "WOULD still crash the main thread i.e. the REPL")
   , (.str "#help"              , .str "show this help string")
   , (.str "#ast <exp|decl>"    , .str "display the parsetree of <exp> or <decl>")
   , (.str "#(type|check) <exp>", .str "typecheck <exp> without evaluating it, useful for")
   , (.str ""                   , .str "type reduction on a potentially diverging term")]
