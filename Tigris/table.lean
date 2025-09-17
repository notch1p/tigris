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
    , .str $ truncate widVal $ toString $ VE.getD  k (.VEvalError "⋯ "))

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
  #[ (.str "#dump [x] [y]"    , .str "dump the REPL environment in table form")
   , (.str ""                 , .str "set truncate threshold for table printer")
   , (.str ""                 , .str "(type,val) = (x, y)")
   , (.str "#load <path>+"    , .str "load src from <path> into REPL")
   , (.str ""                 , .byl "<path> is space-separated,")
   , (.str ""                 , .byl "may not contain spaces or ';'")
   , (.str "#edit <args>+"    , .str "open an editor with <args> passed as-is")
   , (.str ""                 , .str "editor is designated by $VISUAL/EDITOR")
   , (.str ""                 , .byl "<args> is space-separated,")
   , (.str ""                 , .byl "may not contain spaces or ';'")
   , (.str "#sync <src>"      , .str "interpret <src> in the main thread")
   , (.str ""                 , .str "by default, evaluation happens in a")
   , (.str ""                 , .str "separate thread, due to limitations,")
   , (.str ""                 , .byl "this does not prevent stackoverflow")
   , (.str ""                 , .byl "from crashing the main thread")
   , (.str "#help"            , .str "show this help string")
   , (.str "#ast <exp|decl>"  , .str "display the parsetree of <exp|decl>")
   , (.str "#tast <exp>"      , .str "display the typed parsetree of <exp>")
   , (.str "#type <exp>"      , .str "typecheck <exp> without evaluating it")
   , (.str ""                 , .str "useful for type reduction")
   , (.str ""                 , .str "on a potentially diverging term")
   , (.str "#flush"           , .str "flush the environment")
   , (.str ""                 , .byl "changes to the env are dropped")
   , (.str "#lam[+opts] <exp>", .str "Compile <exp> to Lambda IR, opts:")
   , (.str ""                 , .blu "⬝ raw: w/o any optimization;")
   , (.str ""                 , .blu "⬝ opt: default, w/ optimizations;")
   , (.str ""                 , .blu "⬝ cc: w/ closure conversion, implies `opt`")
   , (.str ""                 , .byl "use tigrisl for actual compilation.")]

def tiglHelpMsg : TableOf HelpHeader :=
  #[ (.str "-l, --lam"  , .str "prepend CC'd IR with its source IR")
   , (.str "<ifiles>"   , .str "a list of input files read from")
   , (.str "-o <ofiles>", .str "a list of output files written to")
   , (.str ""           , .byl "must match or be smaller than input list")
   , (.str ""           , .str "unmatched inputs use default naming convention")
   , (.str ""           , .blu "i.e. 'file.tig' renames to 'file.tig.ir'")
   , (.str "-h, --help" , .str "show this help string")]
