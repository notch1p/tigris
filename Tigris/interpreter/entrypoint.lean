import Tigris.parsing.pexp
import Tigris.typing.typing
import Tigris.parsing.ptype
import Tigris.typing.types
import Tigris.parsing.types
import Tigris.interpreter.types

namespace Parsing open Lexing Parser PType
abbrev TopDecl := Binding ⊕ TyDecl
def declaration : TParser σ TopDecl := first'
  #[ tyDecl <|> tyEmpty
   , value parseExpr
   , letrecPointedDecl
   , letPointedDecl
   , letrecDecl
   , letDecl
   , infixlDecl
   , infixrDecl
   ]
  simpErrorCombine

def module : TParser σ $ Array TopDecl :=
  sepBy (optional END) declaration <* optional END

def parse (s : String) : Except String Expr :=
  match runST fun _ => spaces *> parseExpr <* endOfInput |>.run s |>.run' (initState, "") with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule' (s : String) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  let liftEIO act := IO.toEIO IO.Error.toString act
  match runST fun _ => spaces *> module <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

end Parsing

namespace MLType

def check1 (s : String) (E : Env := defaultE) : String :=
  match Parsing.parse s with
  | .error e => toString e
  | .ok e    =>
    match runInfer1 e E with
    | .error e' => toString e' ++ s!"AST: {reprStr e}"
    | .ok    s => toString s

end MLType
