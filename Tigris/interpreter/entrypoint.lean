import Tigris.parsing.pexp
import Tigris.typing.typing
import Tigris.parsing.ptype
import Tigris.typing.types
import Tigris.parsing.types

namespace Parsing open Lexing Parser PType
abbrev TopDecl := Binding ⊕ TyDecl
def declaration : TParser TopDecl := first'
  #[ tyDecl <|> tyEmpty
   , value parseExpr
   , letrecPointedDecl
   , letPointedDecl
   , letrecDecl
   , letDecl
   , infixlDecl
   , infixrDecl
   ]

def module : TParser $ Array TopDecl :=
  sepBy (optional END) declaration <* optional END

def parse (s : String) : Except String Expr :=
  match spaces *> parseExpr <* endOfInput |>.run s |>.run' initState with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule (s : String) : EStateM String PEnv (Array TopDecl) := do
  match spaces *> module <* endOfInput |>.run s |>.run (<- get) with
  | (.ok _ t, s)    => set s *> pure t
  | (.error _ e, _) => throw (toString e)

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
