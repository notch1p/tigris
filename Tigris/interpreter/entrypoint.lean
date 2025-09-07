import Tigris.parsing.pexp
import Tigris.typing.typing
import Tigris.parsing.ptype
import Tigris.typing.types
import Tigris.parsing.types
import Tigris.interpreter.types
namespace Parsing open Lexing Parser PType TopDecl
-- abbrev TopDecl := Binding ⊕ TyDecl
def declaration : TParser σ TopDecl := first'
  #[ tyBind <$> tyDecl false
   , tyBind <$> tyEmpty
   , (idBind ∘ Array.singleton) <$> value parseExpr
   , idBind <$> letDeclDispatch
   , (idBind ∘ Array.singleton) <$> infixlDecl
   , (idBind ∘ Array.singleton) <$> infixrDecl
   ]
  simpErrorCombine

def mutTyDecl : TParser σ $ Array TopDecl := do
  let tysd <- takeMany1 (tyBind <$> tyDecl true)
  let ({undTy,tys,..}, _) <- get
  let undty := undTy.filter (tys.find? · matches some (_, false))
  if let [] := undty then return tysd
  else
    error s!"unresolved types {undTy.map Logging.magenta} must not elide mutual block\n"
    throwUnexpected

def module : TParser σ $ Array TopDecl :=
  sepBy (optional END) declaration <* optional END

def parse (s : String) (PE : PEnv) : Except String Expr :=
  match runST fun _ => parseExpr <* optional END <* spaces <* endOfInput |>.run s |>.run' (PE, "") with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule' (s : String) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  let liftEIO act := IO.toEIO IO.Error.toString act
  match runST fun _ => module <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def lpOrMod : TParser σ TopDecl := withErrorMessage "Decl" $
  first' #[declaration, patBind <$> letPatDecl] simpErrorCombine

def lpOrModOrMut : TParser σ $ Array TopDecl := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> lpOrMod

def toplevel : TParser σ $ Array TopDecl := withErrorMessage "Toplevel" $
  let hd := lpOrModOrMut <* optional END
  (foldl (· ++ ·) · hd) =<< hd

def parseModuleIR (s : String) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  let liftEIO act := IO.toEIO IO.Error.toString act
  match runST fun _ => toplevel <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)
end Parsing

namespace MLType

def check1 (s : String) (E : Env := defaultE) : String :=
  match Parsing.parse s initState with
  | .error e => toString e
  | .ok e    =>
    match runInfer1 e E with
    | .error e' => toString e' ++ s!"AST: {reprStr e}"
    | .ok    s => toString s

end MLType
