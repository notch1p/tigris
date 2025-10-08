import Tigris.parsing.pexp
import Tigris.typing.typing
import Tigris.typing.fexpr
import Tigris.parsing.ptype
import Tigris.typing.ttypes
import Tigris.parsing.types
import Tigris.interpreter.types
namespace Parsing open Lexing Parser PType TopDecl
-- abbrev TopDecl := Binding ⊕ TyDecl
def declaration : TParser σ TopDecl := first'
  #[ instanceDecl
   , externDecl
   , tyBind <$> tyDecl false
   , idBind <$> letDeclDispatch
   , (idBind ∘ Array.singleton) <$> infixlDecl
   , (idBind ∘ Array.singleton) <$> infixrDecl
   , (idBind ∘ Array.singleton) <$> value parseExpr
   ]
  simpErrorCombine

def tydecl : TParser σ TopDecl := first'
 #[ tyBind <$> tyDecl false
   , tyBind <$> tyEmpty]
  simpErrorCombine

def declarationFile : TParser σ TopDecl := first'
  #[ instanceDecl
   , externDecl
   , tyBind <$> tyDecl false
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

def moduleFile : TParser σ $ Array TopDecl :=
  sepBy (optional END) declarationFile <* optional END

def parse (s : String) (PE : PEnv) : Except String Expr :=
  match runST fun _ => parseExpr <* optional END <* spaces <* endOfInput |>.run s |>.run' (PE, "") with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule' (s : String) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  match runST fun _ => module <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def typeExpr (s : String) (PE : PEnv) (E : Env) : EIO String TExpr :=
  match runST fun _ => parseExpr <* optional END <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (_, l))   => do
    liftEIO (IO.print l)
    let (te, _, l) <- MLType.runInferT1 t E |>.mapError toString |> EIO.ofExcept
    liftEIO (IO.print l)
    return te
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def lpOrMod : TParser σ TopDecl := withErrorMessage "Decl" $
  first' #[declaration, patBind <$> letPatDecl] simpErrorCombine

def lpOrModOrMut : TParser σ $ Array TopDecl := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> lpOrMod

def lpOrModOrMutFile : TParser σ $ Array TopDecl := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> (withErrorMessage "Decl" $
  first' #[declarationFile, patBind <$> letPatDecl] simpErrorCombine)

def toplevel : TParser σ $ Array TopDecl := withErrorMessage "Toplevel" $
  let hd := lpOrModOrMut <* optional END
  (foldl (· ++ ·) · hd) =<< hd

def toplevelFile : TParser σ $ Array TopDecl := withErrorMessage "Toplevel" $
  let hd := lpOrModOrMutFile <* optional END
  (foldl (· ++ ·) · hd) =<< hd

def parseModuleIR (s : String) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  match runST fun _ => toplevelFile <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)
end Parsing

namespace MLType

def check1 (s : String) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInfer1 e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    s => println! s

def check1C (s : String) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInferConstraintT e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    (te, s, l) => println!
      reprStr te ++ "\n" ++
      toString s ++ "\n" ++ l
def check1C' (s : String) (E : Env := defaultE) : Option TExpr := do
  let e <- Parsing.parse s initState |>.toOption
  runInferConstraintT e E |>.toOption |>.map Prod.fst

def check1F (s : String) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInferConstraintF e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    (te, s, l) => println!
      reprStr te ++ "\n" ++
      toString s ++ "\n" ++ l

def checkFile (s : String) : IO Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState |>.toIO .userError
  let stage0 <- inferToplevelC topdecl defaultE' |> IO.ofExcept
  let (toplevel, logger) <- inferToplevelF stage0 |> IO.ofExcept
  println! logger
  println! unexpandDeclsF toplevel

end MLType

