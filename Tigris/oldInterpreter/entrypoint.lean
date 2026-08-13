import Tigris.parsing.pexp
import Tigris.typing.oldtyping
import Tigris.typing.fexpr
import Tigris.parsing.ptype
import Tigris.typing.ttypes
import Tigris.parsing.types
import Tigris.oldInterpreter.types
namespace Parsing open Lexing Parser PType TopDecl

def declaration : TParser σ TopDecl := first'
  #[ instanceDecl
   , externDecl
   , tyBind <$> tyDecl false
   , idBind <$> letDeclDispatch
   , (idBind ∘ Array.singleton) <$> infixlDecl
   , (idBind ∘ Array.singleton) <$> infixrDecl
   , (idBind ∘ Array.singleton) <$> prefixDecl
   , (idBind ∘ Array.singleton) <$> postfixDecl
   , (idBind ∘ Array.singleton) <$> value parseExpr
   ]
--  simpErrorCombine

def tydecl : TParser σ TopDecl := first'
 #[ tyBind <$> tyDecl false
   , tyBind <$> tyEmpty]
--  simpErrorCombine

def declarationFile : TParser σ TopDecl := first'
  #[ instanceDecl
   , externDecl
   , tyBind <$> tyDecl false
   , idBind <$> letDeclDispatch
   , (idBind ∘ Array.singleton) <$> infixlDecl
   , (idBind ∘ Array.singleton) <$> infixrDecl
   , (idBind ∘ Array.singleton) <$> prefixDecl
   , (idBind ∘ Array.singleton) <$> postfixDecl
   ]
--  simpErrorCombine

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

def parse (s : String.Slice) (PE : PEnv) : Except String Expr :=
  match runST fun _ => parseExpr <* optional END <* spaces <* endOfInput |>.run s |>.run' (PE, "") with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule' (s : String.Slice) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  match runST fun _ => module <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def typeExpr (s : String.Slice) (PE : PEnv) (E : Env) : EIO String TExpr :=
  match runST fun _ => parseExpr <* optional END <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (_, l))   => do
    liftEIO (IO.print l)
    let (te, _, l) <- MLType.runInferT1 t E |>.mapError toString |> EIO.ofExcept
    liftEIO (IO.print l)
    return te
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def lpOrMod : TParser σ TopDecl := withExpected "declaration" $
  first' #[declaration, patBind <$> letPatDecl] -- simpErrorCombine

def lpOrModOrMut : TParser σ $ Array TopDecl := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> lpOrMod

def lpOrModOrMutFile : TParser σ $ Array TopDecl := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> (withExpected "declaration" $
  first' #[declarationFile, patBind <$> letPatDecl] /- simpErrorCombine -/)

def toplevel : TParser σ $ Array TopDecl := withExpected "Toplevel" $
  let hd := lpOrModOrMut <* optional END
  (foldl (· ++ ·) · hd) =<< hd

def toplevelFile : TParser σ $ Array TopDecl := withExpected "Toplevel" $
  let hd := lpOrModOrMutFile <* optional END
  (foldl (· ++ ·) · hd) =<< hd

def parseModuleIR (s : String.Slice) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  match runST fun _ => toplevelFile <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)

def parseREPL (s : String.Slice) (PE : PEnv) : EIO String (PEnv × Array TopDecl) :=
  match runST fun _ => toplevel <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ t, (pe, l))   => liftEIO (IO.print l) *> pure (pe, t)
  | (.error _ e, (_, l)) => liftEIO (IO.print l) *> throw (toString e)
end Parsing

namespace MLType

def parseToplevel (s : String.Slice) (toplevel := `File) : IO Unit :=
  let p {σ} : TParser σ (Array TopDecl) := if toplevel matches `File then Parsing.toplevelFile else Parsing.toplevel
  match runST fun _ => (p <* Lexing.spaces <* Parser.endOfInput) s |>.run (initState, "") with
  | (.error _ e, (_, l)) => do
    println! l
    println! e
  | (.ok _ t, (_, l)) => do
    println! l
    println! repr t

def testTParser : String.Slice -> IO Unit := fun s =>
  match
    runST fun _ => (Parsing.letDeclDispatch <* Lexing.spaces <* Parser.endOfInput) |>.run s |>.run (initState, "")
  with
  | (.error _ e, (_, l)) => do
    println! l
    println! e
  | (.ok _ t, (_, l)) => do
    println! l
    println! repr t

def check1 (s : String.Slice) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInfer1 e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    s => println! s

def check1C (s : String.Slice) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInferConstraintT e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    (te, s, l) => println!
      reprStr te ++ "\n" ++
      toString s ++ "\n" ++ l
def check1C' (s : String.Slice) (E : Env := defaultE) : Option TExpr := do
  let e <- Parsing.parse s initState |>.toOption
  runInferConstraintT e E |>.toOption |>.map Prod.fst

def check1F (s : String.Slice) (E : Env := defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInferConstraintF e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    (te, s, l) => println!
      reprStr te ++ "\n" ++
      toString s ++ "\n" ++ l

def checkFile (s : String.Slice) : IO Unit := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState |>.toIO .userError
  let stage0 <- inferToplevelC topdecl defaultE' |> IO.ofExcept
  let (toplevel, logger, _) <- inferToplevelF stage0 |> IO.ofExcept
  println! logger
  println! Std.Format.pretty (width := 80) $ unexpandDeclsF toplevel
end MLType

/-- info:
let z : Int = 3 and x : Int = add z 1
and w : Int = 4 and y : Int = add w 2
and main : Int = add x y
-/
#guard_msgs in
#eval MLType.checkFile $
"
let rec main = x + y
where
     x :=
  z + 1
     y :=
      w + 2
     z := 3; w := 4
"
example := x + y
where
     x :=
  z + 1
     y :=
      w + 2
     z := 3; w := 4


/-- info:
let i_C_0 : C Int = C@Int (fun x : Int => x)
let i_C_1 : C Bool = C@Bool (fun x : Bool => 5)
let i_D_0 : D Int = D@Int (fun x : Int => 100)
let i_C_2 : ∀ a [D a], C a =
  (Λ a. fun d_D_0 : D a => C@a (fun x : a => add (d_D_0[0, d]@a x) 1))
let main : Int × Int =
  let rd_D_0 : D Int = i_D_0
  and rd_C_1 : C Int = (Λ α. i_C_2@Int rd_D_0)
  and rd_C_2 : C Bool = i_C_1
  in (rd_C_1[0, c]@Int 1 , rd_C_2[0, c]@Bool true)
-/
#guard_msgs (whitespace := lax) in
#eval MLType.checkFile $
"
class C a where c : a -> Int
instance C Int where c x = x
instance C Bool where c x = 5
class D a where d : a -> Int
instance D Int where d x = 100
instance forall a [D a], C a where c x = d x + 1
let main = (c 1, c true)
"


#eval MLType.checkFile $
"
class Eq a = {eq : a -> a -> Bool}
class HEq a b = {heq : a -> b -> Bool}
class HAdd a b c = {hadd : a -> b -> c}
instance Eq Int = {eq x y = __eqInt x y}
instance ∀a [Eq a], HEq a a = {heq = eq}
instance HAdd Int Int Int = {hadd = (_ + _)}
let f' = heq (hadd 2 3) 5
"
