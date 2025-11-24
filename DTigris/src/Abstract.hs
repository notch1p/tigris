{-# OPTIONS_GHC -Wno-orphans #-}

module Abstract where

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic (from))
import Text.Parsec.Pos (SourcePos, initialPos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound

strN :: String -> Unbound.Name a
strN = Unbound.string2Name

type Symbol = Unbound.Name Term
type Type = Term
data Term
  = Type0
  | Var Symbol
  | Lam Eps (Unbound.Bind Symbol Term)
  | App Term Arg
  | Pi Eps Type (Unbound.Bind Symbol Type)
  | Ann Term Type
  | Pos SourcePos Term
  | Sorry
  | Print
  | Let Term (Unbound.Bind Symbol Term)
  | VU | TU
  | VB Bool | TB
  | Cond Term Term Term
  | Sigma Term (Unbound.Bind Symbol Term)
  | Prod Term Term
  | Id Term Term
  | Rfl
  | Rw Term Term
  | Contra Term
  | TyCon String [Arg]
  | Ctor String [Arg]
  | Case [Term] [[MatchAlt]]
  deriving (Show, Generic)

data Arg = Arg {argEp :: Eps, unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

data Eps = Rel | Irr deriving (Eq, Show, Read, Bounded, Enum, Ord, Generic, Unbound.Alpha, Unbound.Subst Term)

newtype MatchAlt = Br (Unbound.Bind Pattern Term)
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

data Pattern = PCtor String [(Pattern, Eps)] | PVar Symbol
  deriving (Show, Eq, Generic, Unbound.Alpha, Unbound.Subst Term)

data Module = Module
  { moduleName :: String
  , moduleImports :: [ModuleImport]
  , moduleEntries :: [Entry]
  , moduleConstructors :: CtorNames
  }
  deriving (Show, Generic, Unbound.Alpha)

newtype ModuleImport = ModuleImport String
  deriving (Show, Eq, Generic)
  deriving anyclass (Unbound.Alpha)

data TypeDecl = TypeDecl
  {declName :: Symbol, declEp :: Eps, declType :: Type}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

mkDecl :: Symbol -> Type -> Entry
mkDecl n ty = Decl $ TypeDecl n Rel ty
mkDecl' :: String -> Type -> Entry
mkDecl' = mkDecl . strN

data Entry
  = Decl TypeDecl
  | Def Symbol Term
  | Demote Eps
  | Data String Ambient [CtorDef]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

data CtorNames = CtorNames {tconNames :: Set String, dconNames :: Set String}
  deriving (Show, Eq, Ord, Generic)

data CtorDef = CtorDef SourcePos String Ambient
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

newtype Ambient = Ambient [Entry]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

isNum :: Term -> Maybe Int
isNum (Pos _ t) = isNum t
isNum (Ctor c []) | c == "Zero" = Just 0
isNum (Ctor c [Arg _ t])
  | c == "Succ" =
      (+ 1) <$> isNum t
isNum _ = Nothing

isPatVar :: Pattern -> Bool
isPatVar (PVar _) = True
isPatVar _ = False

mkCtorNames :: [String] -> [String] -> CtorNames
mkCtorNames = CtorNames `on` Set.fromList
initCtorNames :: CtorNames
initCtorNames =
  mkCtorNames
    ["Sigma", "Prod", "Bool", "Unit"]
    ["True", "False", "()"]

alpha :: Unbound.Name a
beta :: Unbound.Name a
dumX :: Unbound.Name a
dumY :: Unbound.Name a
(alpha, beta, dumX, dumY) = (strN "α", strN "β", strN "x", strN "y")

preludeDataDecls :: [Entry]
preludeDataDecls =
  [ Data "Sigma" sAmb [pd]
  , Data "Unit" (Ambient []) [ud]
  , Data "Bool" (Ambient []) [b₁, b₂]
  ]
 where
  internalPos = initialPos "prelude"
  b₁ = CtorDef internalPos "true" (Ambient [])
  b₂ = CtorDef internalPos "false" (Ambient [])
  ud = CtorDef internalPos "()" (Ambient [])
  sAmb = Ambient [t₁, t₂]
  pd = CtorDef internalPos "Prod" (Ambient [x, y])
  (t₁, t₂) = (mkDecl alpha Type0, mkDecl beta $ Pi Rel (Var alpha) $ Unbound.bind dumX Type0)
  (x, y) = (mkDecl dumX (Var alpha), mkDecl dumY (App (Var beta) (Arg Rel (Var dumX))))

strip :: Term -> Term
strip (Pos _ tm) = strip tm
strip (Ann tm _) = strip tm
strip tm = tm
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing
getPos :: Term -> SourcePos
getPos t = fromMaybe (newPos "unknown pos" 0 0) (unPos t)

aeq :: Term -> Term -> Bool
aeq = Unbound.aeq

fv :: Term -> [Unbound.Name Term]
fv = Unbound.toListOf Unbound.fv
subst :: Symbol -> Term -> Term -> Term
subst = Unbound.subst
instantiate :: Unbound.Bind Symbol Term -> Term -> Term
instantiate bnd a = Unbound.instantiate bnd [a]
unbind :: (Unbound.Fresh m) => Unbound.Bind Symbol Term -> m (Symbol, Term)
unbind = Unbound.unbind
unbind2 :: (Unbound.Fresh m) => Unbound.Bind Symbol Term -> Unbound.Bind Symbol Term -> m (Symbol, Term, Term)
unbind2 b1 b2 = do
  o <- Unbound.unbind2 b1 b2
  case o of
    Just (x, t, _, u) -> return (x, t, u)
    Nothing -> error "impossible"

instance Unbound.Alpha Term where
  aeq' :: Unbound.AlphaCtx -> Term -> Term -> Bool
  aeq' ctx a b =
    let gaeq = Unbound.gaeq ctx `on` from
     in gaeq (strip a) (strip b)

instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing

instance Unbound.Alpha SourcePos where
  aeq' _ _ _ = True
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ

instance Unbound.Subst b SourcePos where
  subst _ _ = id
  substs _ = id
  substBvs _ _ = id

instance Unbound.Alpha CtorNames where
  aeq' _ a1 a2 = a1 == a2
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ
