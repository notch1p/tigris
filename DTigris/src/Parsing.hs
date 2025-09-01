module Parsing 
where

import Abstract
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State.Lazy hiding (join)
import Text.Parsec hiding (Empty, State)
import Text.Parsec.Expr (Assoc (..), Operator (..), buildExpressionParser)
import Unbound.Generics.LocallyNameless qualified as Unbound
