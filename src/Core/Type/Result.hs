module Core.Type.Result where

import Control.Monad.Result (CtxResult)
import Core.Type.Syntax (ProperKind)
import Data.List.NonEmpty (NonEmpty)

type TypeResult e = CtxResult [ProperKind] NonEmpty e
