module Core.Type.Result where

import Core.Type.Syntax (ProperKind)
import Data.List.NonEmpty (NonEmpty)
import Data.Result (CtxResult)

type TypeResult e = CtxResult [ProperKind] NonEmpty e
