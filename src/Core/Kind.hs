module Core.Kind where

import Data.List.NonEmpty (NonEmpty)
import Position (Position, Positioned (..))
import Result (CtxResult (..), Result (..))

data SimpleKind
  = Pretype
  | Type
  | SimpleKind :*: SimpleKind
  deriving (Show, Eq)

data ProperKind
  = Simple SimpleKind
  | Mult
  | Row ProperKind
  | ProperKind :**: ProperKind
  | ProperKind :->: ProperKind
  deriving (Show, Eq)

data Expected
  = EKind ProperKind
  | EOperator
  | EPair
  | ERow
  | ESimple
  deriving (Show)

data KindingError
  = KMismatch Position ProperKind Expected
  | KDifferentRows Position (NonEmpty ProperKind)
  deriving (Show)

type KindingErrors = NonEmpty KindingError

type KindingResult = CtxResult [ProperKind] KindingErrors

intoCheck :: ProperKind -> (Positioned f -> KindingResult ProperKind) -> Positioned f -> KindingResult ()
intoCheck k g t = do
  k' <- g t
  if k == k'
    then pure ()
    else failWith $ KMismatch (pos t) k' $ EKind k

failWith = CtxR . const . Err . pure
