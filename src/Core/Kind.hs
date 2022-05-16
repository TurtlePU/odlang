{-# LANGUAGE LambdaCase #-}

module Core.Kind where

import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty)
import Data.Position (Position, Positioned (..), getPosition)
import Data.Result (CtxResult (..), Result (..))

data SimpleKind
  = Data
  | SimpleKind :*: SimpleKind
  deriving (Show, Eq)

data ProperKind
  = Simple SimpleKind
  | Type
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
  = KMismatch ProperKind Expected Position
  | KDifferentRows (NonEmpty ProperKind) Position
  deriving (Show)

type KindingErrors = NonEmpty KindingError

type KindingResult = CtxResult [ProperKind] KindingErrors

type PosResult = CtxResult ([ProperKind], Position) KindingErrors

intoCheck :: ProperKind -> PosResult ProperKind -> PosResult ()
intoCheck k g = do
  k' <- g
  if k == k'
    then pure ()
    else failWith $ KMismatch k' $ EKind k

intoAssert :: ProperKind -> PosResult ProperKind -> PosResult ProperKind
intoAssert k g = intoCheck k g $> k

failWith f = getPosition >>= CtxR . const . Err . pure . f

pullArrow :: ProperKind -> PosResult (ProperKind, ProperKind)
pullArrow = \case
  kx :->: ky -> pure (kx, ky)
  k -> failWith (KMismatch k EOperator)

pullSimple :: ProperKind -> PosResult SimpleKind
pullSimple = \case
  Simple k -> pure k
  k -> failWith (KMismatch k ESimple)

pullPair :: ProperKind -> PosResult (ProperKind, ProperKind)
pullPair = \case
  kl :**: kr -> pure (kl, kr)
  Simple (kl :*: kr) -> pure (Simple kl, Simple kr)
  k -> failWith (KMismatch k EPair)
