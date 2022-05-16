{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.TypeLevel where

import Control.Applicative (Applicative (liftA2))
import Control.Monad (forM_, (>=>))
import Control.Monad.Free (Free (Free))
import Core.Data
import Core.Kind
import Core.Multiplicity
import Core.Row
import Data.Bifunctor (Bifunctor (first, second))
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..), nub)
import Data.Position
import Data.Result

data TLLambda t
  = LVar Int
  | LApp t t
  | LAbs ProperKind t
  | LSPair t t
  | LPair t t
  | LFst t
  | LSnd t
  | LPre t
  | LMul t
  | LFix SimpleKind t
  | LMap t t
  deriving (Show, Functor)

data TLTerm t
  = KLam (TLLambda t)
  | KMult (MultTerm t)
  | KRow (RowTerm' t)
  | KType (TypeTerm' t)
  | KData (DataTerm' t)
  deriving (Functor)

shiftTLTerm :: Positioned TLTerm -> Int -> Positioned TLTerm
shiftTLTerm = _

substTLTerm ::
  Positioned TLTerm -> Int -> Positioned TLTerm -> Positioned TLTerm
substTLTerm = _

synthesizeKind :: Positioned TLTerm -> KindingResult ProperKind
synthesizeKind = withPosition (foldPositioned synthesizeKind')

synthesizeKind' :: TLTerm (PosResult ProperKind) -> PosResult ProperKind
synthesizeKind' = \case
  KLam (LVar i) -> CtxR $ Ok . (!! i) . fst
  KLam (LApp f x) -> f >>= pullArrow >>= \(kx, ky) -> intoCheck kx x $> ky
  KLam (LAbs k t) -> (k :->:) <$> mapCtx (first (k :)) t
  KLam (LSPair l r) ->
    liftA2 ((Simple .) . (:*:)) (l >>= pullSimple) (r >>= pullSimple)
  KLam (LPair l r) -> liftA2 (:**:) l r
  KLam (LFst t) -> fmap fst $ t >>= pullPair
  KLam (LSnd t) -> fmap snd $ t >>= pullPair
  KLam (LPre t) -> intoCheck Type t $> Simple Data
  KLam (LMul t) -> intoCheck Type t $> Mult
  KLam (LFix k t) ->
    mapCtx (first (Simple k :)) (intoCheck (Simple k) t) $> Simple k
  KLam (LMap f r) ->
    f >>= pullArrow >>= \(kx, ky) -> intoCheck (Row kx) r $> Row ky
  KMult m -> checkMultKind m
  KRow r -> synthesizeRowKind r
  KType t -> checkTypeKind t
  KData p -> checkDataKind p

type Mult = Positioned TLTerm

type Type = Positioned TLTerm

checkSup :: Foldable f => Mult -> f Type -> KindingResult ()
checkSup = error "TODO"

upperBound :: Int -> MultLit
upperBound = liftA2 MultLit (>= 1) (<= 1)

upperBound' :: Position -> Int -> Positioned TLTerm
upperBound' p = Posed p . KMult . Free . MLit . upperBound
