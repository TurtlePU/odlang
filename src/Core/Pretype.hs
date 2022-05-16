{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Pretype where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.Free (hoistFree)
import Core.Kind
import Core.Multiplicity
import Core.Row
import Data.Bifree
import Data.Bifunctor (Bifunctor (..))
import Data.Functor (($>))
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Position (Position)
import Data.Result (Result (..), mapCtx)

data Connective = CAnd | CWith | COr deriving (Show, Eq)

data TypeT n a = TLit
  { tyPos :: Position,
    tyPre :: a,
    tyMul :: MultTerm n
  }
  deriving (Functor)

data PreTypeT n a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective (RowTerm a n)

instance Bifunctor TypeT where
  bimap f g (TLit q p m) = TLit q (g p) (fmap f m)

instance Bifunctor PreTypeT where
  bimap f g = \case
    PArrow d c -> PArrow (g d) (g c)
    PForall k t -> PForall k (g t)
    PSpread c r -> PSpread c (bimapRow g f r)

instance Functor (PreTypeT n) where
  fmap = second

data PreTypeOption
  = OArrow
  | OForall ProperKind
  | OSpread Connective

getOption :: PreTypeT n a -> PreTypeOption
getOption = \case
  PArrow _ _ -> OArrow
  PForall k _ -> OForall k
  PSpread c _ -> OSpread c

type TypeTerm n a = Bifree (PreTypeT n) (TypeT n) a a

type PreType n a = Bifree (TypeT n) (PreTypeT n) a a

bifirst ::
  (Bifunctor f, Bifunctor g, Functor (f b), Functor (g b)) =>
  (a -> b) ->
  Bifree (f a) (g a) c d ->
  Bifree (f b) (g b) c d
bifirst f = bihoist (first f) (first f)

newtype TypeTerm' a = TTerm {unTT :: TypeTerm a a}

newtype PreType' a = PTerm {unPT :: PreType a a}

instance Functor TypeTerm' where
  fmap f = TTerm . bifirst f . bimap f f . unTT

instance Functor PreType' where
  fmap f = PTerm . bifirst f . bimap f f . unPT

checkTypeKind' ::
  TypeT (PosResult ProperKind) (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind' (TLit _ p m) =
  Type <$ intoCheck (Simple Pretype) p <* checkMultKind m

checkPreTypeKind' ::
  PreTypeT (PosResult ProperKind) (PosResult ProperKind) -> PosResult ProperKind
checkPreTypeKind' =
  fmap (const $ Simple Pretype) . \case
    PArrow f t -> intoCheck Type f *> intoCheck Type t
    PForall k t -> intoCheck Type $ mapCtx (first (k :)) t
    PSpread c r ->
      intoCheck (Row Type) $
        synthesizeRowKind $
          MkRowTerm' $
            hoistFree (first $ intoAssert Type) r

checkTypeKind :: TypeTerm' (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind = biiter checkTypeKind' checkPreTypeKind' . unTT

checkPreTypeKind :: PreType' (PosResult ProperKind) -> PosResult ProperKind
checkPreTypeKind = biiter checkPreTypeKind' checkTypeKind' . unPT

type TyEqResult n a = Result (NonEmpty (TyEqError n)) [TyEqAssumption n a]

checkTypeEQ :: (Eq n, Eq a) => TypeTerm n a -> TypeTerm n a -> TyEqResult n a
checkTypeEQ l r = case (l, r) of
  (BFree (TLit ql pl ml), BFree (TLit qr pr mr)) ->
    liftA2 (<>) (checkPreTypeEQ pl pr) (fromMult $ checkMultEQ ml ml)
  (l, r) -> Ok [Left (l, r)]
  where
    fromMult = \case
      Just errs -> Err $ pure $ EMult errs
      Nothing -> Ok []

checkPreTypeEQ :: (Eq n, Eq a) => PreType n a -> PreType n a -> TyEqResult n a
checkPreTypeEQ l r = case (l, r) of
  (BFree (PArrow f t), BFree (PArrow f' t')) ->
    liftA2 (<>) (checkTypeEQ f f') (checkTypeEQ t t')
  (BFree (PForall k t), BFree (PForall k' t')) ->
    if k == k'
      then checkTypeEQ t t'
      else Err $ pure $ EPre (OForall k, OForall k')
  (BFree (PSpread c r), BFree (PSpread c' r')) ->
    if c == c'
      then fromRow $ checkRowEQ r r'
      else Err $ pure $ EPre (OSpread c, OSpread c')
  (BFree t, BFree t') -> Err $ pure $ EPre (getOption t, getOption t')
  (t, t') -> Ok [Right (t, t')]
  where
    fromRow = \case
      [] -> Ok []
      (x : xs) -> Err $ pure $ ESpread (x :| xs)

data TyEqError n
  = EPre (Assumption PreTypeOption)
  | ESpread (NonEmpty RowEqError)
  | EMult (IndexedBag n MultLit)

type TyEqAssumption n a =
  Either (Assumption (TypeTerm n a)) (Assumption (PreType n a))

type Assumption a = (a, a)
