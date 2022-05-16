{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Data where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.Bifree
import Control.Monad.Free (hoistFree)
import Core.Kind
import Core.Multiplicity
import Core.Row
import Data.Bifunctor (Bifunctor (..))
import Data.Functor (($>))
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Position (Position)
import Data.Result (Result (..), mapCtx)
import Data.Aps (Ap(Ap))

data Connective = CAnd | CWith | COr deriving (Show, Eq)

data TypeT n a = TLit
  { tyPos :: Position,
    tyPre :: a,
    tyMul :: MultTerm n
  }
  deriving (Functor)

data DataT n a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective (RowTerm a n)

instance Bifunctor TypeT where
  bimap f g (TLit q p m) = TLit q (g p) (fmap f m)

instance Bifunctor DataT where
  bimap f g = \case
    PArrow d c -> PArrow (g d) (g c)
    PForall k t -> PForall k (g t)
    PSpread c r -> PSpread c (bimapRow g f r)

instance Functor (DataT n) where
  fmap = second

data DataVariety
  = VArrow
  | VForall ProperKind
  | VSpread Connective

getOption :: DataT n a -> DataVariety
getOption = \case
  PArrow _ _ -> VArrow
  PForall k _ -> VForall k
  PSpread c _ -> VSpread c

type TypeTerm n a = Bifree (DataT n) (TypeT n) a a

type DataTerm n a = Bifree (TypeT n) (DataT n) a a

newtype TypeTerm' a = TTerm {unTT :: TypeTerm a a}

newtype DataTerm' a = DTerm {unDT :: DataTerm a a}

instance Functor TypeTerm' where
  fmap f = TTerm . bifirst f . bimap f f . unTT

instance Functor DataTerm' where
  fmap f = DTerm . bifirst f . bimap f f . unDT

checkTypeKind' ::
  TypeT (PosResult ProperKind) (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind' (TLit _ p m) =
  Type <$ intoCheck (Simple Data) p <* checkMultKind m

checkDataKind' ::
  DataT (PosResult ProperKind) (PosResult ProperKind) -> PosResult ProperKind
checkDataKind' =
  fmap (const $ Simple Data) . \case
    PArrow f t -> intoCheck Type f *> intoCheck Type t
    PForall k t -> intoCheck Type $ mapCtx (first (k :)) t
    PSpread c r ->
      intoCheck (Row Type) $
        synthesizeRowKind $
          MkRowTerm' $
            hoistFree (first $ intoAssert Type) r

checkTypeKind :: TypeTerm' (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind = biiter checkTypeKind' checkDataKind' . unTT

checkDataKind :: DataTerm' (PosResult ProperKind) -> PosResult ProperKind
checkDataKind = biiter checkDataKind' checkTypeKind' . unDT

type TyEqResult n a = Result (NonEmpty (TyEqError n)) [TyEqAssumption n a]

checkTypeEQ :: (Eq n, Eq a) => TypeTerm n a -> TypeTerm n a -> TyEqResult n a
checkTypeEQ l r = case (l, r) of
  (BFree (Ap (TLit ql pl ml)), BFree (Ap (TLit qr pr mr))) ->
    liftA2 (<>) (checkDataEQ pl pr) (fromMult $ checkMultEQ ml ml)
  (l, r) -> Ok [Left (l, r)]
  where
    fromMult = \case
      Just errs -> Err $ pure $ EMult errs
      Nothing -> Ok []

checkDataEQ :: (Eq n, Eq a) => DataTerm n a -> DataTerm n a -> TyEqResult n a
checkDataEQ l r = case (l, r) of
  (BFree (Ap (PArrow f t)), BFree (Ap (PArrow f' t'))) ->
    liftA2 (<>) (checkTypeEQ f f') (checkTypeEQ t t')
  (BFree (Ap (PForall k t)), BFree (Ap (PForall k' t'))) ->
    if k == k'
      then checkTypeEQ t t'
      else Err $ pure $ EData (VForall k, VForall k')
  (BFree (Ap (PSpread c r)), BFree (Ap (PSpread c' r'))) ->
    if c == c'
      then fromRow $ checkRowEQ r r'
      else Err $ pure $ EData (VSpread c, VSpread c')
  (BFree (Ap t), BFree (Ap t')) -> Err $ pure $ EData (getOption t, getOption t')
  (t, t') -> Ok [Right (t, t')]
  where
    fromRow = \case
      [] -> Ok []
      (x : xs) -> Err $ pure $ ESpread (x :| xs)

data TyEqError n
  = EData (Assumption DataVariety)
  | ESpread (NonEmpty RowEqError)
  | EMult (IndexedBag n MultLit)

type TyEqAssumption n a =
  Either (Assumption (TypeTerm n a)) (Assumption (DataTerm n a))

type Assumption a = (a, a)
