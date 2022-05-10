{-# LANGUAGE LambdaCase #-}

module Core.Pretype where

import Control.Applicative (Applicative (liftA2))
import Core.Kind
import Core.Multiplicity
import Core.Row
import Data.Bifunctor (Bifunctor (..))
import Data.Functor (($>))
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Position (Position)
import Data.Result (Result (..), mapCtx)

data Connective = CAnd | CWith | COr deriving (Show, Eq)

data TypeTerm n a
  = TVar a
  | TLit Position (PreType n a) (MultTerm n)

data PreType n a
  = PVar a
  | PArrow Position (TypeTerm n a) (TypeTerm n a)
  | PForall Position ProperKind (TypeTerm n a)
  | PSpread Position Connective (RowTerm a n)

instance Bifunctor TypeTerm where
  bimap f g = \case
    TVar x -> TVar (g x)
    TLit q p m -> TLit q (bimap f g p) (f <$> m)

instance Bifunctor PreType where
  bimap f g = \case
    PVar x -> PVar (g x)
    PArrow p d c -> PArrow p (bimap f g d) (bimap f g c)
    PForall p k t -> PForall p k (bimap f g t)
    PSpread p c r -> PSpread p c (bimap g f r)

newtype TypeTerm' a = TTerm {unTT :: TypeTerm a a}

newtype PreType' a = PTerm {unPT :: PreType a a}

instance Functor TypeTerm' where
  fmap f = TTerm . bimap f f . unTT

instance Functor PreType' where
  fmap f = PTerm . bimap f f . unPT

checkTypeKind :: TypeTerm' (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind (TTerm t) =
  Simple Type <$ case t of
    TVar t -> intoCheck (Simple Type) t
    TLit _ p m -> checkPreTypeKind (PTerm p) *> checkMultKind m $> ()

checkPreTypeKind :: PreType' (PosResult ProperKind) -> PosResult ProperKind
checkPreTypeKind (PTerm t) =
  Simple Pretype <$ case t of
    PVar p -> intoCheck (Simple Pretype) p
    PArrow _ f t -> checkTypeKind (TTerm f) *> checkTypeKind (TTerm t) $> ()
    PForall _ k t -> mapCtx (first (k :)) (checkTypeKind $ TTerm t) $> ()
    PSpread _ c r ->
      intoCheck (Row $ Simple Type) $
        synthesizeRowKind $ MkRowTerm' $ first (intoAssert $ Simple Type) r

type TyEqResult n a = Result (NonEmpty (TyEqError n)) [TyEqAssumption n a]

checkTypeEQ :: (Eq n, Eq a) => TypeTerm n a -> TypeTerm n a -> TyEqResult n a
checkTypeEQ l r = case (l, r) of
  (TLit ql pl ml, TLit qr pr mr) ->
    mappend
      <$> checkPreTypeEQ pl pr
      <*> maybe (Ok []) (Err . pure . EMult (ql, qr)) (checkMultEQ ml mr)
  (l, r) -> Ok $ pure $ Left (l, r)

checkPreTypeEQ :: (Eq n, Eq a) => PreType n a -> PreType n a -> TyEqResult n a
checkPreTypeEQ l r = case (l, r) of
  (PArrow _ lc ld, PArrow _ rc rd) ->
    mappend
      <$> checkTypeEQ lc rc
      <*> checkTypeEQ ld ld
  (PForall lp lk lt, PForall rp rk rt) ->
    if lk == rk
      then checkTypeEQ lt rt
      else Err $ pure $ EPre (OForall lp lk, OForall rp rk)
  (PSpread lp lc lr, PSpread rp rc rr) ->
    if lc == rc
      then case checkRowEQ lr rr of
        [] -> Ok []
        e : es -> Err $ pure $ ESpread (lp, rp) (e :| es)
      else Err $ pure $ EPre (OSpread lp lc, OSpread rp rc)
  (l, r) -> case liftA2 (,) (getOption l) (getOption r) of
    Nothing -> Ok $ pure $ Right (l, r)
    Just (al, ar) -> Err $ pure $ EPre (al, ar)

data TyEqError n
  = EPre (Assumption PreTypeOption)
  | ESpread Positions (NonEmpty RowEqError)
  | EMult Positions (IndexedBag n MultLit)

type TyEqAssumption n a =
  Either (Assumption (TypeTerm n a)) (Assumption (PreType n a))

type Positions = (Position, Position)

type Assumption a = (a, a)

data PreTypeOption
  = OArrow Position
  | OForall Position ProperKind
  | OSpread Position Connective

getOption :: PreType a b -> Maybe PreTypeOption
getOption = \case
  PVar _ -> Nothing
  PArrow p _ _ -> Just (OArrow p)
  PForall p k _ -> Just (OForall p k)
  PSpread p c _ -> Just (OSpread p c)
