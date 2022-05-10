{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Pretype where

import Core.Kind
import Core.Multiplicity (MultTerm, checkMultKind)
import Core.Row (RowTerm, RowTerm' (MkRowTerm'), synthesizeRowKind)
import Data.Bifunctor (Bifunctor (..))
import Data.Functor (($>))
import Data.Result (mapCtx)

data Connective = CAnd | CWith | COr deriving (Show)

data TypeTerm a
  = TVar a
  | TLit (PreType a) (MultTerm a)
  deriving (Functor)

checkTypeKind :: TypeTerm (PosResult ProperKind) -> PosResult ProperKind
checkTypeKind =
  fmap (const $ Simple Type) . \case
    TVar t -> intoCheck (Simple Type) t
    TLit p m -> checkPreTypeKind p *> checkMultKind m $> ()

data PreType a
  = PVar a
  | PArrow (TypeTerm a) (TypeTerm a)
  | PForall ProperKind (TypeTerm a)
  | PSpread Connective (RowTerm (TypeTerm a) a)

instance Functor PreType where
  fmap f = \case
    PVar p -> PVar (f p)
    PArrow t t' -> PArrow (fmap f t) (fmap f t')
    PForall k t -> PForall k (fmap f t)
    PSpread c r -> PSpread c (bimap (fmap f) f r)

checkPreTypeKind :: PreType (PosResult ProperKind) -> PosResult ProperKind
checkPreTypeKind =
  fmap (const $ Simple Pretype) . \case
    PVar p -> intoCheck (Simple Pretype) p
    PArrow f t -> checkTypeKind f *> checkTypeKind t $> ()
    PForall k t -> mapCtx (first (k :)) (checkTypeKind t) $> ()
    PSpread c r ->
      intoCheck (Row $ Simple Type) $
        synthesizeRowKind $ MkRowTerm' $ first checkTypeKind r
