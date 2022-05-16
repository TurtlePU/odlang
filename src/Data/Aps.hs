{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Aps where

import Data.Bifunctor (Bifunctor (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))

newtype Ap f a = Ap (f a)
  deriving newtype (Functor, Eq1, Show1)

instance (Eq1 f, Eq a) => Eq (Ap f a) where
  (==) = liftEq (==)

instance (Show1 f, Show a) => Show (Ap f a) where
  showsPrec = liftShowsPrec showsPrec showList

newtype Ap2 f a b = Ap2 (f a b)
  deriving newtype (Bifunctor, Eq2, Show2)
  deriving (Eq, Show) via (Ap (Ap2 f a) b)

instance Bifunctor f => Functor (Ap2 f a) where
  fmap = second

instance (Eq2 f, Eq a) => Eq1 (Ap2 f a) where
  liftEq = liftEq2 (==)

instance (Show2 f, Show a) => Show1 (Ap2 f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList
