{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Functor.Ap where

import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..))

newtype Ap f a = Ap (f a)
  deriving newtype (Functor, Foldable, Eq1, Show1, Hashable1)

instance Traversable f => Traversable (Ap f) where
  sequenceA (Ap t) = Ap <$> sequenceA t

instance (Eq1 f, Eq a) => Eq (Ap f a) where
  (==) = liftEq (==)

instance (Show1 f, Show a) => Show (Ap f a) where
  showsPrec = liftShowsPrec showsPrec showList

instance (Hashable1 f, Hashable a) => Hashable (Ap f a) where
  hashWithSalt = liftHashWithSalt hashWithSalt
