module Data.Ap2 where

import Data.Bifunctor (Bifunctor (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))

newtype Ap2 f a b = Ap2 (f a b)

instance Bifunctor f => Bifunctor (Ap2 f) where
  bimap f g (Ap2 x) = Ap2 (bimap f g x)

instance Bifunctor f => Functor (Ap2 f a) where
  fmap = second

instance Eq2 f => Eq2 (Ap2 f) where
  liftEq2 f g (Ap2 x) (Ap2 y) = liftEq2 f g x y

instance (Eq2 f, Eq a) => Eq1 (Ap2 f a) where
  liftEq = liftEq2 (==)

instance (Eq2 f, Eq a, Eq b) => Eq (Ap2 f a b) where
  (==) = liftEq (==)

instance Show2 f => Show2 (Ap2 f) where
  liftShowsPrec2 ia la ib lb i (Ap2 x) = liftShowsPrec2 ia la ib lb i x

instance (Show2 f, Show a) => Show1 (Ap2 f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show2 f, Show a, Show b) => Show (Ap2 f a b) where
  showsPrec = liftShowsPrec showsPrec showList
