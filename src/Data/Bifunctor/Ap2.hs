{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Bifunctor.Ap2 where

import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Ap (Ap (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..), Hashable2 (..))

newtype Ap2 f a b = Ap2 (f a b)
  deriving newtype (Bifunctor, Bifoldable, Eq2, Show2, Hashable2)
  deriving (Eq, Show, Hashable) via (Ap (Ap2 f a) b)

instance Bifunctor f => Functor (Ap2 f a) where
  fmap = second

instance Bifoldable f => Foldable (Ap2 f a) where
  foldMap f = bifoldMap (const mempty) f

lfoldMap :: (Bifoldable f, Monoid m) => (a -> m) -> f a b -> m
lfoldMap g = bifoldMap g (const mempty)

instance Bitraversable t => Bitraversable (Ap2 t) where
  bitraverse g h (Ap2 x) = Ap2 <$> bitraverse g h x

instance Bitraversable t => Traversable (Ap2 t a) where
  traverse = bitraverse pure

ltraverse ::
  (Applicative f, Bitraversable t) => (a -> f b) -> t a c -> f (t b c)
ltraverse g = bitraverse g pure

instance (Eq2 f, Eq a) => Eq1 (Ap2 f a) where
  liftEq = liftEq2 (==)

instance (Show2 f, Show a) => Show1 (Ap2 f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Hashable2 f, Hashable a) => Hashable1 (Ap2 f a) where
  liftHashWithSalt = liftHashWithSalt2 hashWithSalt
