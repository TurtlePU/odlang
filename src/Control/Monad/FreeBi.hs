{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Control.Monad.FreeBi where

import Control.Monad.Free (Free (..), hoistFree)
import qualified Control.Monad.Free as Free
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Ap2 (Ap2 (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Classes (Eq1, Eq2 (..), Show1 (..), Show2 (..))
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1 (..), Hashable2 (..))
import Data.Reflection (reify)
import Data.Reflection.Instances

newtype FreeBi f a b = FreeBi {runFreeBi :: Free (Ap2 f a) b}
  deriving newtype (Applicative, Monad)
  deriving (Functor, Foldable, Eq1, Show1, Hashable1) via (Ap2 (FreeBi f) a)
  deriving (Eq, Show, Hashable) via (Ap2 (FreeBi f) a b)

iter :: Bifunctor f => (f a b -> b) -> FreeBi f a b -> b
iter g = Free.iter (\(Ap2 x) -> g x) . runFreeBi

iterA ::
  (Applicative p, Bifunctor f) => (f a (p b) -> p b) -> FreeBi f a b -> p b
iterA g = Free.iterA (\(Ap2 x) -> g x) . runFreeBi

instance (Functor f, Hashable1 f) => Hashable1 (Free f)

instance (Bifunctor f, Hashable2 f) => Hashable2 (FreeBi f) where
  liftHashWithSalt2 ha hb s (FreeBi x) = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt hb s $ hoistFree (first $ mkReflected p) x

instance Bifunctor f => Bifunctor (FreeBi f) where
  bimap f g = FreeBi . fmap g . hoistFree (first f) . runFreeBi

instance (Bifunctor f, Bifoldable f) => Bifoldable (FreeBi f) where
  bifoldMap g h = iter (bifoldMap g id) . fmap h

instance Bitraversable f => Bitraversable (FreeBi f) where
  bitraverse g h = fmap FreeBi . impl . runFreeBi
    where
      impl = \case
        Pure x -> Pure <$> h x
        Free w -> Free <$> bitraverse g impl w

instance Bitraversable f => Traversable (FreeBi f a) where
  traverse = bitraverse pure

instance Eq2 f => Eq2 (FreeBi f) where
  liftEq2 v w (FreeBi l) (FreeBi r) = impl l r
    where
      impl l r = case (l, r) of
        (Pure x, Pure y) -> w x y
        (Free l, Free r) -> liftEq2 v impl l r
        _ -> False

instance (Bifunctor f, Show2 f) => Show2 (FreeBi f) where
  liftShowsPrec2 ia la ib lb i (FreeBi x) = reify (ReifiedShow ia) $ \p ->
    liftShowsPrec ib lb i $ hoistFree (first $ mkReflected p) x
