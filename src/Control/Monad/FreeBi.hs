{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Monad.FreeBi where

import Control.Composition ((.@@), (.@@@))
import Control.Monad.Free (Free (..))
import qualified Control.Monad.Free as Free
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..), Hashable2 (..))
import Data.Reflection (reify)
import Data.Reflection.Instances

------------------------------ BIFUNCTOR HELPER --------------------------------

newtype Ap2 f a b = Ap2 {unAp :: f a b}
  deriving newtype (Bifunctor, Bifoldable, Hashable2, Eq2, Show2)

instance Bifunctor f => Functor (Ap2 f a) where
  fmap = second

instance Bifoldable f => Foldable (Ap2 f a) where
  foldMap = bifoldMap (const mempty)

instance Bitraversable f => Bitraversable (Ap2 f) where
  bitraverse f g = fmap Ap2 . bitraverse f g . unAp

instance Bitraversable f => Traversable (Ap2 f a) where
  traverse = bitraverse pure

instance (Hashable2 f, Hashable a) => Hashable1 (Ap2 f a) where
  liftHashWithSalt = liftHashWithSalt2 hashWithSalt

instance (Hashable2 f, Hashable a, Hashable b) => Hashable (Ap2 f a b) where
  hashWithSalt = liftHashWithSalt hashWithSalt

instance (Eq2 f, Eq a) => Eq1 (Ap2 f a) where
  liftEq = liftEq2 (==)

instance (Eq2 f, Eq a, Eq b) => Eq (Ap2 f a b) where
  (==) = liftEq (==)

instance (Show2 f, Show a) => Show1 (Ap2 f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show2 f, Show a, Show b) => Show (Ap2 f a b) where
  showsPrec = liftShowsPrec showsPrec showList

----------------------------- FREE OVER BIFUNCTOR ------------------------------

newtype FreeBi f a b = FreeBi {runFreeBi :: Free (Ap2 f a) b}
  deriving (Functor, Foldable, Traversable)
  deriving newtype (Applicative, Monad, Eq1, Show1, Hashable1)
  deriving (Eq, Show, Hashable) via (Ap2 (FreeBi f) a b)

bPure :: b -> FreeBi f a b
bPure = FreeBi . Pure

bFree :: Bifunctor f => f a (FreeBi f a b) -> FreeBi f a b
bFree = FreeBi . Free . fmap runFreeBi . Ap2

iter :: Bifunctor f => (f a b -> b) -> FreeBi f a b -> b
iter g = Free.iter (g . unAp) . runFreeBi

iterA ::
  (Applicative p, Bifunctor f) => (f a (p b) -> p b) -> FreeBi f a b -> p b
iterA g = Free.iterA (g . unAp) . runFreeBi

instance Bifunctor f => Bifunctor (FreeBi f) where
  bimap f g = iter (bFree . first f) . fmap (bPure . g)

instance (Bifunctor f, Bifoldable f) => Bifoldable (FreeBi f) where
  bifoldMap g h = iter (bifoldMap g id) . fmap h

instance Bitraversable f => Bitraversable (FreeBi f) where
  bitraverse g h = iter (fmap bFree . bitraverse g id) . fmap (fmap bPure . h)

instance Eq2 f => Eq2 (FreeBi f) where
  liftEq2 v w (FreeBi l) (FreeBi r) = impl l r
    where
      impl l r = case (l, r) of
        (Pure x, Pure y) -> w x y
        (Free l, Free r) -> liftEq2 v impl l r
        _ -> False

instance (Bifunctor f, Show2 f) => Show2 (FreeBi f) where
  liftShowsPrec2 ia _ = reify (ReifiedShow ia) $ \p ->
    first (mkReflected p) .@@@ liftShowsPrec

instance (Bifunctor f, Hashable2 f) => Hashable2 (FreeBi f) where
  liftHashWithSalt2 ha = reify (ReifiedHashable ha) $ \p ->
    first (mkReflected p) .@@ liftHashWithSalt

instance (Functor f, Hashable1 f) => Hashable1 (Free f)
