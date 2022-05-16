{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Control.Monad.Bifree where

import Control.Monad (ap)
import Data.Aps (Ap (..), Ap2 (..))
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Hashable (Hashable (hashWithSalt))
import Data.Hashable.Lifted (Hashable1, Hashable2 (..))
import Data.Reflection (reify)
import Data.Reflection.Instances
import GHC.Generics (Generic, Generic1)

data Bifree g f b a
  = BPure a
  | BFree (Ap f (Bifree f g a b))
  deriving (Generic)
  deriving (Functor, Foldable, Eq1, Show1, Hashable1) via (Ap2 (Bifree g f) b)
  deriving (Eq, Show) via (Ap2 (Bifree g f) b a)

instance
  (Hashable a, Hashable b, Hashable1 g, Hashable1 f) =>
  Hashable (Bifree g f a b)

instance
  (Hashable1 g, Hashable1 f, Functor g, Functor f) =>
  Hashable2 (Bifree g f)
  where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \pa ->
    reify (ReifiedHashable hb) $ \pb ->
      hashWithSalt s $ bimap (mkReflected pa) (mkReflected pb) x

biliftF' :: Functor g => g a -> Bifree f g a b
biliftF' = monowrap . fmap BPure

biliftF :: (Functor f, Functor g) => f (g a) -> Bifree g f b a
biliftF = monowrap . fmap biliftF'

biwrap :: Functor f => f (g (Bifree g f b a)) -> Bifree g f b a
biwrap = monowrap . fmap monowrap

monowrap :: f (Bifree f g a b) -> Bifree g f b a
monowrap = BFree . Ap

biiter ::
  (Functor f, Functor g) => (f b -> a) -> (g a -> b) -> Bifree g f b a -> a
biiter _ _ (BPure x) = x
biiter v w (BFree (Ap fx)) = v (biiter w v <$> fx)

bihoist ::
  (Functor f', Functor g') =>
  (forall a. f a -> f' a) ->
  (forall a. g a -> g' a) ->
  Bifree g f b a ->
  Bifree g' f' b a
bihoist _ _ (BPure x) = BPure x
bihoist v w (BFree (Ap fx)) = BFree (Ap (bihoist w v <$> v fx))

lhoist ::
  (Functor f, Functor g') =>
  (forall a. g a -> g' a) ->
  Bifree g f b a ->
  Bifree g' f b a
lhoist = bihoist id

rhoist ::
  (Functor f', Functor g) =>
  (forall a. f a -> f' a) ->
  Bifree g f b a ->
  Bifree g f' b a
rhoist v = bihoist v id

bifirst ::
  (Bifunctor f, Bifunctor g, Functor (f b), Functor (g b)) =>
  (a -> b) ->
  Bifree (f a) (g a) c d ->
  Bifree (f b) (g b) c d
bifirst f = bihoist (first f) (first f)

bibimap ::
  (Bifunctor f, Bifunctor g, Functor (f c), Functor (g c)) =>
  (a -> c) ->
  (b -> d) ->
  Bifree (f a) (g a) b b ->
  Bifree (f c) (g c) d d
bibimap v w = bimap w w . bifirst v

biunfold ::
  (Functor f, Functor g) =>
  (c -> Either a (f d)) ->
  (d -> Either b (g c)) ->
  c ->
  Bifree g f b a
biunfold v w s = case v s of
  Left x -> BPure x
  Right xs -> monowrap (biunfold w v <$> xs)

biunfoldM ::
  (Traversable f, Traversable g, Monad m) =>
  (c -> m (Either a (f d))) ->
  (d -> m (Either b (g c))) ->
  c ->
  m (Bifree g f b a)
biunfoldM v w s =
  v s >>= \case
    Left x -> pure $ BPure x
    Right xs -> monowrap <$> traverse (biunfoldM w v) xs

instance (Eq1 g, Eq1 f) => Eq2 (Bifree g f) where
  liftEq2 v w l r = case (l, r) of
    (BPure x, BPure y) -> w x y
    (BFree l, BFree g) -> liftEq (liftEq2 w v) l g
    _ -> False

liftEq2Bifree ::
  (Eq2 g, Eq2 f, Bifunctor g, Bifunctor f) =>
  (a -> a -> Bool) ->
  (t -> t -> Bool) ->
  (b -> c -> Bool) ->
  (d -> e -> Bool) ->
  Bifree (g a) (f t) b d ->
  Bifree (g a) (f t) c e ->
  Bool
liftEq2Bifree u s v w l r = reify (ReifiedEq u) $ \p ->
  reify (ReifiedEq s) $ \q -> liftEq2 v w (dohoist q p l) (dohoist q p r)
  where
    dohoist p q = bihoist (ap2 p) (ap2 q)
    ap2 p = Ap2 . first (mkReflected p)

instance (Show1 g, Show1 f) => Show2 (Bifree g f) where
  liftShowsPrec2 ia la ib lb i = \case
    BPure x -> ib i x
    BFree w ->
      liftShowsPrec (liftShowsPrec2 ib lb ia la) (liftShowList2 ib lb ia la) i w

liftShowsPrec2Bifree ::
  (Show2 g, Show2 f, Bifunctor g, Bifunctor f) =>
  (Int -> a -> ShowS) ->
  (Int -> b -> ShowS) ->
  (Int -> c -> ShowS) ->
  ([c] -> ShowS) ->
  (Int -> d -> ShowS) ->
  ([d] -> ShowS) ->
  Int ->
  Bifree (g a) (f b) c d ->
  ShowS
liftShowsPrec2Bifree ia ib ic lc id ld i r = reify (ReifiedShow ia) $ \pa ->
  reify (ReifiedShow ib) $ \pb ->
    liftShowsPrec2 ic lc id ld i $ bihoist (ap2 pb) (ap2 pa) r
  where
    ap2 p = Ap2 . first (mkReflected p)

instance (Functor g, Functor f) => Bifunctor (Bifree g f) where
  bimap v w (BPure x) = BPure (w x)
  bimap v w (BFree fx) = BFree (bimap w v <$> fx)

instance (Functor g, Functor f) => Applicative (Bifree g f c) where
  pure = BPure
  (<*>) = ap

instance (Functor g, Functor f) => Monad (Bifree g f c) where
  BPure x >>= f = f x
  BFree r >>= f = BFree (llift f <$> r)

llift ::
  (Functor g, Functor f) =>
  (b -> Bifree f g a c) ->
  Bifree g f b a ->
  Bifree g f c a
llift _ (BPure x) = BPure x
llift h (BFree fx) = BFree ((>>= h) <$> fx)

instance (Foldable g, Foldable f) => Bifoldable (Bifree g f) where
  bifoldMap v w (BPure x) = w x
  bifoldMap v w (BFree fx) = foldMap (bifoldMap w v) fx

instance (Traversable g, Traversable h) => Bitraversable (Bifree g h) where
  bitraverse v w (BPure x) = pure <$> w x
  bitraverse v w (BFree fx) = BFree <$> sequenceA (bitraverse w v <$> fx)

instance (Traversable g, Traversable h) => Traversable (Bifree g h b) where
  traverse = bitraverse pure