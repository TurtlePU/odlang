{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}

module Control.Monad.Quad where

import Control.Monad.Bifree (Bifree (..), bihoist)
import qualified Control.Monad.Bifree as Bifree
import Data.Aps (Ap (..), Ap2 (..))
import Data.Biapplicative (Bifunctor (..))
import Data.Bifoldable (Bifoldable (..))
import Data.Bitraversable (Bitraversable (..), bisequence)
import Data.Functor.Classes (Eq1, Eq2 (..), Show1, Show2 (..))
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1, Hashable2 (..))
import Data.Reflection (reify)
import Data.Reflection.Instances

newtype Quad f g b a = Quad {runQuad :: Bifree (Ap2 f b) (Ap2 g b) a a}
  deriving (Functor, Foldable, Eq1, Show1, Hashable1) via (Ap2 (Quad f g) b)
  deriving (Eq, Show, Hashable) via (Ap2 (Quad f g) b a)

biiter ::
  (Bifunctor f, Bifunctor g) =>
  (f b a -> a) ->
  (g b a -> a) ->
  Quad f g b a ->
  a
biiter v w = Bifree.biiter (\(Ap2 x) -> w x) (\(Ap2 x) -> v x) . runQuad

instance (Bifunctor f, Bifunctor g) => Bifunctor (Quad f g) where
  bimap v w = Quad . bimap w w . bihoist (first v) (first v) . runQuad

instance
  (Bifunctor f, Bifunctor g, Bifoldable f, Bifoldable g) =>
  Bifoldable (Quad f g)
  where
  bifoldMap v w = biiter bifold bifold . bimap v w

instance (Bitraversable f, Bitraversable g) => Bitraversable (Quad f g) where
  bitraverse v w = fmap Quad . impl . runQuad . bimap v w
    where
      impl ::
        (Bitraversable f, Bitraversable g, Applicative h) =>
        Bifree (Ap2 f (h b)) (Ap2 g (h b)) (h a) (h a) ->
        h (Bifree (Ap2 f b) (Ap2 g b) a a)
      impl = \case
        BPure x -> BPure <$> x
        BFree (Ap u) -> BFree . Ap <$> bisequence (impl <$> u)

instance (Bitraversable f, Bitraversable g) => Traversable (Quad f g b) where
  traverse = bitraverse pure

instance (Eq2 f, Eq2 g) => Eq2 (Quad f g) where
  liftEq2 v w (Quad l) (Quad r) = impl v w l r
    where
      impl ::
        (Eq2 f, Eq2 g) =>
        (a -> c -> Bool) ->
        (b -> d -> Bool) ->
        Bifree (Ap2 f a) (Ap2 g a) b b ->
        Bifree (Ap2 f c) (Ap2 g c) d d ->
        Bool
      impl v w l r = case (l, r) of
        (BPure x, BPure y) -> w x y
        (BFree (Ap t), BFree (Ap u)) -> liftEq2 v (impl v w) t u
        _ -> False

instance (Bifunctor f, Bifunctor g, Show2 f, Show2 g) => Show2 (Quad f g) where
  liftShowsPrec2 ia _ ib lb i x = reify (ReifiedShow ia) $ \p ->
    liftShowsPrec2 ib lb ib lb i $ runQuad $ first (mkReflected p) x

instance
  (Bifunctor f, Bifunctor g, Hashable2 f, Hashable2 g) =>
  Hashable2 (Quad f g)
  where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt2 hb hb s $ runQuad $ first (mkReflected p) x
