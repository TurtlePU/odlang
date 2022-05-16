module Data.FreeBi where

import Control.Monad.Free (Free (..), hoistFree)
import Data.Aps (Ap2 (..))
import Data.Bifunctor (Bifunctor (first))
import Data.Functor.Classes (Eq2 (..), Show1 (..), Show2)
import Data.Reflection (reify)
import Data.Reflection.Instances (reflectShow, ReifiedShow (..))

firstFree ::
  (Bifunctor f, Functor (f c)) => (a -> c) -> Free (f a) b -> Free (f c) b
firstFree g = hoistFree (first g)

bimapFree ::
  (Bifunctor f, Functor (f c)) =>
  (a -> c) ->
  (b -> d) ->
  Free (f a) b ->
  Free (f c) d
bimapFree v w = fmap w . firstFree v

liftEq2Free ::
  Eq2 f =>
  (a -> c -> Bool) ->
  (b -> d -> Bool) ->
  Free (f a) b ->
  Free (f c) d ->
  Bool
liftEq2Free v w l r = case (l, r) of
  (Pure x, Pure y) -> w x y
  (Free l, Free r) -> liftEq2 v (liftEq2Free v w) l r
  _ -> False

liftShowsPrec2Free ::
  (Bifunctor f, Show2 f) =>
  (Int -> a -> ShowS) ->
  (Int -> b -> ShowS) ->
  ([b] -> ShowS) ->
  Int ->
  Free (f a) b ->
  ShowS
liftShowsPrec2Free ia ib lb i x = reify (ReifiedShow ia) $ \p ->
  liftShowsPrec ib lb i $ hoistFree (Ap2 . first (reflectShow p)) x
