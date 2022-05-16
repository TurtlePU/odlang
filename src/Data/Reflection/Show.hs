{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Reflection.Show
  ( ReflectedShow,
    reflectShow,
    ReifiedShow,
    withReifiedShow,
  )
where

import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies (..), reify)

newtype ReflectedShow s a = ReflectShow a

reflectShow :: Proxy s -> a -> ReflectedShow s a
reflectShow _ = ReflectShow

unreflectShow :: ReflectedShow s a -> a
unreflectShow (ReflectShow a) = a

newtype ReifiedShow a = ReifiedShow {reifiedShowsPrec :: Int -> a -> ShowS}

withReifiedShow ::
  (Int -> a -> ShowS) ->
  (forall s. Reifies s (ReifiedShow a) => Proxy s -> r) ->
  r
withReifiedShow reifiedShowsPrec = reify (ReifiedShow reifiedShowsPrec)

instance Reifies s (ReifiedShow a) => Show (ReflectedShow s a) where
  showsPrec i = reifiedShowsPrec (reflect (Proxy :: Proxy s)) i . unreflectShow
