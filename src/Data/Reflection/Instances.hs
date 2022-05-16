{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Reflection.Instances where

import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies (..), reify)

------------------------------------- SHOW -------------------------------------

newtype ReflectedShow s a = ReflectShow a

reflectShow :: Proxy s -> a -> ReflectedShow s a
reflectShow _ = ReflectShow

newtype ReifiedShow a = ReifiedShow {reifiedShowsPrec :: Int -> a -> ShowS}

instance Reifies s (ReifiedShow a) => Show (ReflectedShow s a) where
  showsPrec i (ReflectShow x) =
    reifiedShowsPrec (reflect (Proxy :: Proxy s)) i x

-------------------------------------- EQ --------------------------------------

newtype ReflectedEq s a = ReflectEq a

reflectEq :: Proxy s -> a -> ReflectedEq s a
reflectEq _ = ReflectEq

newtype ReifiedEq a = ReifiedEq {reifiedEq :: a -> a -> Bool}

instance Reifies s (ReifiedEq a) => Eq (ReflectedEq s a) where
  ReflectEq l == ReflectEq r = reifiedEq (reflect (Proxy :: Proxy s)) l r
