{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Reflection.Instances where

import Data.Hashable (Hashable (..))
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies (..), reify)

newtype Reflected s a = Reflect a

mkReflected :: Proxy s -> a -> Reflected s a
mkReflected _ = Reflect

------------------------------------- SHOW -------------------------------------

newtype ReifiedShow a = ReifiedShow {reifiedShowsPrec :: Int -> a -> ShowS}

instance Reifies s (ReifiedShow a) => Show (Reflected s a) where
  showsPrec i (Reflect x) =
    reifiedShowsPrec (reflect (Proxy :: Proxy s)) i x

-------------------------------------- EQ --------------------------------------

newtype ReifiedEq a = ReifiedEq {reifiedEq :: a -> a -> Bool}

instance Reifies s (ReifiedEq a) => Eq (Reflected s a) where
  Reflect l == Reflect r = reifiedEq (reflect (Proxy :: Proxy s)) l r

----------------------------------- HASHABLE -----------------------------------

newtype ReifiedHashable a = ReifiedHashable
  {reifiedHashWithSalt :: Int -> a -> Int}

instance Reifies s (ReifiedHashable a) => Hashable (Reflected s a) where
  hashWithSalt s (Reflect x) =
    reifiedHashWithSalt (reflect (Proxy :: Proxy s)) s x
