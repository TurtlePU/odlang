{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Reflection.Instances where

import Control.Composition ((.@))
import Data.Function (on)
import Data.Hashable (Hashable (..))
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies (..), reify)

newtype Reflected s a = Reflect {unreflect :: a}

mkReflected :: Proxy s -> a -> Reflected s a
mkReflected _ = Reflect

------------------------------------- SHOW -------------------------------------

newtype ReifiedShow a = ReifiedShow {reifiedShowsPrec :: Int -> a -> ShowS}

instance Reifies s (ReifiedShow a) => Show (Reflected s a) where
  showsPrec = unreflect .@ reifiedShowsPrec (reflect (Proxy :: Proxy s))

-------------------------------------- EQ --------------------------------------

newtype ReifiedEq a = ReifiedEq {reifiedEq :: a -> a -> Bool}

instance Reifies s (ReifiedEq a) => Eq (Reflected s a) where
  (==) = reifiedEq (reflect (Proxy :: Proxy s)) `on` unreflect

----------------------------------- HASHABLE -----------------------------------

newtype ReifiedHashable a = ReifiedHashable
  {reifiedHashWithSalt :: Int -> a -> Int}

instance Reifies s (ReifiedHashable a) => Hashable (Reflected s a) where
  hashWithSalt = unreflect .@ reifiedHashWithSalt (reflect (Proxy :: Proxy s))
