{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}

module Data.Position where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Position deriving (Generic)

instance Hashable Position

instance Eq Position where
  (==) x = case x of

instance Show Position where
  show x = case x of

instance Semigroup Position where
  (<>) x = case x of

instance Monoid Position where
  mempty = undefined
