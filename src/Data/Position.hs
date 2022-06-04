{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Position where

import Data.Hashable (Hashable (..))

data PositionEntry = PEntry {line :: Int, column :: Int} deriving (Show)

newtype Position = Pos [PositionEntry]
  deriving newtype (Semigroup, Monoid)
  deriving (Show)

instance Eq Position where
  _ == _ = True

instance Hashable Position where
  hashWithSalt = const
