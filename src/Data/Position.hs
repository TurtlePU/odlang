{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Position where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data PositionEntry = PEntry {line :: Int, column :: Int}
  deriving (Generic, Eq, Show)

instance Hashable PositionEntry

newtype Position = Pos [PositionEntry]
  deriving newtype (Hashable, Semigroup, Monoid)
  deriving (Eq, Show)
