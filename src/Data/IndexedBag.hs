{-# LANGUAGE DeriveTraversable #-}

module Data.IndexedBag where

import Data.Biapplicative (Bifunctor (..))

newtype IndexedBag k v = IBag [(k, v)]
  deriving (Show, Functor, Foldable, Traversable)

instance Bifunctor IndexedBag where
  bimap f g (IBag xs) = IBag (bimap f g <$> xs)

instance Semigroup (IndexedBag k v) where
  IBag xs <> IBag ys = IBag (xs <> ys)
