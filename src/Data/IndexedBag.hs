{-# LANGUAGE DeriveTraversable #-}

module Data.IndexedBag where

newtype IndexedBag k v = IBag [(k, v)]
  deriving (Show, Functor, Foldable, Traversable)

instance Semigroup (IndexedBag k v) where
  IBag xs <> IBag ys = IBag (xs <> ys)
