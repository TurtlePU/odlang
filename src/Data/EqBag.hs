{-# LANGUAGE LambdaCase #-}

module Data.EqBag where

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty

newtype EqBag a = MkBag {unBag :: [NonEmpty a]}

empty :: EqBag a
empty = MkBag []

singleton :: a -> EqBag a
singleton = MkBag . pure . pure

insert :: Eq a => a -> EqBag a -> EqBag a
insert = unsafeCons . pure

instance Eq a => Eq (EqBag a) where
  MkBag b == MkBag b' = b `lenEq` b' && all (flip any b' . compEq) b

instance Eq a => Semigroup (EqBag a) where
  MkBag l <> r = foldr unsafeCons r l

instance Eq a => Monoid (EqBag a) where
  mempty = empty

unsafeCons :: Eq a => NonEmpty a -> EqBag a -> EqBag a
unsafeCons c = MkBag . cons' . unBag
  where
    cons' = \case
      [] -> [c]
      c' : cs ->
        if c `headEq` c'
          then (c <> c') : cs
          else c' : cons' cs

compEq :: Eq a => NonEmpty a -> NonEmpty a -> Bool
compEq xs ys = xs `lenEq` ys && xs `headEq` ys

lenEq :: Foldable f => f a -> f a -> Bool
lenEq = equating length

headEq :: Eq a => NonEmpty a -> NonEmpty a -> Bool
headEq = equating NonEmpty.head

equating :: Eq a => (b -> a) -> b -> b -> Bool
equating f x y = f x == f y