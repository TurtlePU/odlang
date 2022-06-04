{-# LANGUAGE LambdaCase #-}

module Data.EqBag where

import Control.Applicative (Applicative (..))
import Control.Composition (on, (.@))
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Prelude hiding (filter)
import qualified Prelude

newtype EqBag a = MkBag {unBag :: [NonEmpty a]}

empty :: EqBag a
empty = MkBag []

isEmpty :: EqBag a -> Bool
isEmpty = null . unBag

singleton :: a -> EqBag a
singleton = MkBag . pure . pure

insert :: Eq a => a -> EqBag a -> EqBag a
insert = unsafeCons . pure

filter :: (a -> Bool) -> EqBag a -> EqBag a
filter f = MkBag . Prelude.filter (f . NonEmpty.head) . unBag

contains :: Eq a => a -> EqBag a -> Bool
contains = unBag .@ any . (NonEmpty.head .@ (==))

intersection :: Eq a => EqBag a -> EqBag a -> EqBag a
intersection = filter . flip contains

values :: EqBag a -> [a]
values = map NonEmpty.head . unBag

instance Eq a => Eq (EqBag a) where
  (==) = bicomp (&&) lenEq ((compEq .@ flip any) .@ flip all) `on` unBag

instance Eq a => Semigroup (EqBag a) where
  (<>) = flip (foldr unsafeCons) . unBag

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
compEq = bicomp (&&) lenEq headEq

bicomp :: (a -> b -> c) -> (d -> e -> a) -> (d -> e -> b) -> d -> e -> c
bicomp = liftA2 . liftA2

lenEq :: Foldable f => f a -> f a -> Bool
lenEq = (==) `on` length

headEq :: Eq a => NonEmpty a -> NonEmpty a -> Bool
headEq = (==) `on` NonEmpty.head
