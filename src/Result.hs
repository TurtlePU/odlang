{-# LANGUAGE DeriveFunctor #-}

module Result where

import Control.Applicative (Alternative (..), Applicative (..))
import Control.Monad (Monad (..), (>=>))
import Data.Bifunctor (Bifunctor (..))

data Result e a = Err e | Ok a deriving (Functor)

instance Bifunctor Result where
  bimap f g = result (Err . f) (Ok . g)

instance Semigroup e => Applicative (Result e) where
  pure = Ok

  Err l <*> Err r = Err $ l <> r
  Err e <*> Ok _ = Err e
  Ok _ <*> Err e = Err e
  Ok f <*> Ok x = Ok $ f x

instance Semigroup e => Monad (Result e) where
  Err e >>= f = Err e
  Ok x >>= f = f x

instance Monoid e => Alternative (Result e) where
  empty = Err mempty

  Err l <|> Err r = Err $ l <> r
  Ok x <|> _ = Ok x
  _ <|> Ok x = Ok x

result :: (a -> c) -> (b -> c) -> Result a b -> c
result f _ (Err x) = f x
result _ f (Ok x) = f x
