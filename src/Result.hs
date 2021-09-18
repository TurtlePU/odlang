{-# LANGUAGE DeriveFunctor #-}

module Result where

import Control.Applicative (Alternative (..), Applicative (..))
import Control.Monad (Monad (..), (>=>))
import Data.Bifunctor (Bifunctor (..))
import Data.Fix (Fix (..), foldFix, wrapFix)

data Result e a = Ok a | Err e deriving (Functor)

instance Bifunctor Result where
  bimap f g = result (Err . f) (Ok . g)

instance Semigroup e => Applicative (Result e) where
  pure = Ok

  Ok f <*> Ok x = Ok $ f x
  Ok _ <*> Err e = Err e
  Err e <*> Ok _ = Err e
  Err l <*> Err r = Err $ l <> r

instance Semigroup e => Monad (Result e) where
  Ok x >>= f = f x
  Err e >>= f = Err e

instance Monoid e => Alternative (Result e) where
  empty = Err mempty

  Ok x <|> _ = Ok x
  _ <|> Ok x = Ok x
  Err l <|> Err r = Err $ l <> r

result :: (a -> c) -> (b -> c) -> Result a b -> c
result f _ (Err x) = f x
result _ f (Ok x) = f x

newtype Res e f a = Res {unres :: Result e (f a)} deriving (Functor)

res :: Result e (f a) -> Res e f a
res value = Res {unres = value}

ok :: f a -> Res e f a
ok = res . Ok

err :: e -> Res e f a
err = res . Err

sift :: (Semigroup e, Traversable f) => Fix (Res e f) -> Result e (Fix f)
sift = foldFix $ unres >=> fmap wrapFix . sequenceA
