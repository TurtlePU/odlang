{-# LANGUAGE DeriveFunctor #-}

module Result (Result (..), Res (..), ok, err, sift) where

import Control.Monad
import Data.Fix

data Result e a = Ok a | Err e deriving (Functor)

instance Semigroup e => Applicative (Result e) where
  pure = Ok

  Ok f <*> Ok x = Ok $ f x
  Ok _ <*> Err e = Err e
  Err e <*> Ok _ = Err e
  Err l <*> Err r = Err $ l <> r

instance Semigroup e => Monad (Result e) where
  Ok x >>= f = f x
  Err e >>= f = Err e

newtype Res e f a = Res {unres :: Result e (f a)} deriving (Functor)

ok :: f a -> Res e f a
ok value = Res {unres = Ok value}

err :: e -> Res e f a
err value = Res {unres = Err value}

sift :: (Semigroup e, Traversable f) => Fix (Res e f) -> Result e (Fix f)
sift = foldFix $ fmap wrapFix . sequenceA <=< unres
