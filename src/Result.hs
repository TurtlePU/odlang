{-# LANGUAGE DeriveFunctor #-}

module Result where

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

res :: Result e (f a) -> Res e f a
res value = Res {unres = value}

ok :: f a -> Res e f a
ok = res . Ok

err :: e -> Res e f a
err = res . Err

sift :: (Semigroup e, Traversable f) => Fix (Res e f) -> Result e (Fix f)
sift = foldFix $ fmap wrapFix . sequenceA <=< unres
