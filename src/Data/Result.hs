{-# LANGUAGE DeriveFunctor #-}

module Data.Result where

import Control.Applicative (Alternative (..), liftA2)
import Control.Monad ((>=>))
import Data.Bifunctor (Bifunctor (..))

data Result e a = Err e | Ok a deriving (Functor)

result :: (a -> c) -> (b -> c) -> Result a b -> c
result f _ (Err x) = f x
result _ f (Ok x) = f x

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

newtype CtxResult s e a = CtxR {withCtx :: s -> Result e a} deriving (Functor)

runCtx :: s -> CtxResult s e a -> Result e a
runCtx = flip withCtx

instance Bifunctor (CtxResult s) where
  bimap f g x = CtxR $ bimap f g . withCtx x

instance Semigroup e => Applicative (CtxResult s e) where
  pure = CtxR . pure . pure
  f <*> x = CtxR $ liftA2 (<*>) (withCtx f) (withCtx x)

instance Semigroup e => Monad (CtxResult s e) where
  x >>= f = CtxR $ \s -> withCtx x s >>= runCtx s . f

instance Monoid e => Alternative (CtxResult s e) where
  empty = CtxR $ pure empty
  l <|> r = CtxR $ liftA2 (<|>) (withCtx l) (withCtx r)

mapCtx :: (s -> s') -> CtxResult s' e a -> CtxResult s e a
mapCtx f x = CtxR $ withCtx x . f
