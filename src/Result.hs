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

newtype CtxResult s e a = CtxR { withCtx :: s -> Result e a } deriving (Functor)

instance Bifunctor (CtxResult s) where
  bimap f g x = CtxR $ bimap f g . withCtx x

instance Semigroup e => Applicative (CtxResult s e) where
  pure = CtxR . pure . pure
  f <*> x = CtxR $ (<*>) <$> withCtx f <*> withCtx x

instance Semigroup e => Monad (CtxResult s e) where
  x >>= f = CtxR $ (>>=) <$> withCtx x <*> ((. f) . flip withCtx)

instance Monoid e => Alternative (CtxResult s e) where
  empty = CtxR $ pure empty
  l <|> r = CtxR $ (<|>) <$> withCtx l <*> withCtx r

mapCtx :: (s -> s') -> CtxResult s' e a -> CtxResult s e a
mapCtx f x = CtxR $ withCtx x . f
