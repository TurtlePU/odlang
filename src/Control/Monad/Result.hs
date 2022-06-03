{-# LANGUAGE DeriveFunctor #-}

module Control.Monad.Result where

import Control.Applicative (Alternative (..), liftA2)
import Control.Monad.Reader (ReaderT (..), mapReaderT, withReaderT)
import Data.Bifunctor (Bifunctor (..))

data Result e a = Err e | Ok a deriving (Functor, Show, Eq)

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

type CtxResult s f e = ReaderT s (Result (f e))

runCtx :: s -> CtxResult s f e a -> Result (f e) a
runCtx = flip runReaderT

mapCtx :: (s -> s') -> CtxResult s' f e a -> CtxResult s f e a
mapCtx = withReaderT

failWith :: Applicative f => e -> CtxResult s f e a
failWith = ReaderT . const . Err . pure

mapErrs :: Functor f => (e -> e') -> CtxResult s f e a -> CtxResult s f e' a
mapErrs = mapErr . fmap

mapErr :: (e -> e') -> ReaderT s (Result e) a -> ReaderT s (Result e') a
mapErr = mapReaderT . first
