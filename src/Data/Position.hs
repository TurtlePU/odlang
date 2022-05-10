{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}

module Data.Position where

import Data.Result

data Position

instance Show Position where
  show x = case x of

instance Semigroup Position where
  (<>) x = case x of

instance Monoid Position where
  mempty = undefined

data Positioned f = Posed
  { pos :: Position,
    rec :: f (Positioned f)
  }

withPosition ::
  (f (Positioned f) -> CtxResult (s, Position) e a) ->
  Positioned f ->
  CtxResult s e a
withPosition g (Posed p r) = mapCtx (,p) (g r)

getPosition :: CtxResult (s, Position) e Position
getPosition = CtxR $ \(_, p) -> Ok p

foldPositioned ::
  Functor f =>
  (f (CtxResult (s, Position) e a) -> CtxResult (s, Position) e a) ->
  f (Positioned f) ->
  CtxResult (s, Position) e a
foldPositioned g = g . fmap (mapCtx fst . withPosition (foldPositioned g))
