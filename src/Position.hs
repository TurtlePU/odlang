{-# LANGUAGE EmptyCase #-}

module Position where

data Position

instance Show Position where
  show x = case x of

instance Semigroup Position where
  (<>) x = case x of

instance Monoid Position where
  mempty = undefined
