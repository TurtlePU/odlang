{-# LANGUAGE EmptyCase #-}

module Position where

data Position

instance Show Position where
  show x = case x of
