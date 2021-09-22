{-# LANGUAGE TypeFamilies #-}

module NonSingle where

import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty)
import GHC.Exts (IsList (..))

infixr 5 :||

data NonSingle a = a :|| NonEmpty a

instance IsList (NonSingle a) where
  type Item (NonSingle a) = a

  fromList (x : x' : xs) = x :|| x' :| xs
  fromList _ = undefined

  toList (x :|| x' :| xs) = x : x' : xs

fromNonEmpty :: NonEmpty a -> Either a (NonSingle a)
fromNonEmpty (x :| xs) = case nonEmpty xs of
  Nothing -> Left x
  Just xs -> Right $ x :|| xs

nonSingle :: [a] -> Maybe (Either a (NonSingle a))
nonSingle = fmap fromNonEmpty . nonEmpty

infixl 4 |>

(|>) :: NonSingle a -> a -> NonSingle a
x :|| x' :| xs |> x'' = x :|| x' :| (xs `append` x'')
  where
    append [] = pure
    append (x : xs) = (x :) . append xs
