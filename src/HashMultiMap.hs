module HashMultiMap where

import Data.HashMap.Strict (HashMap, singleton, unionWith)
import Data.Hashable (Hashable)
import Result (Res, err)

newtype HashMultiMap k v = HashMultiMap {unMulti :: HashMap k [v]}

multi :: HashMap k [v] -> HashMultiMap k v
multi map = HashMultiMap {unMulti = map}

one :: Hashable k => k -> v -> Res (HashMultiMap k v) f a
one k = err . multi . singleton k . pure

instance (Eq k, Hashable k) => Semigroup (HashMultiMap k v) where
  l <> r = multi $ unionWith (<>) (unMulti l) (unMulti r)
