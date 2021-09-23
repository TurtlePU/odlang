module HashMultiMap where

import Data.HashMap.Strict (HashMap, singleton, unionWith)
import Data.Hashable (Hashable)

newtype HashMultiMap k v = HashMultiMap {unMulti :: HashMap k [v]}

multi :: HashMap k [v] -> HashMultiMap k v
multi hashMap = HashMultiMap {unMulti = hashMap}

instance (Eq k, Hashable k) => Semigroup (HashMultiMap k v) where
  l <> r = multi $ unionWith (<>) (unMulti l) (unMulti r)
