module HashMultiMap where

import Data.HashMap.Strict (HashMap, singleton, unionWith)
import Data.Hashable (Hashable)

newtype HashMultiMap k v = Multi {unMulti :: HashMap k v}

instance (Eq k, Hashable k, Semigroup v) => Semigroup (HashMultiMap k v) where
  l <> r = Multi $ unionWith (<>) (unMulti l) (unMulti r)
