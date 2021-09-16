module HashMultiMap where

import Data.HashMap.Strict
import Data.Hashable
import Result

newtype HashMultiMap k v = HashMultiMap {unMulti :: HashMap k [v]}

multi :: HashMap k [v] -> HashMultiMap k v
multi map = HashMultiMap {unMulti = map}

one :: Hashable k => k -> v -> Res (HashMultiMap k v) f a
one = (. pure) . ((err . multi) .) . singleton

instance (Eq k, Hashable k) => Semigroup (HashMultiMap k v) where
  (<>) = (. unMulti) . (multi .) . unionWith mappend . unMulti
