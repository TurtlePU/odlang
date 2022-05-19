module Data.HashMultiMap where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)

newtype HashMultiMap k v = Multi {unMulti :: HashMap k v}

empty :: HashMultiMap k v
empty = Multi HashMap.empty

singleton :: (Eq k, Hashable k) => k -> v -> HashMultiMap k v
singleton k = Multi . HashMap.singleton k

instance (Eq k, Hashable k, Semigroup v) => Semigroup (HashMultiMap k v) where
  Multi l <> Multi r = Multi $ HashMap.unionWith (<>) l r

instance (Eq k, Hashable k, Semigroup v) => Monoid (HashMultiMap k v) where
  mempty = Multi mempty
