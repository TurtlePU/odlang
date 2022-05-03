module HashMultiMap where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable

newtype HashMultiMap k v = Multi {unMulti :: HashMap k v}

empty :: HashMultiMap k v
empty = Multi HashMap.empty

singleton :: (Eq k, Hashable k) => k -> v -> HashMultiMap k v
singleton k v = Multi (HashMap.singleton k v)

instance (Eq k, Hashable k, Semigroup v) => Semigroup (HashMultiMap k v) where
  l <> r = Multi $ HashMap.unionWith (<>) (unMulti l) (unMulti r)

instance (Eq k, Hashable k, Semigroup v) => Monoid (HashMultiMap k v) where
  mempty = Multi mempty
