{-# LANGUAGE LambdaCase #-}

module Core.Row where

import Core.Kind
import Data.Bifoldable (Bifoldable (..))
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import HashMultiMap (HashMultiMap)
import qualified HashMultiMap

data Row k v r = MkRow
  { rowLit :: HashMultiMap k [v],
    rowVar :: MultiSet r
  }

fromList :: (Eq k, Hashable k) => [(k, v)] -> Row k v r
fromList =
  flip MkRow MultiSet.empty
    . foldMap (\(k, v) -> HashMultiMap.singleton k [v])

fromVar :: Ord r => r -> Row k v r
fromVar = MkRow HashMultiMap.empty . MultiSet.singleton

instance (Eq k, Hashable k, Ord r) => Semigroup (Row k v r) where
  MkRow l v <> MkRow l' v' = MkRow (l <> l') (v <> v')

instance (Eq k, Hashable k, Ord r) => Monoid (Row k v r) where
  mempty = MkRow mempty mempty

data RowT l a
  = RLit l
  | RVar a
  | RJoin (RowT l a) (RowT l a)
  deriving (Show)

instance Bifoldable RowT where
  bifoldMap f g = \case
    RLit l -> f l
    RVar x -> g x
    RJoin a b -> bifoldMap f g a <> bifoldMap f g b

data RowLit k t
  = REmpty k
  | REntry String t
  deriving (Show)

instance Bifoldable RowLit where
  bifoldMap f g = \case
    REmpty k -> f k
    REntry _ t -> g t

type RowTerm t = RowT (RowLit ProperKind t) t

collect :: Applicative f => (t -> f ProperKind) -> RowTerm t -> f [ProperKind]
collect g = sequenceA . bifoldMap (pure . fmap Row . visit) (pure . g)
  where
    visit = bifoldr (const . pure) (const . g) undefined
