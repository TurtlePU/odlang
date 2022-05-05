{-# LANGUAGE LambdaCase #-}

module Core.Row where

import Core.Kind (ProperKind (Row))
import Data.Bifoldable (Bifoldable (..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap

type EntryKey = String

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

toNonEmpty :: (l -> b) -> (a -> b) -> RowT l a -> NonEmpty b
toNonEmpty f g = \case
  RLit l -> f l :| []
  RVar x -> g x :| []
  RJoin a b -> toNonEmpty f g a <> toNonEmpty f g b

data RowLit k t
  = REmpty k
  | REntry EntryKey t
  deriving (Show)

type RowTerm t = RowT (RowLit ProperKind t) t

collectK ::
  Applicative f => (t -> f ProperKind) -> RowTerm t -> f (NonEmpty ProperKind)
collectK g = sequenceA . toNonEmpty litK g
  where
    litK = \case
      REmpty k -> pure k
      REntry _ t -> g t

checkRowEQ :: (t -> t -> Bool) -> RowTerm t -> RowTerm t -> [RowEqError]
checkRowEQ eq l r =
  let MkRow (Multi ll) lv = intoRow l
      MkRow (Multi rl) rv = intoRow r
      eqs = HashMap.intersectionWith checkBagEQ' ll rl
   in [EKeys | HashMap.keysSet ll /= HashMap.keysSet rl]
        ++ HashMap.foldMapWithKey mkUnder eqs
        ++ [EVars | not (checkBagEQ eq lv rv)]
  where
    intoRow = bifoldMap fromLit fromVar
    checkBagEQ' l r = checkBagEQ eq (NonEmpty.toList l) (NonEmpty.toList r)
    fromLit = \case
      REmpty _ -> mempty
      REntry k v -> fromEntry k v
    mkUnder l = \case
      True -> [EUnder l]
      False -> []

checkBagEQ :: (t -> t -> Bool) -> [t] -> [t] -> Bool
checkBagEQ eq l r = checkCompsEq (intoComps l) (intoComps r)
  where
    intoComps = foldr compInsert []
    compInsert x = \case
      [] -> [x :| []]
      (y : ys) ->
        if x `eq` NonEmpty.head y
          then NonEmpty.cons x y : ys
          else y : compInsert x ys
    checkCompsEq l r = length l == length r && all (flip any l . compEq) r
    compEq xs ys =
      length xs == length ys && NonEmpty.head xs `eq` NonEmpty.head ys

data Row t r = MkRow
  { rowLit :: HashMultiMap EntryKey (NonEmpty t),
    rowVar :: [r]
  }

fromEntry :: EntryKey -> t -> Row t r
fromEntry k v = MkRow (HashMultiMap.singleton k (v :| [])) []

fromVar :: r -> Row t r
fromVar x = MkRow HashMultiMap.empty [x]

instance Semigroup (Row t r) where
  MkRow l v <> MkRow l' v' = MkRow (l <> l') (v <> v')

instance Monoid (Row t r) where
  mempty = MkRow mempty mempty

data RowEqError = EVars | EKeys | EUnder EntryKey
