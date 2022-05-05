{-# LANGUAGE LambdaCase #-}

module Core.Row where

import Core.Kind (ProperKind (Row))
import Data.Bifoldable (Bifoldable (..))
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty

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

checkRowEQ :: Eq t => RowTerm t -> RowTerm t -> [RowEqError]
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey mkUnder litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow term =
      let MkRow (Multi lit) var = bifoldMap fromLit fromVar term
       in (lit, var)
    fromLit = \case
      REmpty _ -> mempty
      REntry k v -> fromEntry k v
    mkUnder l = \case
      True -> [EUnder l]
      False -> []

data Row t r = MkRow
  { rowLit :: HashMultiMap EntryKey (EqBag t),
    rowVar :: EqBag r
  }

fromEntry :: EntryKey -> t -> Row t r
fromEntry k =
  flip MkRow EqBag.empty
    . HashMultiMap.singleton k
    . EqBag.singleton

fromVar :: r -> Row t r
fromVar = MkRow HashMultiMap.empty . EqBag.singleton

instance (Eq t, Eq r) => Semigroup (Row t r) where
  MkRow l v <> MkRow l' v' = MkRow (l <> l') (v <> v')

instance (Eq t, Eq r) => Monoid (Row t r) where
  mempty = MkRow mempty mempty

data RowEqError = EVars | EKeys | EUnder EntryKey
