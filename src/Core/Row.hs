{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Row where

import Control.Monad.Free
import Core.Kind
import Data.Bifunctor (Bifunctor (..))
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.Function (fix)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Position (Position, Positioned, getPosition)
import Data.Result (mapCtx)

type EntryKey = String

data RowT e r
  = REmpty ProperKind
  | REntry EntryKey e
  | RJoin r r
  deriving (Functor)

instance Bifunctor RowT where
  bimap f g = \case
    REmpty k -> REmpty k
    REntry e x -> REntry e (f x)
    RJoin l r -> RJoin (g l) (g r)

type RowTerm t = Free (RowT t)

bimapRow :: (a -> b) -> (c -> d) -> RowTerm a c -> RowTerm b d
bimapRow f g = hoistFree (first f) . fmap g

newtype RowTerm' t = MkRowTerm' {unTerm' :: RowTerm t t}

instance Functor RowTerm' where
  fmap f = MkRowTerm' . bimapRow f f . unTerm'

synthesizeRowKind :: RowTerm' (PosResult ProperKind) -> PosResult ProperKind
synthesizeRowKind (MkRowTerm' r) = do
  ks <- sequenceA (iterA fold r)
  case NonEmpty.nub ks of
    Row k :| [] -> pure (Row k)
    k :| [] -> failWith (KMismatch k ERow)
    ks -> failWith (KDifferentRows ks)
  where
    fold = \case
      REmpty k -> pure $ pure $ Row k
      REntry _ v -> pure $ Row <$> v
      RJoin l r -> l <> r

checkRowEQ :: (Eq t, Eq r) => RowTerm t r -> RowTerm t r -> [RowEqError]
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey mkUnder litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow = extract . iter fold . fmap fromVar
    fold = \case
      REmpty _ -> mempty
      REntry k v -> fromEntry k v
      RJoin l r -> l <> r
    extract (MkRow (Multi lit) var) = (lit, var)
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
