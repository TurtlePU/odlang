{-# LANGUAGE LambdaCase #-}

module Core.Row where

import Core.Kind
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.Function (fix)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Position (Position, Positioned)

data RowT k e r
  = REmpty k
  | REntry e
  | RVar r
  | RJoin (RowT k e r) (RowT k e r)
  deriving (Show)

trifold :: Semigroup s => (k -> s) -> (e -> s) -> (r -> s) -> RowT k e r -> s
trifold f g h = fix $ \rec -> \case
  REmpty k -> f k
  REntry e -> g e
  RVar x -> h x
  RJoin l r -> rec l <> rec r

type EntryKey = String

type RowTerm t r = RowT ProperKind (EntryKey, t) r

synthesizeRowKind ::
  (Positioned ft -> KindingResult ProperKind) ->
  (Positioned fr -> KindingResult ProperKind) ->
  Position ->
  RowTerm (Positioned ft) (Positioned fr) ->
  KindingResult ProperKind
synthesizeRowKind g h p r = do
  ks <-
    sequenceA $
      trifold (pure . pure . Row) (pure . fmap Row . g . snd) (pure . h) r
  case NonEmpty.nub ks of
    Row k :| [] -> pure (Row k)
    k :| [] -> failWith (KMismatch p k ERow)
    ks -> failWith (KDifferentRows p ks)

checkRowEQ :: (Eq t, Eq r) => RowTerm t r -> RowTerm t r -> [RowEqError]
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey mkUnder litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow = extract . trifold (const mempty) (uncurry fromEntry) fromVar
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
