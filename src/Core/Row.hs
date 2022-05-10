{-# LANGUAGE LambdaCase #-}

module Core.Row where

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

newtype RowTerm t r = MkRowTerm {unTerm :: RowT ProperKind (EntryKey, t) r}

mapRow :: (a -> b) -> RowTerm a a -> RowTerm b b
mapRow f = bimap f f

instance Bifunctor RowTerm where
  bimap f g = MkRowTerm . rec . unTerm
    where
      rec = \case
        REmpty k -> REmpty k
        REntry (k, t) -> REntry (k, f t)
        RVar x -> RVar (g x)
        RJoin l r -> rec l `RJoin` rec r

newtype RowTerm' t = MkRowTerm' {unTerm' :: RowTerm t t}

instance Functor RowTerm' where
  fmap f = MkRowTerm' . bimap f f . unTerm'

synthesizeRowKind :: RowTerm' (PosResult ProperKind) -> PosResult ProperKind
synthesizeRowKind (MkRowTerm' (MkRowTerm r)) = do
  ks <- sequenceA $ trifold (pure . pure . Row) (pure . fmap Row . snd) pure r
  case NonEmpty.nub ks of
    Row k :| [] -> pure (Row k)
    k :| [] -> failWith (KMismatch k ERow)
    ks -> failWith (KDifferentRows ks)

instance (Eq t, Eq r) => Eq (RowTerm t r) where
  t == t' = null (checkRowEQ t t')

checkRowEQ :: (Eq t, Eq r) => RowTerm t r -> RowTerm t r -> [RowEqError]
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey mkUnder litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow =
      extract . trifold (const mempty) (uncurry fromEntry) fromVar . unTerm
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
