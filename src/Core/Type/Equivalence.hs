{-# LANGUAGE LambdaCase #-}

module Core.Type.Equivalence where

import Control.Applicative (Alternative ((<|>)), liftA2)
import Control.Monad.Bifree (Bifree (BFree))
import Control.Monad.FreeBi (FreeBi (FreeBi), iter)
import Control.Monad.Quad (Quad (Quad))
import Core.Type.Syntax
import Data.Aps (Ap (..), Ap2 (..))
import Data.Bifunctor (Bifunctor (first))
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.Foldable (asum)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (ReifiedEq (ReifiedEq), mkReflected)
import Data.Result (Result (..))

------------------------------------- MULT -------------------------------------

type Offender a = IndexedBag a MultLit

checkMultEQ :: Eq a => MultTerm a -> MultTerm a -> Maybe (Offender a)
checkMultEQ l r =
  (fmap (`MultLit` False) <$> eqVia noWeakening)
    <|> (fmap (MultLit False) <$> eqVia noContraction)
  where
    eqVia f = checkBoolEQ (first f l) (first f r)

checkBoolEQ ::
  Eq a =>
  FreeBi MultF Bool a ->
  FreeBi MultF Bool a ->
  Maybe (IndexedBag a Bool)
checkBoolEQ l r =
  checkLE (eval mkDNF l) (eval mkCNF r)
    <|> checkLE (eval mkDNF r) (eval mkCNF l)
  where
    eval f = iter interpT . fmap f

checkLE :: Eq a => DNF a -> CNF a -> Maybe (IndexedBag a Bool)
checkLE (MkDNF dnf) (MkCNF cnf) = asum (liftA2 findSub dnf cnf)
  where
    findSub conj disj =
      if EqBag.isEmpty (conj `EqBag.intersection` disj)
        then Just (sub True conj <> sub False disj)
        else Nothing
    sub val set = val <$ EqBag.toMap set

type NormalForm a = [EqBag a]

newtype CNF a = MkCNF (NormalForm a)

mkCNF :: a -> CNF a
mkCNF = MkCNF . pure . EqBag.singleton

instance Eq a => Boolean (CNF a) where
  join (MkCNF l) (MkCNF r) = MkCNF (liftA2 (<>) l r)
  meet (MkCNF l) (MkCNF r) = MkCNF (l <> r)
  true = MkCNF []
  false = MkCNF [mempty]

newtype DNF a = MkDNF (NormalForm a)

mkDNF :: a -> DNF a
mkDNF = MkDNF . pure . EqBag.singleton

instance Eq a => Boolean (DNF a) where
  join (MkDNF l) (MkDNF r) = MkDNF (l <> r)
  meet (MkDNF l) (MkDNF r) = MkDNF (liftA2 (<>) l r)
  true = MkDNF [mempty]
  false = MkDNF []

------------------------------------ ROWS --------------------------------------

data RowEqError = EVars | EKeys | EUnder EntryKey

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

--------------------------------- TYPE + DATA ----------------------------------

type Assumption a = (a, a)

type TyEqAssumption n a =
  Either (Assumption (TypeTerm n a)) (Assumption (Position, DataTerm n a))

type Assumptions n a = [TyEqAssumption n a]

data DataVariety
  = VArrow
  | VForall ProperKind
  | VSpread Connective

getVariety :: DataF n a -> DataVariety
getVariety = \case
  PArrow _ _ -> VArrow
  PForall k _ -> VForall k
  PSpread c _ -> VSpread c

data TyEqError n
  = EData Position Position (Assumption DataVariety)
  | ESpread Position Position (NonEmpty RowEqError)
  | EMult Position Position (IndexedBag n MultLit)

type TyEqResult n a = Result (NonEmpty (TyEqError n)) (Assumptions n a)

checkTypeEQ ::
  (Eq n, Eq a) =>
  (Assumptions n a -> Bool) ->
  TypeTerm n a ->
  TypeTerm n a ->
  TyEqResult n a
checkTypeEQ f l r = case (l, r) of
  ( Quad (BFree (Ap (Ap2 (TLit ql pl ml)))),
    Quad (BFree (Ap (Ap2 (TLit qr pr mr))))
    ) ->
      (<>)
        <$> checkDataEQ f ql (Quad pl) qr (Quad pr)
        <*> fromMult ql qr (checkMultEQ ml ml)
  (l, r) -> Ok [Left (l, r)]
  where
    fromMult p q = \case
      Just errs -> Err $ pure $ EMult p q errs
      Nothing -> Ok []

checkDataEQ ::
  (Eq n, Eq a) =>
  (Assumptions n a -> Bool) ->
  Position ->
  DataTerm n a ->
  Position ->
  DataTerm n a ->
  TyEqResult n a
checkDataEQ v p l q r = case (l, r) of
  (Quad (BFree (Ap (Ap2 l))), Quad (BFree (Ap (Ap2 r)))) -> case (l, r) of
    (PArrow f t, PArrow f' t') ->
      (<>)
        <$> checkTypeEQ v (Quad f) (Quad f')
        <*> checkTypeEQ v (Quad t) (Quad t')
    (PForall k t, PForall k' t') ->
      if k == k'
        then checkTypeEQ v (Quad t) (Quad t')
        else Err $ pure $ EData p q (VForall k, VForall k')
    (PSpread c r, PSpread c' r') ->
      if c == c'
        then fromRow $
          reify (ReifiedEq $ finish v) $ \p ->
            checkRowEQ (reflected p r) (reflected p r')
        else Err $ pure $ EData p q (VSpread c, VSpread c')
    (l, r) -> Err $ pure $ EData p q (getVariety l, getVariety r)
  (l, r) -> Ok [Right ((p, l), (q, r))]
  where
    fromRow = \case
      [] -> Ok []
      (x : xs) -> Err $ pure $ ESpread p q (x :| xs)
    finish v l r =
      case checkTypeEQ v (Quad l) (Quad r) of
        Ok xs -> v xs
        Err _ -> False
    reflected = first . mkReflected
