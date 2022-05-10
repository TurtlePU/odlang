{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Multiplicity where

import Control.Applicative (liftA2, (<|>))
import Control.Monad.Free (Free, hoistFree, iter)
import Core.Kind
import Data.Bifunctor (Bifunctor (..))
import Data.EqBag
import Data.Foldable (asum, for_)
import Data.Functor (($>))
import Data.IndexedBag
import Data.Maybe (isNothing)
import Data.Position

class Boolean a where
  join :: a -> a -> a
  meet :: a -> a -> a

  true :: a
  true = fromBool True

  false :: a
  false = fromBool False

  fromBool :: Bool -> a
  fromBool True = true
  fromBool False = false

instance Boolean Bool where
  join = (||)
  meet = (&&)
  fromBool = id

data MultT l a
  = MLit l
  | MJoin a a
  | MMeet a a
  deriving (Show, Foldable, Functor)

interp :: Boolean b => MultT Bool b -> b
interp = \case
  MLit x -> fromBool x
  MJoin l r -> l `join` r
  MMeet l r -> l `meet` r

instance Bifunctor MultT where
  bimap f g = \case
    MLit l -> MLit (f l)
    MJoin t t' -> g t `MJoin` g t'
    MMeet t t' -> g t `MMeet` g t'

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Show)

type MultTerm = Free (MultT MultLit)

checkMultKind :: MultTerm (PosResult ProperKind) -> PosResult ProperKind
checkMultKind m = for_ m (intoCheck Mult) $> Mult

checkMultEQ :: Eq a => MultTerm a -> MultTerm a -> Maybe (IndexedBag a MultLit)
checkMultEQ l r =
  let lw = mapLit noWeakening l
      lc = mapLit noContraction l
      rw = mapLit noWeakening r
      rc = mapLit noContraction r
   in (fmap (`MultLit` False) <$> checkBoolEQ lw rw)
        <|> (fmap (MultLit False) <$> checkBoolEQ lc rc)
  where
    mapLit f = hoistFree (first f)

checkBoolEQ ::
  Eq a =>
  Free (MultT Bool) a ->
  Free (MultT Bool) a ->
  Maybe (IndexedBag a Bool)
checkBoolEQ l r =
  let lc = eval mkCNF l
      ld = eval mkDNF l
      rc = eval mkCNF r
      rd = eval mkDNF r
   in checkLE ld rc <|> checkLE rd lc
  where
    eval f = iter interp . fmap f

checkLE :: Eq a => DNF a -> CNF a -> Maybe (IndexedBag a Bool)
checkLE (MkDNF dnf) (MkCNF cnf) = asum (liftA2 findSub dnf cnf)
  where
    findSub conj disj =
      if isEmpty (conj `intersection` disj)
        then Just (sub True conj <> sub False disj)
        else Nothing
    sub val set = val <$ toMap set

type NormalForm a = [EqBag a]

newtype CNF a = MkCNF (NormalForm a)

mkCNF :: a -> CNF a
mkCNF = MkCNF . pure . singleton

instance Eq a => Boolean (CNF a) where
  join (MkCNF l) (MkCNF r) = MkCNF (liftA2 (<>) l r)
  meet (MkCNF l) (MkCNF r) = MkCNF (l <> r)
  true = MkCNF []
  false = MkCNF [mempty]

newtype DNF a = MkDNF (NormalForm a)

mkDNF :: a -> DNF a
mkDNF = MkDNF . pure . singleton

instance Eq a => Boolean (DNF a) where
  join (MkDNF l) (MkDNF r) = MkDNF (l <> r)
  meet (MkDNF l) (MkDNF r) = MkDNF (liftA2 (<>) l r)
  true = MkDNF [mempty]
  false = MkDNF []
