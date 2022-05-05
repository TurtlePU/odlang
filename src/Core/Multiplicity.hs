{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Core.Multiplicity where

import Control.Applicative (liftA2, (<|>))
import Core.Kind
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (asum, for_)
import Data.Functor (($>))
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet, intersection, singleton, toMap)
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import Position

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
  | MVar a
  | MJoin (MultT l a) (MultT l a)
  | MMeet (MultT l a) (MultT l a)
  deriving (Show, Foldable, Functor)

eval :: Boolean b => MultT Bool b -> b
eval (MLit l) = fromBool l
eval (MVar x) = x
eval (MJoin t t') = eval t `join` eval t'
eval (MMeet t t') = eval t `meet` eval t'

instance Bifunctor MultT where
  bimap f g = \case
    MLit l -> MLit (f l)
    MVar x -> MVar (g x)
    MJoin t t' -> bimap f g t `MJoin` bimap f g t'
    MMeet t t' -> bimap f g t `MMeet` bimap f g t'

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Show)

type MultTerm = MultT MultLit

checkMultKind :: MultTerm (PosResult ProperKind) -> PosResult ProperKind
checkMultKind m = for_ m (intoCheck Mult) $> Mult

checkEQ ::
  (Eq a, Hashable a) => MultTerm a -> MultTerm a -> Maybe (HashMap a MultLit)
checkEQ l r =
  let lw = first noWeakening l
      lc = first noContraction l
      rw = first noWeakening r
      rc = first noContraction r
   in (fmap (`MultLit` False) <$> checkBoolEQ lw rw)
        <|> (fmap (MultLit False) <$> checkBoolEQ lc rc)

checkBoolEQ ::
  (Eq a, Hashable a) => MultT Bool a -> MultT Bool a -> Maybe (HashMap a Bool)
checkBoolEQ l r =
  let lc = eval (second mkCNF l)
      ld = eval (second mkDNF l)
      rc = eval (second mkCNF r)
      rd = eval (second mkDNF r)
   in checkLE ld rc <|> checkLE rd lc

checkLE :: (Eq a, Hashable a) => DNF a -> CNF a -> Maybe (HashMap a Bool)
checkLE (MkDNF dnf) (MkCNF cnf) = asum (liftA2 findSub dnf cnf)
  where
    findSub conj disj =
      if HashSet.null (conj `intersection` disj)
        then Just (sub True conj <> sub False disj)
        else Nothing
    sub val set = val <$ toMap set

type NormalForm a = [HashSet a]

newtype CNF a = MkCNF (NormalForm a)

mkCNF :: (Eq a, Hashable a) => a -> CNF a
mkCNF = MkCNF . pure . singleton

instance (Eq a, Hashable a) => Boolean (CNF a) where
  join (MkCNF l) (MkCNF r) = MkCNF (liftA2 (<>) l r)
  meet (MkCNF l) (MkCNF r) = MkCNF (l <> r)
  true = MkCNF []
  false = MkCNF [mempty]

newtype DNF a = MkDNF (NormalForm a)

mkDNF :: (Eq a, Hashable a) => a -> DNF a
mkDNF = MkDNF . pure . singleton

instance (Eq a, Hashable a) => Boolean (DNF a) where
  join (MkDNF l) (MkDNF r) = MkDNF (l <> r)
  meet (MkDNF l) (MkDNF r) = MkDNF (liftA2 (<>) l r)
  true = MkDNF [mempty]
  false = MkDNF []
