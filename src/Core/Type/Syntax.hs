{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module Core.Type.Syntax where

import Algebra.Lattice (BoundedLattice, Lattice (..), fromBool)
import Control.Monad.FreeBi (FreeBi, iter)
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Bifunctor.TH
import Data.Bitraversable (Bitraversable (..))
import Data.Deriving (deriveEq1, deriveEq2, deriveShow1, deriveShow2)
import Data.Fix (Fix)
import Data.Functor.Identity (Identity)
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..), Hashable2 (..))
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (ReifiedHashable (..), mkReflected)
import GHC.Generics (Generic, Generic1)

------------------------------------ KINDS -------------------------------------

data SimpleKind
  = Data
  | SimpleKind :*: SimpleKind
  deriving (Generic, Eq, Show)

instance Hashable SimpleKind

data ProperKind
  = Simple SimpleKind
  | Type
  | Mult
  | Row ProperKind
  | ProperKind :**: ProperKind
  | ProperKind :->: ProperKind
  deriving (Generic, Eq, Show)

instance Hashable ProperKind

-------------------------------- MULTIPLICITIES --------------------------------

data MultF l a
  = MLit l
  | MJoin a a
  | MMeet a a
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

evalM :: BoundedLattice b => (a -> b) -> FreeBi MultF Bool a -> b
evalM f = iter interpT . fmap f
  where
    interpT (MLit x) = fromBool x
    interpT (MJoin l r) = l \/ r
    interpT (MMeet l r) = l /\ r

$(deriveBifunctor ''MultF)
$(deriveBifoldable ''MultF)
$(deriveBitraversable ''MultF)
$(deriveEq2 ''MultF)
$(deriveEq1 ''MultF)
$(deriveShow2 ''MultF)
$(deriveShow1 ''MultF)

instance Hashable2 MultF where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt hb s $ first (mkReflected p) x

instance Hashable l => Hashable1 (MultF l)

instance (Hashable l, Hashable a) => Hashable (MultF l a)

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Generic, Eq, Show)

instance Hashable MultLit

type MultTerm = FreeBi MultF MultLit

------------------------------------- ROWS -------------------------------------

data RowF e r
  = REmpty ProperKind
  | REntry e
  | RJoin r r
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

$(deriveBifunctor ''RowF)
$(deriveBifoldable ''RowF)
$(deriveBitraversable ''RowF)
$(deriveEq2 ''RowF)
$(deriveEq1 ''RowF)
$(deriveShow2 ''RowF)
$(deriveShow1 ''RowF)

instance Hashable2 RowF where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt hb s $ first (mkReflected p) x

instance Hashable e => Hashable1 (RowF e)

instance (Hashable e, Hashable r) => Hashable (RowF e r)

type EntryKey = String

type RowTerm = Biff (FreeBi RowF) ((,) EntryKey) Identity

------------------------------------- DATA -------------------------------------

data Connective = CAnd | CWith | COr deriving (Generic, Eq, Show)

instance Hashable Connective

data DataF a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective a
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

$(deriveEq1 ''DataF)
$(deriveShow1 ''DataF)

instance Hashable1 DataF

instance Hashable a => Hashable (DataF a)

------------------------------------- TYPE -------------------------------------

data TypeF a = TLit {tyDat :: a, tyMul :: a}
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

$(deriveEq1 ''TypeF)
$(deriveShow1 ''TypeF)

instance Hashable1 TypeF

instance Hashable a => Hashable (TypeF a)

------------------------------------ LAMBDA ------------------------------------

data LambdaF a
  = LVar Int
  | LApp Position a a
  | LAbs ProperKind a
  | LSPair Position a a
  | LPair a a
  | LFst Position a
  | LSnd Position a
  | LDat Position a
  | LMul Position a
  | LFix Position SimpleKind a
  | LMap Position a a
  | LRnd Position a
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

$(deriveEq1 ''LambdaF)
$(deriveShow1 ''LambdaF)

instance Hashable1 LambdaF

instance Hashable a => Hashable (LambdaF a)

--------------------------------- GENERIC TERM ---------------------------------

data TermF a
  = TLam (LambdaF a)
  | TType Position (TypeF a)
  | TData Position (DataF a)
  | TRow Position (Join RowTerm a)
  | TMul Position (MultTerm a)
  deriving (Generic1, Functor, Foldable, Traversable, Generic, Eq, Show)

$(deriveEq1 ''TermF)
$(deriveShow1 ''TermF)

instance Hashable2 f => Hashable1 (Join f) where
  liftHashWithSalt ha s = liftHashWithSalt2 ha ha s . runJoin

instance (Hashable2 f, Hashable a) => Hashable (Join f a) where
  hashWithSalt = liftHashWithSalt hashWithSalt

instance (Hashable2 p, Hashable1 f, Hashable1 g) => Hashable2 (Biff p f g) where
  liftHashWithSalt2 ha hb s =
    liftHashWithSalt2 (liftHashWithSalt ha) (liftHashWithSalt hb) s . runBiff

instance Hashable1 TermF

instance Hashable a => Hashable (TermF a)

type Term = Fix TermF
