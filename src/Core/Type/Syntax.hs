{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}

module Core.Type.Syntax where

import Control.Monad.Free (Free (..), hoistFree, iter)
import Data.Ap2 (Ap2 (..))
import Data.Bifree (Bifree)
import Data.Bifunctor (Bifunctor (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Position (Position)
import Data.Reflection.Show (withReifiedShow, reflectShow)
import Data.FreeBi (bimapFree, liftEq2Free, liftShowsPrec2Free)

------------------------------------ KINDS -------------------------------------

data SimpleKind
  = Data
  | SimpleKind :*: SimpleKind
  deriving (Show, Eq)

data ProperKind
  = Simple SimpleKind
  | Type
  | Mult
  | Row ProperKind
  | ProperKind :**: ProperKind
  | ProperKind :->: ProperKind
  deriving (Show, Eq)

-------------------------------- MULTIPLICITIES --------------------------------

data MultT l a
  = MLit l
  | MJoin a a
  | MMeet a a
  deriving (Foldable)
  deriving (Functor, Eq1, Show1) via (Ap2 MultT l)
  deriving (Eq, Show) via (Ap2 MultT l a)

instance Bifunctor MultT where
  bimap f g = \case
    MLit b -> MLit (f b)
    MJoin l r -> MJoin (g l) (g r)
    MMeet l r -> MMeet (g l) (g r)

instance Eq2 MultT where
  liftEq2 f g l r = case (l, r) of
    (MLit b, MLit b') -> f b b'
    (MJoin l r, MJoin l' r') -> g l l' && g r r'
    (MMeet l r, MMeet l' r') -> g l l' && g r r'
    _ -> False

instance Show2 MultT where
  liftShowsPrec2 ia _ ib _ i = \case
    MLit b -> ia i b
    MJoin l r ->
      showParen (i > join_prec) $
        ib (join_prec + 1) l . showString " \\/ " . ib (join_prec + 1) r
    MMeet l r ->
      showParen (i > meet_prec) $
        ib (meet_prec + 1) l . showString " /\\ " . ib (meet_prec + 1) r
    where
      join_prec = 5
      meet_prec = 6

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Show, Eq)

type MultTerm = Free (MultT MultLit)

--------------------------------- BOOLEAN CLASS --------------------------------

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

interpT :: Boolean b => MultT Bool b -> b
interpT = \case
  MLit x -> fromBool x
  MJoin l r -> l `join` r
  MMeet l r -> l `meet` r

interp :: Boolean b => Free (MultT Bool) b -> b
interp = iter interpT

------------------------------------- ROWS -------------------------------------

type EntryKey = String

data RowT e r
  = REmpty ProperKind
  | REntry EntryKey e
  | RJoin r r
  deriving (Functor, Eq1, Show1) via (Ap2 RowT e)
  deriving (Eq, Show) via (Ap2 RowT e r)

instance Bifunctor RowT where
  bimap f g = \case
    REmpty k -> REmpty k
    REntry k v -> REntry k (f v)
    RJoin l r -> RJoin (g l) (g r)

instance Eq2 RowT where
  liftEq2 f g l r = case (l, r) of
    (REmpty k, REmpty k') -> k == k'
    (REntry k v, REntry k' v') -> k == k' && f v v'
    (RJoin l r, RJoin l' r') -> g l l' && g r r'
    _ -> False

instance Show2 RowT where
  liftShowsPrec2 ia _ ib _ i = \case
    REmpty k ->
      showParen (i > app_prec) $ showString "{/} " . showsPrec (app_prec + 1) k
    REntry k v ->
      showParen (i > colon_prec) $
        showString k . showString ": " . ia (colon_prec + 1) v
    RJoin l r ->
      showParen (i > join_prec) $
        ib (join_prec + 1) l . showString " \\/ " . ib (join_prec + 1) r
    where
      app_prec = 10
      colon_prec = 8
      join_prec = 5

type RowTerm t = Free (RowT t)

------------------------------------- DATA -------------------------------------

data Connective = CAnd | CWith | COr deriving (Show, Eq)

showConnective :: Connective -> ShowS -> ShowS
showConnective c s =
  showString (fst $ braces c) . s . showString (snd $ braces c)
  where
    braces = \case
      CAnd -> ("{", "}")
      CWith -> ("[", "]")
      COr -> ("(|", "|)")

data DataT n a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective (RowTerm a n)
  deriving (Functor, Eq1, Show1) via (Ap2 DataT n)
  deriving (Eq, Show) via (Ap2 DataT n a)

instance Bifunctor DataT where
  bimap f g = \case
    PArrow d c -> PArrow (g d) (g c)
    PForall k t -> PForall k (g t)
    PSpread c r -> PSpread c (bimapFree g f r)

instance Eq2 DataT where
  liftEq2 f g l r = case (l, r) of
    (PArrow c d, PArrow c' d') -> g c c' && g d d'
    (PForall k t, PForall k' t') -> k == k' && g t t'
    (PSpread c r, PSpread c' r') -> c == c' && liftEq2Free g f r r'
    _ -> False

instance Show2 DataT where
  liftShowsPrec2 ia la ib _ i = \case
    PArrow c d ->
      showParen (i > arr_prec) $
        ib (arr_prec + 1) c . showString " -> " . ib (arr_prec + 1) d
    PForall k t ->
      showParen (i > arr_prec) $
        showString "∀ "
          . showsPrec (arr_prec + 1) k
          . showString ". "
          . ib (arr_prec + 1) t
    PSpread c r -> showConnective c $ liftShowsPrec2Free ib ia la i r
    where
      arr_prec = 6

type DataTerm n a = Bifree (TypeT n) (DataT n) a a

------------------------------------- TYPE -------------------------------------

data TypeT n a = TLit
  { tyPos :: Position,
    tyPre :: a,
    tyMul :: MultTerm n
  }
  deriving (Functor, Eq1, Show1) via (Ap2 TypeT n)
  deriving (Eq, Show) via (Ap2 TypeT n a)

instance Bifunctor TypeT where
  bimap f g (TLit p q m) = TLit p (g q) (fmap f m)

instance Eq2 TypeT where
  liftEq2 f g (TLit p q m) (TLit p' q' m') = p == p' && g q q' && liftEq f m m'

instance Show2 TypeT where
  liftShowsPrec2 ia la ib _ i (TLit p q m) =
    showParen (i > 0) $
      showsPrec (app_prec + 1) p
        . showString " "
        . ib (app_prec + 1) q
        . showString " % "
        . liftShowsPrec ia la (mod_prec + 1) m
    where
      app_prec = 10
      mod_prec = 4

type TypeTerm n a = Bifree (DataT n) (TypeT n) a a
