{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Core.Type.Syntax where

import Control.Monad.Free (Free, hoistFree, iter)
import Data.Aps (Ap (..), Ap2 (..))
import Data.Bifree (Bifree, bibimap, liftShowsPrec2Bifree)
import Data.Bifunctor (Bifunctor (..))
import Data.Fix (Fix)
import Data.FreeBi (bimapFree, liftEq2Free, liftShowsPrec2Free)
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.Position (Position)
import GHC.Generics (Generic, Generic1)

instance (Functor f, Hashable1 f) => Hashable1 (Free f)

instance (Hashable a, Hashable (f (Free f a))) => Hashable (Free f a)

------------------------------------ KINDS -------------------------------------

data SimpleKind
  = Data
  | SimpleKind :*: SimpleKind
  deriving (Show, Eq, Generic)

instance Hashable SimpleKind

data ProperKind
  = Simple SimpleKind
  | Type
  | Mult
  | Row ProperKind
  | ProperKind :**: ProperKind
  | ProperKind :->: ProperKind
  deriving (Show, Eq, Generic)

instance Hashable ProperKind

-------------------------------- MULTIPLICITIES --------------------------------

data MultF l a
  = MLit l
  | MJoin a a
  | MMeet a a
  deriving (Foldable, Generic, Generic1)
  deriving (Functor, Eq1, Show1) via (Ap2 MultF l)
  deriving (Eq, Show) via (Ap2 MultF l a)

instance (Hashable l, Hashable a) => Hashable (MultF l a)

instance Hashable l => Hashable1 (MultF l)

instance Bifunctor MultF where
  bimap f g = \case
    MLit b -> MLit (f b)
    MJoin l r -> MJoin (g l) (g r)
    MMeet l r -> MMeet (g l) (g r)

instance Eq2 MultF where
  liftEq2 f g l r = case (l, r) of
    (MLit b, MLit b') -> f b b'
    (MJoin l r, MJoin l' r') -> g l l' && g r r'
    (MMeet l r, MMeet l' r') -> g l l' && g r r'
    _ -> False

instance Show2 MultF where
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
  deriving (Show, Eq, Generic)

instance Hashable MultLit

type MultTerm = Free (MultF MultLit)

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

interpT :: Boolean b => MultF Bool b -> b
interpT = \case
  MLit x -> fromBool x
  MJoin l r -> l `join` r
  MMeet l r -> l `meet` r

interp :: Boolean b => Free (MultF Bool) b -> b
interp = iter interpT

------------------------------------- ROWS -------------------------------------

type EntryKey = String

data RowF e r
  = REmpty ProperKind
  | REntry EntryKey e
  | RJoin r r
  deriving (Generic, Generic1)
  deriving (Functor, Eq1, Show1) via (Ap2 RowF e)
  deriving (Eq, Show) via (Ap2 RowF e r)

instance Hashable e => Hashable1 (RowF e)

instance (Hashable e, Hashable r) => Hashable (RowF e r)

instance Bifunctor RowF where
  bimap f g = \case
    REmpty k -> REmpty k
    REntry k v -> REntry k (f v)
    RJoin l r -> RJoin (g l) (g r)

instance Eq2 RowF where
  liftEq2 f g l r = case (l, r) of
    (REmpty k, REmpty k') -> k == k'
    (REntry k v, REntry k' v') -> k == k' && f v v'
    (RJoin l r, RJoin l' r') -> g l l' && g r r'
    _ -> False

instance Show2 RowF where
  liftShowsPrec2 ia _ ib _ i = \case
    REmpty k -> appConst showsPrec "{/}" i k
    REntry k v ->
      showParen (i > colon_prec) $
        showString k . showString ": " . ia (colon_prec + 1) v
    RJoin l r ->
      showParen (i > join_prec) $
        ib join_prec l . showString " \\/ " . ib join_prec r
    where
      colon_prec = 4
      join_prec = 5

type RowTerm t = Free (RowF t)

------------------------------------- DATA -------------------------------------

data Connective = CAnd | CWith | COr deriving (Eq, Show, Generic)

instance Hashable Connective

data DataF n a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective (RowTerm a n)
  deriving (Generic)
  deriving (Functor, Eq1, Show1) via (Ap2 DataF n)
  deriving (Eq, Show) via (Ap2 DataF n a)

instance (Hashable n, Hashable a) => Hashable (DataF n a)

instance Bifunctor DataF where
  bimap f g = \case
    PArrow d c -> PArrow (g d) (g c)
    PForall k t -> PForall k (g t)
    PSpread c r -> PSpread c (bimapFree g f r)

instance Eq2 DataF where
  liftEq2 f g l r = case (l, r) of
    (PArrow c d, PArrow c' d') -> g c c' && g d d'
    (PForall k t, PForall k' t') -> k == k' && g t t'
    (PSpread c r, PSpread c' r') -> c == c' && liftEq2Free g f r r'
    _ -> False

instance Show2 DataF where
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
    PSpread c r -> parens (braces c) $ liftShowsPrec2Free ib ia la i r
    where
      arr_prec = 6
      braces = \case
        CAnd -> ("{", "}")
        CWith -> ("[", "]")
        COr -> ("(|", "|)")

type DataTerm n a = Bifree (TypeF n) (DataF n) a a

------------------------------------- TYPE -------------------------------------

data TypeF n a = TLit
  { tyPos :: Position,
    tyPre :: a,
    tyMul :: MultTerm n
  }
  deriving (Generic, Generic1)
  deriving (Functor, Eq1, Show1) via (Ap2 TypeF n)
  deriving (Eq, Show) via (Ap2 TypeF n a)

instance Hashable n => Hashable1 (TypeF n)

instance (Hashable n, Hashable a) => Hashable (TypeF n a)

instance Bifunctor TypeF where
  bimap f g (TLit p q m) = TLit p (g q) (fmap f m)

instance Eq2 TypeF where
  liftEq2 f g (TLit p q m) (TLit p' q' m') = p == p' && g q q' && liftEq f m m'

instance Show2 TypeF where
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

type TypeTerm n a = Bifree (DataF n) (TypeF n) a a

------------------------------------ LAMBDA ------------------------------------

data LambdaF a
  = LVar Int
  | LApp Position a a
  | LAbs ProperKind a
  | LSPair a a
  | LPair a a
  | LFst Position a
  | LSnd Position a
  | LPre Position a
  | LMul Position a
  | LFix SimpleKind a
  | LMap Position a a
  deriving (Functor, Generic, Generic1)
  deriving (Eq, Show) via (Ap LambdaF a)

instance Hashable1 LambdaF

instance Hashable a => Hashable (LambdaF a)

instance Eq1 LambdaF where
  liftEq f l r = case (l, r) of
    (LVar x, LVar y) -> x == y
    (LApp p g x, LApp q h y) -> p == q && f g h && f x y
    (LAbs k t, LAbs l u) -> k == l && f t u
    (LSPair s t, LSPair u v) -> f s u && f t v
    (LPair s t, LPair u v) -> f s u && f t v
    (LFst p t, LFst q u) -> p == q && f t u
    (LSnd p t, LSnd q u) -> p == q && f t u
    (LPre p t, LPre q u) -> p == q && f t u
    (LMul p t, LMul q u) -> p == q && f t u
    (LFix k t, LFix l u) -> k == l && f t u
    (LMap p g x, LMap q h y) -> p == q && f g h && f x y
    _ -> False

instance Show1 LambdaF where
  liftShowsPrec ia la i = \case
    LVar x -> showsPrec i x
    LApp p f x ->
      showParen (i > app_prec) $
        showsPrec (app_prec + 1) p
          . showString " "
          . ia app_prec f
          . showString " "
          . ia (app_prec + 1) x
    LAbs k t ->
      showParen (i > abs_prec) $
        showString "\\:: " . showsPrec (abs_prec + 1) k . ia abs_prec t
    LSPair l r -> parens ("<", ">") $ ia 0 l . showString ", " . ia 0 r
    LPair l r -> parens ("<", ">") $ ia 0 l . showString ", " . ia 0 r
    LFst p t -> app_const "fst" p t
    LSnd p t -> app_const "snd" p t
    LPre p t -> app_const "pre" p t
    LMul p t -> app_const "mul" p t
    LFix k t ->
      showParen (i > abs_prec) $
        showString "μ:: " . showsPrec (abs_prec + 1) k . ia abs_prec t
    LMap p f x ->
      showParen (i > map_prec) $
        showsPrec (map_prec + 1) p
          . ia (map_prec + 1) f
          . showString " @ "
          . ia map_prec x
    where
      app_prec = 10
      abs_prec = 0
      map_prec = 6
      app_const s p t = showsPrec (app_prec + 1) p . appConst ia s i t

type LambdaTerm = Free LambdaF

--------------------------------- GENERIC TERM ---------------------------------

data TermF a
  = TLam (LambdaTerm a)
  | TType (TypeTerm a a)
  | TData (DataTerm a a)
  | TRow (RowTerm a a)
  | TMul (MultTerm a)
  deriving (Eq, Generic)
  deriving (Show) via (Ap TermF a)

instance Hashable a => Hashable (TermF a)

instance Functor TermF where
  fmap f = \case
    TLam t -> TLam (fmap f t)
    TType t -> TType (bibimap f f t)
    TData t -> TData (bibimap f f t)
    TRow t -> TRow (bimapFree f f t)
    TMul t -> TMul (fmap f t)

instance Show1 TermF where
  liftShowsPrec ia la i = \case
    TLam t -> liftShowsPrec ia la i t
    TType t -> liftShowsPrec2Bifree ia ia ia la ia la i t
    TData t -> liftShowsPrec2Bifree ia ia ia la ia la i t
    TRow t -> liftShowsPrec2Free ia ia la i t
    TMul t -> liftShowsPrec ia la i t

type Term = Fix TermF

---------------------------------- SHOW UTILS ----------------------------------

parens :: (String, String) -> ShowS -> ShowS
parens (l, r) s = showString l . s . showString r

appConst :: (Int -> a -> ShowS) -> String -> Int -> a -> ShowS
appConst p s i t = showParen (i > 10) $ showString s . showString " " . p 11 t
