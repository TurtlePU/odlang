{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}

module Core.Type.Syntax where

import Algebra.Lattice (BoundedLattice, Lattice (..), fromBool)
import Control.Monad.FreeBi (FreeBi, iter)
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Ap2 (Ap2 (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Fix (Fix)
import Data.Functor.Ap (Ap (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Functor.Identity (Identity)
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1 (..), Hashable2 (..))
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances
import GHC.Generics (Generic, Generic1)

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
  deriving (Generic, Generic1)
  deriving (Functor, Foldable, Eq1, Show1) via (Ap2 MultF l)
  deriving (Eq, Show, Hashable) via (Ap2 MultF l a)

instance Hashable l => Hashable1 (MultF l)

instance Hashable2 MultF where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt hb s $ first (mkReflected p) x

instance Bifunctor MultF where
  bimap f g = \case
    MLit b -> MLit (f b)
    MJoin l r -> MJoin (g l) (g r)
    MMeet l r -> MMeet (g l) (g r)

instance Bifoldable MultF where
  bifoldMap f g = \case
    MLit b -> f b
    MJoin l r -> g l <> g r
    MMeet l r -> g l <> g r

instance Bitraversable MultF where
  bitraverse f g = \case
    MLit b -> MLit <$> f b
    MJoin l r -> MJoin <$> g l <*> g r
    MMeet l r -> MMeet <$> g l <*> g r

instance Traversable (MultF l) where
  traverse = bitraverse pure

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

type MultTerm = FreeBi MultF MultLit

evalM :: BoundedLattice b => (a -> b) -> FreeBi MultF Bool a -> b
evalM f = iter interpT . fmap f
  where
    interpT = \case
      MLit x -> fromBool x
      MJoin l r -> l \/ r
      MMeet l r -> l /\ r

------------------------------------- ROWS -------------------------------------

data RowF e r
  = REmpty ProperKind
  | REntry e
  | RJoin r r
  deriving (Generic, Generic1)
  deriving (Functor, Foldable, Eq1, Show1) via (Ap2 RowF e)
  deriving (Eq, Show, Hashable) via (Ap2 RowF e r)

instance Hashable e => Hashable1 (RowF e)

instance Hashable2 RowF where
  liftHashWithSalt2 ha hb s x = reify (ReifiedHashable ha) $ \p ->
    liftHashWithSalt hb s $ first (mkReflected p) x

instance Bifunctor RowF where
  bimap f g = \case
    REmpty k -> REmpty k
    REntry v -> REntry (f v)
    RJoin l r -> RJoin (g l) (g r)

instance Bifoldable RowF where
  bifoldMap f g = \case
    REmpty _ -> mempty
    REntry v -> f v
    RJoin l r -> g l <> g r

instance Bitraversable RowF where
  bitraverse f g = \case
    REmpty k -> pure (REmpty k)
    REntry v -> REntry <$> f v
    RJoin l r -> RJoin <$> g l <*> g r

instance Traversable (RowF e) where
  traverse = bitraverse pure

instance Eq2 RowF where
  liftEq2 f g l r = case (l, r) of
    (REmpty k, REmpty k') -> k == k'
    (REntry v, REntry v') -> f v v'
    (RJoin l r, RJoin l' r') -> g l l' && g r r'
    _ -> False

instance Show2 RowF where
  liftShowsPrec2 ia _ ib _ i = \case
    REmpty k -> appConst showsPrec "{/}" i k
    REntry v -> showParen (i > colon_prec) $ ia (colon_prec + 1) v
    RJoin l r ->
      showParen (i > join_prec) $
        ib join_prec l . showString " \\/ " . ib join_prec r
    where
      colon_prec = 4
      join_prec = 5

type EntryKey = String

type RowTerm = Biff (FreeBi RowF) ((,) EntryKey) Identity

------------------------------------- DATA -------------------------------------

data Connective = CAnd | CWith | COr deriving (Eq, Show, Generic)

instance Hashable Connective

data DataF a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective a
  deriving (Generic, Generic1, Functor, Foldable, Traversable)
  deriving (Eq, Show, Hashable) via (Ap DataF a)

instance Hashable1 DataF

instance Eq1 DataF where
  liftEq f l r = case (l, r) of
    (PArrow c d, PArrow c' d') -> f c c' && f d d'
    (PForall k t, PForall k' t') -> k == k' && f t t'
    (PSpread c r, PSpread c' r') -> c == c' && f r r'
    _ -> False

instance Show1 DataF where
  liftShowsPrec ia la i = \case
    PArrow c d ->
      showParen (i > arr_prec) $
        ia (arr_prec + 1) c . showString " -> " . ia (arr_prec + 1) d
    PForall k t ->
      showParen (i > arr_prec) $
        showString "∀ "
          . showsPrec (arr_prec + 1) k
          . showString ". "
          . ia (arr_prec + 1) t
    PSpread c r -> parens (braces c) $ ia 0 r
    where
      arr_prec = 6
      braces = \case
        CAnd -> ("{", "}")
        CWith -> ("[", "]")
        COr -> ("(|", "|)")

------------------------------------- TYPE -------------------------------------

data TypeF a = TLit {tyDat :: a, tyMul :: a}
  deriving (Generic, Generic1, Functor, Foldable, Traversable)
  deriving (Eq, Show, Hashable) via (Ap TypeF a)

instance Hashable1 TypeF

instance Eq1 TypeF where
  liftEq f (TLit d m) (TLit d' m') = f d d' && f m m'

instance Show1 TypeF where
  liftShowsPrec ia la i (TLit q m) =
    showParen (i > 0) $
      showString " "
        . ia (app_prec + 1) q
        . showString " % "
        . ia (mod_prec + 1) m
    where
      app_prec = 10
      mod_prec = 4

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
  deriving (Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Eq, Show, Hashable) via (Ap LambdaF a)

instance Hashable1 LambdaF

instance Eq1 LambdaF where
  liftEq f l r = case (l, r) of
    (LVar x, LVar y) -> x == y
    (LApp p g x, LApp q h y) -> p == q && f g h && f x y
    (LAbs k t, LAbs l u) -> k == l && f t u
    (LSPair p s t, LSPair q u v) -> p == q && f s u && f t v
    (LPair s t, LPair u v) -> f s u && f t v
    (LFst p t, LFst q u) -> p == q && f t u
    (LSnd p t, LSnd q u) -> p == q && f t u
    (LDat p t, LDat q u) -> p == q && f t u
    (LMul p t, LMul q u) -> p == q && f t u
    (LFix p k t, LFix q l u) -> p == q && k == l && f t u
    (LMap p g x, LMap q h y) -> p == q && f g h && f x y
    (LRnd p t, LRnd q u) -> p == q && f t u
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
    LSPair p l r ->
      showsPrec i p . parens ("<", ">") (ia 0 l . showString ", " . ia 0 r)
    LPair l r -> parens ("<", ">") $ ia 0 l . showString ", " . ia 0 r
    LFst p t -> app_const "fst" p t
    LSnd p t -> app_const "snd" p t
    LDat p t -> app_const "dat" p t
    LMul p t -> app_const "mul" p t
    LFix p k t ->
      showParen (i > abs_prec) $
        showsPrec (abs_prec + 1) p
          . showString "μ:: "
          . showsPrec (abs_prec + 1) k
          . ia abs_prec t
    LMap p f x ->
      showParen (i > map_prec) $
        showsPrec (map_prec + 1) p
          . ia (map_prec + 1) f
          . showString " @ "
          . ia map_prec x
    LRnd p t ->
      showParen (i > app_prec) $
        showsPrec (app_prec + 1) p . parens (" ⌊", "⌋") (ia abs_prec t)
    where
      app_prec = 10
      abs_prec = 0
      map_prec = 6
      app_const s p t = showsPrec (app_prec + 1) p . appConst ia s i t

--------------------------------- GENERIC TERM ---------------------------------

data TermF a
  = TLam (LambdaF a)
  | TType Position (TypeF a)
  | TData Position (DataF a)
  | TRow Position (Join RowTerm a)
  | TMul Position (MultTerm a)
  deriving (Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Show, Eq, Hashable) via (Ap TermF a)

instance Hashable2 f => Hashable1 (Join f) where
  liftHashWithSalt ha s (Join x) = liftHashWithSalt2 ha ha s x

instance (Hashable2 p, Hashable1 f, Hashable1 g) => Hashable2 (Biff p f g) where
  liftHashWithSalt2 ha hb s (Biff t) =
    liftHashWithSalt2 (liftHashWithSalt ha) (liftHashWithSalt hb) s t

instance Hashable1 TermF

instance Eq1 TermF where
  liftEq f l r = case (l, r) of
    (TLam l, TLam r) -> liftEq f l r
    (TType p l, TType q r) -> p == q && liftEq f l r
    (TData p l, TData q r) -> p == q && liftEq f l r
    (TRow p l, TRow q r) -> p == q && liftEq f l r
    (TMul p l, TMul q r) -> p == q && liftEq f l r
    _ -> False

instance Show1 TermF where
  liftShowsPrec ia la i = \case
    TLam t -> liftShowsPrec ia la i t
    TType p t -> showsPrec i p . liftShowsPrec ia la i t
    TData p t -> showsPrec i p . liftShowsPrec ia la i t
    TRow p t -> showsPrec i p . liftShowsPrec ia la i t
    TMul p t -> showsPrec i p . liftShowsPrec ia la i t

type Term = Fix TermF

---------------------------------- SHOW UTILS ----------------------------------

parens :: (String, String) -> ShowS -> ShowS
parens (l, r) s = showString l . s . showString r

appConst :: (Int -> a -> ShowS) -> String -> Int -> a -> ShowS
appConst p s i t = showParen (i > 10) $ showString s . showString " " . p 11 t
