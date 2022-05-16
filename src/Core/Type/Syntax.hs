{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}

module Core.Type.Syntax where

import Control.Monad.Free (Free, hoistFree, iter)
import Data.Aps (Ap (..), Ap2 (..))
import Data.Bifree (Bifree, bibimap, liftShowsPrec2Bifree)
import Data.Bifunctor (Bifunctor (..))
import Data.FreeBi (bimapFree, liftEq2Free, liftShowsPrec2Free)
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..))
import Data.Position (Position)

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

data MultF l a
  = MLit l
  | MJoin a a
  | MMeet a a
  deriving (Foldable)
  deriving (Functor, Eq1, Show1) via (Ap2 MultF l)
  deriving (Eq, Show) via (Ap2 MultF l a)

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
  deriving (Show, Eq)

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
  deriving (Functor, Eq1, Show1) via (Ap2 RowF e)
  deriving (Eq, Show) via (Ap2 RowF e r)

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

data Connective = CAnd | CWith | COr deriving (Show, Eq)

data DataF n a
  = PArrow a a
  | PForall ProperKind a
  | PSpread Connective (RowTerm a n)
  deriving (Functor, Eq1, Show1) via (Ap2 DataF n)
  deriving (Eq, Show) via (Ap2 DataF n a)

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
  deriving (Functor, Eq1, Show1) via (Ap2 TypeF n)
  deriving (Eq, Show) via (Ap2 TypeF n a)

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
  | LApp a a
  | LAbs ProperKind a
  | LSPair a a
  | LPair a a
  | LFst a
  | LSnd a
  | LPre a
  | LMul a
  | LFix SimpleKind a
  | LMap a a
  deriving (Functor)
  deriving (Eq, Show) via (Ap LambdaF a)

instance Eq1 LambdaF where
  liftEq f l r = case (l, r) of
    (LVar x, LVar y) -> x == y
    (LApp g x, LApp h y) -> f g h && f x y
    (LAbs k t, LAbs l u) -> k == l && f t u
    (LSPair s t, LSPair u v) -> f s u && f t v
    (LPair s t, LPair u v) -> f s u && f t v
    (LFst t, LFst u) -> f t u
    (LSnd t, LSnd u) -> f t u
    (LPre t, LPre u) -> f t u
    (LMul t, LMul u) -> f t u
    (LFix k t, LFix l u) -> k == l && f t u
    (LMap g x, LMap h y) -> f g h && f x y
    _ -> False

instance Show1 LambdaF where
  liftShowsPrec ia la i = \case
    LVar x -> showsPrec i x
    LApp f x ->
      showParen (i > app_prec) $
        ia app_prec f . showString " " . ia (app_prec + 1) x
    LAbs k t ->
      showParen (i > abs_prec) $
        showString "\\:: " . showsPrec (abs_prec + 1) k . ia abs_prec t
    LSPair l r -> parens ("<", ">") $ ia 0 l . showString ", " . ia 0 r
    LPair l r -> parens ("<", ">") $ ia 0 l . showString ", " . ia 0 r
    LFst t -> app_const "fst" t
    LSnd t -> app_const "snd" t
    LPre t -> app_const "pre" t
    LMul t -> app_const "mul" t
    LFix k t ->
      showParen (i > abs_prec) $
        showString "μ:: " . showsPrec (abs_prec + 1) k . ia abs_prec t
    LMap f x ->
      showParen (i > map_prec) $
        ia (map_prec + 1) f . showString " @ " . ia map_prec x
    where
      app_prec = 10
      abs_prec = 0
      map_prec = 6
      app_const s t = appConst ia s i t

type LambdaTerm = Free LambdaF

--------------------------------- GENERIC TERM ---------------------------------

data TermF a
  = TLam (LambdaTerm a)
  | TType (TypeTerm a a)
  | TData (DataTerm a a)
  | TRow (RowTerm a a)
  | TMul (MultTerm a)
  deriving (Eq)
  deriving (Show) via (Ap TermF a)

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

---------------------------------- SHOW UTILS ----------------------------------

parens :: (String, String) -> ShowS -> ShowS
parens (l, r) s = showString l . s . showString r

appConst :: (Int -> a -> ShowS) -> String -> Int -> a -> ShowS
appConst p s i t = showParen (i > 10) $ showString s . showString " " . p 11 t
