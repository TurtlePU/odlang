{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Core.Term.Syntax where

import Core.Type
import Data.Array.ST (MArray (newArray), readArray, runSTArray, writeArray)
import Data.Array.Unboxed (Array)
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Either (partitionEithers)
import Data.Foldable (for_)

------------------------------ CONTEXT SPLITTING -------------------------------

data Direction2 = DLeft | DRight

direct :: Direction2 -> a -> Either a a
direct = \case
  DLeft -> Left
  DRight -> Right

type Split2 = [Direction2]

(!!!) :: [a] -> Split2 -> ([a], [a])
xs !!! ss = partitionEithers $ zipWith direct ss xs

type SplitN = [Int]

(!*!) :: [a] -> SplitN -> Array Int [a]
xs !*! ss = runSTArray $ do
  arr <- newArray (0, maximum ss) []
  for_ (reverse $ zip xs ss) $ \(x, i) -> do
    xs <- readArray arr i
    writeArray arr i (x : xs)
  pure arr

newtype Refinement = Refine [Int]

(***) :: [a] -> Refinement -> [a]
xs *** Refine rs = concat $ zipWith replicate rs xs

------------------------------------ ROWBAG ------------------------------------

newtype RowBag a = MkBag (Array Int (RowKey, a))
  deriving (Functor, Foldable, Traversable)

------------------------------------ TERMS -------------------------------------

data TermF tled term
  = TVar
  | TAbs
      { argTy :: tled,
        argCnt :: Int,
        absBody :: term,
        absMult :: tled
      }
  | TApp
      { appFun :: term,
        appSplit :: Split2,
        appArg :: term
      }
  | TGen
      { argKi :: Kind,
        genBody :: term,
        genMult :: tled
      }
  | TInst
      { instFun :: term,
        instArg :: tled
      }
  | TAndI
      { andBag :: RowBag term,
        andSplit :: SplitN,
        andMult :: tled
      }
  | TAndE
      { letArg :: term,
        letOrd :: [RowKey],
        letSplit :: Split2,
        letBody :: term
      }
  | TWithI
      { withBag :: RowBag (Refinement, term),
        withMult :: tled
      }
  | TWithE
      { punArg :: term,
        punKey :: RowKey
      }
  | TOrI
      { orKey :: RowKey,
        orValue :: term,
        orRow :: tled,
        orMult :: tled
      }
  | TOrE
      { casesArg :: term,
        casesSplit :: Split2,
        cases :: RowBag (Refinement, term)
      }

instance Bifunctor TermF where
  bimap f g = \case
    TVar -> TVar
    TAbs {..} ->
      TAbs {argTy = f argTy, absBody = g absBody, absMult = f absMult, ..}
    TApp {..} -> TApp {appFun = g appFun, appArg = g appArg, ..}
    TGen {..} -> TGen {genBody = g genBody, genMult = f genMult, ..}
    TInst {..} -> TInst {instFun = g instFun, instArg = f instArg}
    TAndI {..} -> TAndI {andBag = fmap g andBag, andMult = f andMult, ..}
    TAndE {..} -> TAndE {letArg = g letArg, letBody = g letBody, ..}
    TWithI {..} ->
      TWithI {withBag = fmap (second g) withBag, withMult = f withMult}
    TWithE {..} -> TWithE {punArg = g punArg, ..}
    TOrI {..} ->
      TOrI {orValue = g orValue, orRow = f orRow, orMult = f orMult, ..}
    TOrE {..} -> TOrE {casesArg = g casesArg, cases = fmap (second g) cases, ..}

instance Bifoldable TermF where
  bifoldMap f g = \case
    TVar -> mempty
    TAbs t _ b m -> f t <> g b <> f m
    TApp h _ x -> g h <> g x
    TGen _ b m -> g b <> f m
    TInst h a -> g h <> f a
    TAndI b _ m -> foldMap g b <> f m
    TAndE a _ _ b -> g a <> g b
    TWithI b m -> foldMap (g . snd) b <> f m
    TWithE w _ -> g w
    TOrI _ v r m -> g v <> f r <> f m
    TOrE o _ c -> g o <> foldMap (g . snd) c

instance Bitraversable TermF where
  bitraverse f g = \case
    TVar -> pure TVar
    TAbs t c b m -> TAbs <$> f t <*> pure c <*> g b <*> f m
    TApp h s x -> TApp <$> g h <*> pure s <*> g x
    TGen k b m -> TGen k <$> g b <*> f m
    TInst h a -> TInst <$> g h <*> f a
    TAndI b s m -> TAndI <$> traverse g b <*> pure s <*> f m
    TAndE a o s b -> TAndE <$> g a <*> pure o <*> pure s <*> g b
    TWithI b m -> TWithI <$> traverse (traverse g) b <*> f m
    TWithE w k -> TWithE <$> g w <*> pure k
    TOrI k v r m -> TOrI k <$> g v <*> f r <*> f m
    TOrE o s c -> TOrE <$> g o <*> pure s <*> traverse (traverse g) c
