{-# LANGUAGE LambdaCase #-}

module Core.Term where

import Core.Type
import Data.Array.ST (MArray (newArray), readArray, runSTArray, writeArray)
import Data.Array.Unboxed (Array)
import Data.Either (partitionEithers)
import Data.Foldable (for_)
import Data.IndexedBag (IndexedBag)

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

------------------------------------ TERMS -------------------------------------

type RowBag = IndexedBag RowKey

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
