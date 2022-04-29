{-# LANGUAGE DeriveTraversable #-}

module Core.Term where

import Control.Arrow ((>>>))
import Control.Monad (forM_, zipWithM)
import Core.Kind
import Core.TypeLevel
import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe)
import Position
import Result

data RowKey

newtype IndexedBag k v = IBag [(k, v)]
  deriving (Show, Functor, Foldable, Traversable)

type RowBag = IndexedBag RowKey

withValues :: Functor f => ([v] -> f [v']) -> IndexedBag k v -> f (IndexedBag k v')
withValues g (IBag kv) = IBag . zip (fst <$> kv) <$> g (snd <$> kv)

data Direction = DLeft | DRight

direct :: Direction -> a -> Either a a
direct DLeft = Left
direct DRight = Right

type Split = [Direction]

(!!!) :: [a] -> Split -> ([a], [a])
xs !!! s = partitionEithers $ zipWith direct s xs

type SplitN = [Int]

(!*!) :: [a] -> SplitN -> [[a]] -- list of contexts
xs !*! s = elems $ foldr putAt mempty $ zip xs s
  where
    putAt = uncurry $ \x -> alter ((x :) . fromMaybe mempty)

type Row = Positioned TLTerm

data Term t
  = TVar
  | TAbs Int Type t Mult
  | TApp Split t t
  | TGen ProperKind t Mult
  | TInst t (Positioned TLTerm)
  | TAndI SplitN (RowBag t) Mult
  | TAndE Split t [RowKey] t
  | TWithI (RowBag t) Mult
  | TWithE t RowKey
  | TOrI RowKey t Row Mult
  | TOrE Split t (RowBag t)

data TypingError
  = Kinding KindingError

type TypingErrors = NonEmpty TypingError

type TypingResult = CtxResult ([ProperKind], [Type]) TypingErrors

synthesizeType :: Positioned Term -> TypingResult Type
synthesizeType (Posed _ TVar) = CtxR $ \(_, [ty]) -> pure ty
synthesizeType (Posed p (TAbs n ty tm mul)) = do
  isType ty
  getCtx >>= checkSup' mul
  checkSup' (upperBound' p n) [ty]
  Posed p . KPretype . PArrow ty
    <$> modifyCtx (replicate n ty ++) (synthesizeType tm)
synthesizeType (Posed _ (TApp s f x)) = do
  (tyf, tyx) <- splitCtx s (synthesizeType f) $ pairM (synthesizeType x)
  (tyarg, tyres) <- pullArrow tyf
  checkTyEq tyarg tyx
  pure tyres
synthesizeType (Posed p (TGen k tm mul)) = do
  getCtx >>= checkSup' mul
  Posed p . KPretype . PForall k <$> shiftCtx k (synthesizeType tm)
  where
    shiftCtx k = mapCtx $ bimap (k :) $ fmap $ flip shiftTLTerm 1
synthesizeType (Posed p (TInst tm arg)) = do
  (k, ty) <- synthesizeType tm >>= pullForall
  fromKinding $ checkKind k arg
  pure $ substTLTerm ty 0 arg
synthesizeType (Posed p (TAndI s rs mul)) = do
  tys <- withValues (splitCtxN s . fmap synthesizeType) rs
  checkSup' mul tys
  pure $ mkAlgebraic CAnd p tys
synthesizeType (Posed p (TAndE s tup order tm)) =
  splitCtx s (synthesizeType tup) $ \tytup -> do
    addend <- reorder tytup order
    modifyCtx (addend ++) (synthesizeType tm)
synthesizeType (Posed p (TWithI rs mul)) = do
  tys <- traverse synthesizeType rs
  checkSup' mul tys
  pure $ mkAlgebraic CWith p tys
synthesizeType (Posed p (TWithE tm key)) = do
  ty <- synthesizeType tm
  pickTy key ty
synthesizeType (Posed p (TOrI key tm row mul)) = _
synthesizeType (Posed p (TOrE s tm rs)) = _

pairM :: Monad m => m b -> a -> m (a, b)
pairM b = flip fmap b . (,)

mkAlgebraic :: Connective -> Position -> IndexedBag RowKey Type -> Type
mkAlgebraic c p = Posed p . KPretype . PSpread c . Posed p . KRow . _

splitCtx :: Split -> TypingResult a -> (a -> TypingResult b) -> TypingResult b
splitCtx s ra rb = CtxR $ \(ks, tys) ->
  let (tya, tyb) = tys !!! s
   in withCtx' ks tya ra >>= withCtx' ks tyb . rb

splitCtxN :: SplitN -> [TypingResult a] -> TypingResult [a]
splitCtxN s rs = CtxR $ \(ks, tys) -> zipWithM (withCtx' ks) (tys !*! s) rs

withCtx' :: [ProperKind] -> [Type] -> TypingResult a -> Result TypingErrors a
withCtx' = curry $ flip withCtx

getCtx :: TypingResult [Type]
getCtx = CtxR $ pure . snd

modifyCtx :: ([Type] -> [Type]) -> TypingResult a -> TypingResult a
modifyCtx f = mapCtx $ second f

isType :: Type -> TypingResult ()
isType = fromKinding . checkKind (Simple Type)

checkSup' :: Foldable f => Mult -> f Type -> TypingResult ()
checkSup' m = fromKinding . checkSup m

fromKinding :: KindingResult a -> TypingResult a
fromKinding = first (fmap Kinding) . mapCtx fst

reorder :: Type -> [RowKey] -> TypingResult [Type]
reorder = _

pullArrow :: Type -> TypingResult (Type, Type)
pullArrow = _

pullForall :: Type -> TypingResult (ProperKind, Type)
pullForall = _

checkTyEq :: Type -> Type -> TypingResult ()
checkTyEq = _
