{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

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

type RowBag = IndexedBag RowKey Term

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

type Row = TLTerm

data Term
  = TVar Position
  | TAbs Position Int Type Term Mult
  | TApp Position Split Term Term
  | TGen Position ProperKind Term Mult
  | TInst Position Term TLTerm
  | TAndI Position SplitN RowBag Mult
  | TAndE Position Split Term [RowKey] Term
  | TWithI Position RowBag Mult
  | TWithE Position Term RowKey
  | TOrI Position RowKey Term Row Mult
  | TOrE Position Split Term RowBag

data TypingError
  = Kinding KindingError

type TypingErrors = NonEmpty TypingError

type TypingResult = CtxResult ([ProperKind], [Type]) TypingErrors

synthesizeType :: Term -> TypingResult Type
synthesizeType (TVar _) = CtxR $ \(_, [ty]) -> pure ty
synthesizeType (TAbs p n ty tm mul) = do
  isType ty
  getCtx >>= checkSup' mul
  checkSup' (upperBound' p n) [ty]
  KPretype p . PArrow ty <$> modifyCtx (replicate n ty ++) (synthesizeType tm)
synthesizeType (TApp _ s f x) = do
  (tyf, tyx) <- splitCtx s (synthesizeType f) $ pairM (synthesizeType x)
  (tyarg, tyres) <- pullArrow tyf
  checkTyEq tyarg tyx
  pure tyres
synthesizeType (TGen p k tm mul) = do
  getCtx >>= checkSup' mul
  KPretype p . PForall k <$> shiftCtx k (synthesizeType tm)
  where
    shiftCtx k = mapCtx $ bimap (k :) $ fmap $ flip shiftTLTerm 1
synthesizeType (TInst p tm arg) = do
  (k, ty) <- synthesizeType tm >>= pullForall
  fromKinding $ checkKind k arg
  pure $ substTLTerm ty 0 arg
synthesizeType (TAndI p s rs mul) = do
  tys <- withValues (splitCtxN s . fmap synthesizeType) rs
  checkSup' mul tys
  pure $ mkAlgebraic CAnd p tys
synthesizeType (TAndE p s tup order tm) =
  splitCtx s (synthesizeType tup) $ \tytup -> do
    addend <- reorder tytup order
    modifyCtx (addend ++) (synthesizeType tm)
synthesizeType (TWithI p rs mul) = do
  tys <- traverse synthesizeType rs
  checkSup' mul tys
  pure $ mkAlgebraic CWith p tys
synthesizeType (TWithE p tm key) = do
  ty <- synthesizeType tm
  pickTy key ty
synthesizeType (TOrI p key tm row mul) = _
synthesizeType (TOrE p s tm rs) = _

pairM :: Monad m => m b -> a -> m (a, b)
pairM b = flip fmap b . (,)

mkAlgebraic :: Connective -> Position -> IndexedBag RowKey Type -> Type
mkAlgebraic c p = KPretype p . PSpread c . KRow p . _

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
