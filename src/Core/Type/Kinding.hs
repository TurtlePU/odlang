{-# LANGUAGE LambdaCase #-}

module Core.Type.Kinding where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.Free (iter)
import Control.Monad.FreeBi (iterA)
import Control.Monad.Quad (biiter)
import Core.Type.Syntax
import Data.Bifunctor (Bifunctor (bimap))
import Data.Bifunctor.Join (Join (Join))
import Data.Fix (foldFix)
import Data.Foldable (for_)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Position (Position)
import Data.Result

---------------------------------- DATA TYPES ----------------------------------

data Expected
  = EKind ProperKind
  | EOperator
  | EPair
  | ERow
  | ESimple
  deriving (Show)

data KindingError
  = KMismatch Position ProperKind Expected
  | KDifferentRows Position (NonEmpty ProperKind)
  deriving (Show)

type KindingErrors = NonEmpty KindingError

type KindingResult = CtxResult [ProperKind] KindingErrors

---------------------------------- ALGORITHM -----------------------------------

checkKind :: Position -> ProperKind -> Term -> KindingResult ()
checkKind p k t = intoCheck p k $ synthesizeKind t

synthesizeKind :: Term -> KindingResult ProperKind
synthesizeKind = foldFix $ \case
  TLam t -> case t of
    LVar i -> CtxR $ Ok . (!! i)
    LApp p f x -> do
      (kx, ky) <- f >>= pullArrow p
      intoCheck p kx x
      pure ky
    LAbs k t -> (k :->:) <$> mapCtx (k :) t
    LSPair p l r ->
      Simple <$> liftA2 (:*:) (l >>= pullSimple p) (r >>= pullSimple p)
    LPair l r -> liftA2 (:**:) l r
    LFst p t -> fst <$> (t >>= pullPair p)
    LSnd p t -> snd <$> (t >>= pullPair p)
    LDat p t -> intoCheck p Type t $> Simple Data
    LMul p t -> intoCheck p Type t $> Mult
    LFix p k t -> intoAssert p (Simple k) $ mapCtx (Simple k :) t
    LMap p f x -> do
      (kx, ky) <- f >>= pullArrow p
      intoCheck p (Row kx) x
      pure (Row ky)
  TMul p m -> for_ m (intoCheck p Mult) $> Mult
  TRow p (Join x) -> do
    ks <- sequenceA (iterA fold x)
    case NonEmpty.nub ks of
      Row k :| [] -> pure (Row k)
      k :| [] -> failWith $ KMismatch p k ERow
      ks -> failWith $ KDifferentRows p ks
    where
      fold = \case
        REmpty k -> pure $ pure $ Row k
        REntry _ v -> pure $ Row <$> v
        RJoin l r -> l <> r
  TType p (TLit d m) ->
    intoCheck p (Simple Data) d *> intoCheck p Mult m $> Type
  TData p t -> case t of
    PArrow d c -> intoCheck p Type d *> intoCheck p Type c $> Simple Data
    PForall k t -> mapCtx (k :) (intoCheck p Type t) $> Simple Data
    PSpread _ r -> intoCheck p (Row Type) r $> Simple Data
  where
    intoAssert p k k' = intoCheck p k k' $> k

    pullSimple p = \case
      Simple k -> pure k
      k' -> failWith $ KMismatch p k' ESimple

    pullPair p = \case
      Simple (k :*: k') -> pure (Simple k, Simple k')
      (k :**: k') -> pure (k, k')
      k' -> failWith $ KMismatch p k' EPair

intoCheck p k mk = do
  k' <- mk
  if k == k'
    then pure ()
    else failWith $ KMismatch p k' $ EKind k

pullArrow :: Position -> ProperKind -> KindingResult (ProperKind, ProperKind)
pullArrow p = \case
  (k :->: k') -> pure (k, k')
  k' -> failWith $ KMismatch p k' EOperator

failWith = CtxR . const . Err . pure
