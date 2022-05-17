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

synthesizeKind :: Term -> KindingResult ProperKind
synthesizeKind = foldFix $ \case
  TLam t -> flip iter t $ \case
    LVar i -> CtxR $ Ok . (!! i)
    LApp p f x -> do
      (kx, ky) <- f >>= pullArrow p
      x >>= intoCheck p kx
      pure ky
    LAbs k t -> (k :->:) <$> mapCtx (k :) t
    LSPair p l r ->
      Simple <$> liftA2 (:*:) (l >>= pullSimple p) (r >>= pullSimple p)
    LPair l r -> liftA2 (:**:) l r
    LFst p t -> fst <$> (t >>= pullPair p)
    LSnd p t -> snd <$> (t >>= pullPair p)
    LDat p t -> (t >>= intoCheck p Type) $> Simple Data
    LMul p t -> (t >>= intoCheck p Type) $> Mult
    LFix p k t -> mapCtx (Simple k :) t >>= intoAssert p (Simple k)
    LMap p f x -> do
      (kx, ky) <- f >>= pullArrow p
      x >>= intoCheck p (Row kx)
      pure (Row ky)
  TMul p m -> synthesizeMultKind p m
  TRow p (Join x) -> synthesizeRowKind p x
  TType p (Join x) -> tyiter synthesizeDataKind synthesizeTypeKind x p
  TData p (Join x) -> tyiter synthesizeTypeKind synthesizeDataKind x p
  where
    tyiter f g = biiter f g . bimap const const

    synthesizeMultKind p m = for_ m (>>= intoCheck p Mult) $> Mult

    synthesizeTypeKind (TLit q d m) _ =
      (d q >>= intoCheck q (Simple Data))
        *> synthesizeMultKind q (fmap ($ q) m)
        $> Type

    synthesizeDataKind t p = case t of
      PArrow d c ->
        (d p >>= intoCheck p Type) *> (c p >>= intoCheck p Type) $> Simple Data
      PForall k t -> mapCtx (k :) (t p >>= intoCheck p Type) $> Simple Data
      PSpread _ r ->
        (synthesizeRowKind p (bimap ($ p) ($ p) r) >>= intoCheck p (Row Type))
          $> Simple Data

    synthesizeRowKind p x = do
      ks <- sequenceA (iterA fold x)
      case NonEmpty.nub ks of
        Row k :| [] -> pure (Row k)
        k :| [] -> failWith $ KMismatch p k ERow
        ks -> failWith $ KDifferentRows p ks

    fold = \case
      REmpty k -> pure $ pure $ Row k
      REntry _ v -> pure $ Row <$> v
      RJoin l r -> l <> r

    intoCheck p k k' =
      if k == k'
        then pure ()
        else failWith $ KMismatch p k' $ EKind k

    intoAssert p k k' = intoCheck p k k' $> k

    pullSimple p = \case
      Simple k -> pure k
      k' -> failWith $ KMismatch p k' ESimple

    pullPair p = \case
      Simple (k :*: k') -> pure (Simple k, Simple k')
      (k :**: k') -> pure (k, k')
      k' -> failWith $ KMismatch p k' EPair

pullArrow :: Position -> ProperKind -> KindingResult (ProperKind, ProperKind)
pullArrow p = \case
  (k :->: k') -> pure (k, k')
  k' -> failWith $ KMismatch p k' EOperator

failWith e = CtxR $ const $ Err $ pure e
