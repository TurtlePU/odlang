{-# LANGUAGE LambdaCase #-}

module Core.Type.Kinding where

import Control.Applicative (Applicative (liftA2))
import Control.Composition (on, (.@))
import Control.Monad.FreeBi (iterA)
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Result (Result (..), failWith, mapCtx)
import Core.Type.Result (TypeResult)
import Core.Type.Syntax
import Data.Bifunctor.Biff (Biff (Biff))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (foldFix)
import Data.Foldable (for_)
import Data.Functor (($>))
import Data.Functor.Identity (Identity (..))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Position (Position)

data Expected
  = EKind ProperKind
  | EOperator
  | EPair
  | ERow
  | ESimple
  deriving (Show, Eq)

data KindingError
  = KMismatch ProperKind Expected Position
  | KDifferentRows (NonEmpty ProperKind) Position
  deriving (Show, Eq)

type KindingResult = TypeResult KindingError

checkKind :: ProperKind -> Term -> Position -> KindingResult ()
checkKind = synthesizeKind .@ intoCheck

synthesizeKind :: Term -> KindingResult ProperKind
synthesizeKind = foldFix $ \case
  TLam t -> case t of
    LVar i -> ReaderT $ Ok . (!! i)
    LApp f x p -> do
      (kx, ky) <- f >>= flip pullArrow p
      intoCheck kx x p
      pure ky
    LAbs k t -> (k :->:) <$> mapCtx (k :) t
    LSPair l r p -> Simple <$> on (liftA2 (:*:)) (>>= flip pullSimple p) l r
    LPair l r -> liftA2 (:**:) l r
    LFst t p -> fst <$> (t >>= flip pullPair p)
    LSnd t p -> snd <$> (t >>= flip pullPair p)
    LDat t p -> intoCheck Type t p $> Simple Data
    LMul t p -> intoCheck Type t p $> Mult
    LFix k t p -> intoAssert (Simple k) (mapCtx (Simple k :) t) p
    LMap f x p -> do
      (kx, ky) <- f >>= flip pullArrow p
      intoCheck (Row kx) x p
      pure (Row ky)
    LRnd t p -> t >>= flip pullRow p
  TMul m p -> for_ m (flip (intoCheck Mult) p) $> Mult
  TRow (Join (Biff x)) p -> do
    ks <- sequenceA (iterA fold $ fmap runIdentity x)
    case NonEmpty.nub ks of
      Row k :| [] -> pure (Row k)
      k :| [] -> failWith $ KMismatch k ERow p
      ks -> failWith $ KDifferentRows ks p
    where
      fold = \case
        REmpty k -> pure . pure $ Row k
        REntry (_, v) -> pure $ Row <$> v
        RJoin l r -> l <> r
  TType (TLit d m) p ->
    intoCheck (Simple Data) d p *> intoCheck Mult m p $> Type
  TData t p -> case t of
    PArrow d c -> intoCheck Type d p *> intoCheck Type c p $> Simple Data
    PForall k t -> mapCtx (k :) (intoCheck Type t p) $> Simple Data
    PSpread _ r -> intoCheck (Row Type) r p $> Simple Data
  where
    intoAssert k k' p = intoCheck k k' p $> k

    pullSimple = \case
      Simple k -> const $ pure k
      k' -> failWith . KMismatch k' ESimple

    pullPair = \case
      Simple (k :*: k') -> const $ pure (Simple k, Simple k')
      (k :**: k') -> const $ pure (k, k')
      k' -> failWith . KMismatch k' EPair

intoCheck ::
  ProperKind -> KindingResult ProperKind -> Position -> KindingResult ()
intoCheck k mk p = do
  k' <- mk
  if k == k'
    then pure ()
    else failWith $ KMismatch k' (EKind k) p

pullRow :: ProperKind -> Position -> KindingResult ProperKind
pullRow = \case
  Row k -> const $ pure k
  k' -> failWith . KMismatch k' ERow

pullArrow :: ProperKind -> Position -> KindingResult (ProperKind, ProperKind)
pullArrow = \case
  (k :->: k') -> const $ pure (k, k')
  k' -> failWith . KMismatch k' EOperator
