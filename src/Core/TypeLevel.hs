{-# LANGUAGE LambdaCase #-}

module Core.TypeLevel where

import Control.Monad (forM_)
import Core.Kind
import Core.Multiplicity
import Core.Row
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..), nub)
import Position
import Result

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

data TLLambda t
  = LVar Int
  | LApp t t
  | LAbs ProperKind t
  | LSPair t t
  | LPair t t
  | LFst t
  | LSnd t
  | LPre t
  | LMul t
  | LFix SimpleKind t
  | LMap t t
  deriving (Show)

data Connective = CAnd | CWith | COr deriving (Show)

data PreTerm t
  = PArrow t t
  | PForall ProperKind t
  | PSpread Connective t
  deriving (Show)

data TLTerm t
  = KLam (TLLambda t)
  | KMult (MultTerm t)
  | KRow (RowTerm t)
  | KType t t
  | KPretype (PreTerm t)
  deriving (Show)

shiftTLTerm :: Positioned TLTerm -> Int -> Positioned TLTerm
shiftTLTerm = _

substTLTerm :: Positioned TLTerm -> Int -> Positioned TLTerm -> Positioned TLTerm
substTLTerm = _

type KindingResult = CtxResult [ProperKind] KindingErrors

synthesizeKind :: Positioned TLTerm -> KindingResult ProperKind
synthesizeKind (Posed _ (KLam (LVar i))) = CtxR $ Ok . (!! i)
synthesizeKind (Posed p (KLam (LApp f x))) =
  synthesizeKind f >>= \case
    kx :->: ky -> checkKind kx x $> ky
    k -> failWith $ KMismatch p k EOperator
synthesizeKind (Posed _ (KLam (LAbs k t))) =
  (k :->:) <$> mapCtx (k :) (synthesizeKind t)
synthesizeKind (Posed _ (KLam (LSPair l r))) =
  (Simple .) . (:*:) <$> pullSimple l <*> pullSimple r
synthesizeKind (Posed _ (KLam (LPair l r))) =
  (:**:) <$> synthesizeKind l <*> synthesizeKind r
synthesizeKind (Posed p (KLam (LFst t))) =
  synthesizeKind t >>= \case
    kl :**: _ -> pure kl
    Simple (kl :*: _) -> pure $ Simple kl
    k -> failWith $ KMismatch p k EPair
synthesizeKind (Posed p (KLam (LSnd t))) =
  synthesizeKind t >>= \case
    _ :**: kr -> pure kr
    Simple (_ :*: kr) -> pure $ Simple kr
    k -> failWith $ KMismatch p k EPair
synthesizeKind (Posed _ (KLam (LPre t))) =
  checkKind (Simple Type) t $> Simple Pretype
synthesizeKind (Posed _ (KLam (LMul t))) = checkKind (Simple Type) t $> Mult
synthesizeKind (Posed _ (KLam (LFix k t))) =
  mapCtx (Simple k :) (checkKind (Simple k) t) $> Simple k
synthesizeKind (Posed p (KLam (LMap f r))) =
  synthesizeKind f >>= \case
    kx :->: ky -> checkKind (Row kx) r $> Row ky
    k -> failWith $ KMismatch p k EOperator
synthesizeKind (Posed _ (KMult m)) = forM_ m (checkKind Mult) $> Mult
synthesizeKind (Posed p (KRow r)) = do
  ks <- collectK synthesizeKind r
  case nub ks of
    Row k :| [] -> pure (Row k)
    k :| [] -> failWith (KMismatch p k ERow)
    ks -> failWith (KDifferentRows p ks)
synthesizeKind (Posed _ (KType t m)) =
  checkKind (Simple Pretype) t *> checkKind Mult m $> Simple Type
synthesizeKind (Posed _ (KPretype (PArrow f x))) =
  checkKind (Simple Type) f *> checkKind (Simple Type) x $> Simple Pretype
synthesizeKind (Posed _ (KPretype (PForall k f))) =
  mapCtx (k :) (checkKind (Simple Type) f) $> Simple Pretype
synthesizeKind (Posed p (KPretype (PSpread _ r))) =
  synthesizeKind r >>= \case
    Row (Simple Type) -> pure (Simple Pretype)
    k -> failWith $ KMismatch p k $ EKind $ Row $ Simple Type

checkKind :: ProperKind -> Positioned TLTerm -> KindingResult ()
checkKind k t = do
  k' <- synthesizeKind t
  if k == k'
    then pure ()
    else failWith $ KMismatch (pos t) k' (EKind k)

failWith = CtxR . const . Err . pure

pullSimple t =
  synthesizeKind t >>= \case
    Simple k -> pure k
    k -> failWith $ KMismatch (pos t) k ESimple

type Mult = Positioned TLTerm

type Type = Positioned TLTerm

checkSup :: Foldable f => Mult -> f Type -> KindingResult ()
checkSup = error "TODO"

upperBound :: Int -> MultLit
upperBound = MultLit <$> (>= 1) <*> (<= 1)

upperBound' :: Position -> Int -> Positioned TLTerm
upperBound' p = Posed p . KMult . MLit . upperBound
