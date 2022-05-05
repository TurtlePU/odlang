{-# LANGUAGE LambdaCase #-}

module Core.TypeLevel where

import Control.Monad (forM_)
import Core.Kind
import Core.Multiplicity
import Core.Pretype
import Core.Row
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..), nub)
import Position
import Result

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

data TLTerm t
  = KLam (TLLambda t)
  | KMult (MultTerm t)
  | KRow (RowTerm t t)
  | KType t t
  | KPretype (PreTypeT t t t t)

shiftTLTerm :: Positioned TLTerm -> Int -> Positioned TLTerm
shiftTLTerm = _

substTLTerm :: Positioned TLTerm -> Int -> Positioned TLTerm -> Positioned TLTerm
substTLTerm = _

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
synthesizeKind (Posed _ (KMult m)) = checkMultKind synthesizeKind m
synthesizeKind (Posed p (KRow r)) = synthesizeRowKind synthesizeKind synthesizeKind p r
synthesizeKind (Posed _ (KType _ _)) = _
synthesizeKind (Posed _ (KPretype _)) = _

checkKind :: ProperKind -> Positioned TLTerm -> KindingResult ()
checkKind k = intoCheck k synthesizeKind

nonEmpty ::
  (ProperKind -> a) -> (r -> a) -> (t -> a) -> RowTerm r t -> NonEmpty a
nonEmpty f g h = trifold (pure . f) (pure . g . snd) (pure . h)

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
