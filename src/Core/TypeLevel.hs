{-# LANGUAGE LambdaCase #-}

module Core.TypeLevel where

import Control.Monad (forM_)
import Core.Kind
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..))
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
  = KMismatch Position Expected ProperKind
  | KDifferentRows Position ProperKind ProperKind
  deriving (Show)

type KindingErrors = NonEmpty KindingError

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Show)

data MultTerm t
  = MLit MultLit
  | MJoin t t
  | MMeet t t
  deriving (Show)

data RowEntry t = REntry
  { enPos :: Position,
    enLabel :: String,
    enTerm :: t
  }
  deriving (Show)

data RowTerm t
  = REmpty ProperKind
  | RLit (NonEmpty (RowEntry t))
  | RJoin t t
  deriving (Show)

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
    k -> failWith $ KMismatch p EOperator k
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
    k -> failWith $ KMismatch p EPair k
synthesizeKind (Posed p (KLam (LSnd t))) =
  synthesizeKind t >>= \case
    _ :**: kr -> pure kr
    Simple (_ :*: kr) -> pure $ Simple kr
    k -> failWith $ KMismatch p EPair k
synthesizeKind (Posed _ (KLam (LPre t))) =
  checkKind (Simple Type) t $> Simple Pretype
synthesizeKind (Posed _ (KLam (LMul t))) = checkKind (Simple Type) t $> Mult
synthesizeKind (Posed _ (KLam (LFix k t))) =
  mapCtx (Simple k :) (checkKind (Simple k) t) $> Simple k
synthesizeKind (Posed p (KLam (LMap f r))) =
  synthesizeKind f >>= \case
    kx :->: ky -> checkKind (Row kx) r $> Row ky
    k -> failWith $ KMismatch p EOperator k
synthesizeKind (Posed _ (KMult (MLit _))) = pure Mult
synthesizeKind (Posed _ (KMult (MJoin m m'))) =
  checkKind Mult m *> checkKind Mult m' $> Mult
synthesizeKind (Posed _ (KMult (MMeet m m'))) =
  checkKind Mult m *> checkKind Mult m' $> Mult
synthesizeKind (Posed _ (KRow (REmpty k))) = pure $ Row k
synthesizeKind (Posed _ (KRow (RLit (r :| rs)))) = do
  k <- synthesizeKind (enTerm r)
  forM_ rs (checkKind k . enTerm) $> Row k
synthesizeKind (Posed p (KRow (RJoin l r))) = do
  kl <- pullRow l
  kr <- pullRow r
  if kl == kr
    then pure $ Row kl
    else failWith $ KDifferentRows p kl kr
synthesizeKind (Posed _ (KType t m)) =
  checkKind (Simple Pretype) t *> checkKind Mult m $> Simple Type
synthesizeKind (Posed _ (KPretype (PArrow f x))) =
  checkKind (Simple Type) f *> checkKind (Simple Type) x $> Simple Pretype
synthesizeKind (Posed _ (KPretype (PForall k f))) =
  mapCtx (k :) (checkKind (Simple Type) f) $> Simple Pretype
synthesizeKind (Posed _ (KPretype (PSpread _ r))) = pullRow r $> Simple Pretype

checkKind :: ProperKind -> Positioned TLTerm -> KindingResult ()
checkKind k t = do
  k' <- synthesizeKind t
  if k == k'
    then pure ()
    else failWith $ KMismatch (pos t) (EKind k) k'

failWith = CtxR . const . Err . pure

pullRow t =
  synthesizeKind t >>= \case
    Row k -> pure k
    k -> failWith $ KMismatch (pos t) ERow k

pullSimple t =
  synthesizeKind t >>= \case
    Simple k -> pure k
    k -> failWith $ KMismatch (pos t) ESimple k

type Mult = Positioned TLTerm
type Type = Positioned TLTerm

checkSup :: Foldable f => Mult -> f Type -> KindingResult ()
checkSup = error "TODO"

upperBound :: Int -> MultLit
upperBound = MultLit <$> (>= 1) <*> (<= 1)

upperBound' :: Position -> Int -> Positioned TLTerm
upperBound' p = Posed p . KMult . MLit . upperBound
