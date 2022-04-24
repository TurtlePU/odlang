{-# LANGUAGE DeriveFunctor #-}
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

data MultTerm
  = MLit MultLit
  | MJoin TLTerm TLTerm
  | MMeet TLTerm TLTerm
  deriving (Show)

data RowEntry = REntry
  { enPos :: Position,
    enLabel :: String,
    enTerm :: TLTerm
  }
  deriving (Show)

data RowTerm
  = REmpty ProperKind
  | RLit (NonEmpty RowEntry)
  | RJoin TLTerm TLTerm
  deriving (Show)

data TLLambda
  = LVar Int
  | LApp TLTerm TLTerm
  | LAbs ProperKind TLTerm
  | LSPair TLTerm TLTerm
  | LPair TLTerm TLTerm
  | LFst TLTerm
  | LSnd TLTerm
  | LPre TLTerm
  | LMul TLTerm
  | LFix SimpleKind TLTerm
  | LMap TLTerm TLTerm
  deriving (Show)

data Connective = CAnd | CWith | COr deriving (Show)

data PreTerm
  = PArrow TLTerm TLTerm
  | PForall ProperKind TLTerm
  | PSpread Connective TLTerm
  deriving (Show)

data TLTerm
  = KLam Position TLLambda
  | KMult Position MultTerm
  | KRow Position RowTerm
  | KType Position TLTerm TLTerm
  | KPretype Position PreTerm
  deriving (Show)

shiftTLTerm :: TLTerm -> Int -> TLTerm
shiftTLTerm = _

substTLTerm :: TLTerm -> Int -> TLTerm -> TLTerm
substTLTerm = _

type KindingResult = CtxResult [ProperKind] KindingErrors

synthesizeKind :: TLTerm -> KindingResult ProperKind
synthesizeKind (KLam _ (LVar i)) = CtxR $ Ok . (!! i)
synthesizeKind (KLam p (LApp f x)) =
  synthesizeKind f >>= \case
    kx :->: ky -> checkKind kx x $> ky
    k -> failWith $ KMismatch p EOperator k
synthesizeKind (KLam _ (LAbs k t)) =
  (k :->:) <$> mapCtx (k :) (synthesizeKind t)
synthesizeKind (KLam _ (LSPair l r)) =
  (Simple .) . (:*:) <$> pullSimple l <*> pullSimple r
synthesizeKind (KLam _ (LPair l r)) =
  (:**:) <$> synthesizeKind l <*> synthesizeKind r
synthesizeKind (KLam p (LFst t)) =
  synthesizeKind t >>= \case
    kl :**: _ -> pure kl
    Simple (kl :*: _) -> pure $ Simple kl
    k -> failWith $ KMismatch p EPair k
synthesizeKind (KLam p (LSnd t)) =
  synthesizeKind t >>= \case
    _ :**: kr -> pure kr
    Simple (_ :*: kr) -> pure $ Simple kr
    k -> failWith $ KMismatch p EPair k
synthesizeKind (KLam _ (LPre t)) = checkKind (Simple Type) t $> Simple Pretype
synthesizeKind (KLam _ (LMul t)) = checkKind (Simple Type) t $> Mult
synthesizeKind (KLam _ (LFix k t)) =
  mapCtx (Simple k :) (checkKind (Simple k) t) $> Simple k
synthesizeKind (KLam p (LMap f r)) =
  synthesizeKind f >>= \case
    kx :->: ky -> checkKind (Row kx) r $> Row ky
    k -> failWith $ KMismatch p EOperator k
synthesizeKind (KMult _ (MLit _)) = pure Mult
synthesizeKind (KMult _ (MJoin m m')) =
  checkKind Mult m *> checkKind Mult m' $> Mult
synthesizeKind (KMult _ (MMeet m m')) =
  checkKind Mult m *> checkKind Mult m' $> Mult
synthesizeKind (KRow _ (REmpty k)) = pure $ Row k
synthesizeKind (KRow _ (RLit (r :| rs))) = do
  k <- synthesizeKind (enTerm r)
  forM_ rs (checkKind k . enTerm) $> Row k
synthesizeKind (KRow p (RJoin l r)) = do
  kl <- pullRow l
  kr <- pullRow r
  if kl == kr
    then pure $ Row kl
    else failWith $ KDifferentRows p kl kr
synthesizeKind (KType _ t m) =
  checkKind (Simple Pretype) t *> checkKind Mult m $> Simple Type
synthesizeKind (KPretype _ (PArrow f x)) =
  checkKind (Simple Type) f *> checkKind (Simple Type) x $> Simple Pretype
synthesizeKind (KPretype _ (PForall k f)) =
  mapCtx (k :) (checkKind (Simple Type) f) $> Simple Pretype
synthesizeKind (KPretype _ (PSpread _ r)) = pullRow r $> Simple Pretype

checkKind :: ProperKind -> TLTerm -> KindingResult ()
checkKind k t = do
  k' <- synthesizeKind t
  if k == k'
    then pure ()
    else failWith $ KMismatch (getPos t) (EKind k) k'

failWith = CtxR . const . Err . pure

pullRow t =
  synthesizeKind t >>= \case
    Row k -> pure k
    k -> failWith $ KMismatch (getPos t) ERow k

pullSimple t =
  synthesizeKind t >>= \case
    Simple k -> pure k
    k -> failWith $ KMismatch (getPos t) ESimple k

getPos (KLam p _) = p
getPos (KMult p _) = p
getPos (KRow p _) = p
getPos (KType p _ _) = p
getPos (KPretype p _) = p

type Mult = TLTerm
type Type = TLTerm

checkSup :: Foldable f => Mult -> f Type -> KindingResult ()
checkSup = error "TODO"

upperBound :: Int -> MultLit
upperBound = MultLit <$> (>= 1) <*> (<= 1)

upperBound' :: Position -> Int -> TLTerm
upperBound' p = KMult p . MLit . upperBound
