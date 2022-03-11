{-# LANGUAGE LambdaCase #-}

module Core.TypeLevel where

import Control.Monad (forM_)
import Core.Kind
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..))
import Result

data Expected
  = EKind ProperKind
  | EOperator
  | EPair
  | ERow
  | ESimple
  deriving (Show)

data KindingError p
  = KMismatch p Expected ProperKind
  | KDifferentRows p ProperKind ProperKind
  deriving (Show)

type KindingErrors p = NonEmpty (KindingError p)

data MultLit = MultLit
  { noWeakening :: Bool,
    noContraction :: Bool
  }
  deriving (Show)

data MultTerm p
  = MLit MultLit
  | MJoin (TLTerm p) (TLTerm p)
  | MMeet (TLTerm p) (TLTerm p)
  deriving (Show)

data RowEntry p = REntry
  { enPos :: p,
    enLabel :: String,
    enTerm :: TLTerm p
  }
  deriving (Show)

data RowTerm p
  = REmpty ProperKind
  | RLit (NonEmpty (RowEntry p))
  | RJoin (TLTerm p) (TLTerm p)
  deriving (Show)

data TLLambda p
  = LVar Int
  | LApp (TLTerm p) (TLTerm p)
  | LAbs ProperKind (TLTerm p)
  | LSPair (TLTerm p) (TLTerm p)
  | LPair (TLTerm p) (TLTerm p)
  | LFst (TLTerm p)
  | LSnd (TLTerm p)
  | LFix SimpleKind (TLTerm p)
  | LMap (TLTerm p) (TLTerm p)
  deriving (Show)

data Connective = CAnd | CWith | COr deriving (Show)

data PreTerm p
  = PArrow (TLTerm p) (TLTerm p)
  | PForall ProperKind (TLTerm p)
  | PSpread Connective (TLTerm p)
  deriving (Show)

data TLTerm p
  = KLam p (TLLambda p)
  | KMult p (MultTerm p)
  | KRow p (RowTerm p)
  | KType p (TLTerm p) (TLTerm p)
  | KPretype p (PreTerm p)
  deriving (Show)

synthesizeKind ctx (KLam _ (LVar i)) = Ok (ctx !! i)
synthesizeKind ctx (KLam p (LApp f x)) =
  synthesizeKind ctx f >>= \case
    kx :->: ky -> checkKind ctx kx x $> ky
    k -> failWith $ KMismatch p EOperator k
synthesizeKind ctx (KLam _ (LAbs k t)) =
  (k :->:) <$> synthesizeKind (k : ctx) t
synthesizeKind ctx (KLam _ (LSPair l r)) = do
  kl <- synthesizeKind ctx l
  kr <- synthesizeKind ctx r
  case (kl, kr) of
    (Simple kl', Simple kr') -> Ok $ Simple $ kl' :*: kr'
    (kl, kr) ->
      Err $
        KMismatch (getPos l) ESimple kl
          :| [KMismatch (getPos r) ESimple kr]
synthesizeKind ctx (KLam _ (LPair l r)) =
  (:**:) <$> synthesizeKind ctx l <*> synthesizeKind ctx r
synthesizeKind ctx (KLam p (LFst t)) =
  synthesizeKind ctx t >>= \case
    kl :**: _ -> Ok kl
    Simple (kl :*: _) -> Ok $ Simple kl
    k -> failWith $ KMismatch p EPair k
synthesizeKind ctx (KLam p (LSnd t)) =
  synthesizeKind ctx t >>= \case
    _ :**: kr -> Ok kr
    Simple (_ :*: kr) -> Ok $ Simple kr
    k -> failWith $ KMismatch p EPair k
synthesizeKind ctx (KLam _ (LFix k t)) =
  checkKind (Simple k : ctx) (Simple k) t $> Simple k
synthesizeKind ctx (KLam p (LMap f r)) =
  synthesizeKind ctx f >>= \case
    kx :->: ky -> checkKind ctx (Row kx) r $> Row ky
    k -> failWith $ KMismatch p EOperator k
synthesizeKind _ (KMult _ (MLit _)) = Ok Mult
synthesizeKind ctx (KMult _ (MJoin m m')) =
  checkKind ctx Mult m *> checkKind ctx Mult m' $> Mult
synthesizeKind ctx (KMult _ (MMeet m m')) =
  checkKind ctx Mult m *> checkKind ctx Mult m' $> Mult
synthesizeKind ctx (KRow _ (REmpty k)) = Ok $ Row k
synthesizeKind ctx (KRow _ (RLit (r :| rs))) = do
  k <- synthesizeKind ctx $ enTerm r
  forM_ rs (checkKind ctx k . enTerm) $> Row k
synthesizeKind ctx (KRow p (RJoin l r)) = do
  kl <- synthesizeKind ctx l >>= pullRow (getPos l)
  kr <- synthesizeKind ctx r >>= pullRow (getPos r)
  if kl == kr
    then Ok $ Row kl
    else failWith $ KDifferentRows p kl kr
synthesizeKind ctx (KType _ t m) =
  checkKind ctx (Simple Pretype) t *> checkKind ctx Mult m $> Simple Type
synthesizeKind ctx (KPretype _ (PArrow f x)) =
  checkKind ctx (Simple Type) f
    *> checkKind ctx (Simple Type) x
    $> Simple Pretype
synthesizeKind ctx (KPretype _ (PForall k f)) =
  checkKind (k : ctx) (Simple Type) f $> Simple Pretype
synthesizeKind ctx (KPretype _ (PSpread _ r)) =
  (synthesizeKind ctx r >>= pullRow (getPos r)) $> Simple Pretype

getPos (KLam p _) = p
getPos (KMult p _) = p
getPos (KRow p _) = p
getPos (KType p _ _) = p
getPos (KPretype p _) = p

failWith = Err . pure

pullRow _ (Row r) = Ok r
pullRow p k = failWith $ KMismatch p ERow k

assertKind ctx k t = checkKind ctx k t $> k

checkKind ::
  [ProperKind] ->
  ProperKind ->
  TLTerm p ->
  Result (KindingErrors p) ()
checkKind ctx k t = do
  k' <- synthesizeKind ctx t
  if k == k'
    then Ok ()
    else failWith $ KMismatch (getPos t) (EKind k) k'
