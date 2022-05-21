{-# LANGUAGE LambdaCase #-}

module Core.Type where

import Control.Monad ((>=>))
import qualified Core.Type.Equivalence as Equivalence
import qualified Core.Type.Evaluation as Evaluation
import qualified Core.Type.Kinding as Kinding
import Core.Type.Syntax
import Data.Bifunctor (Bifunctor (first))
import Data.Fix (Fix (..))
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty (NonEmpty)
import Data.Position (Position)
import Data.Result (CtxResult (..), Result (..), failWith)

------------------------------- KINDING FRONTEND -------------------------------

type Kind = ProperKind

type TL = Term

type KindingResult = Kinding.KindingResult

checkKind :: Position -> Kind -> TL -> KindingResult ()
checkKind = Kinding.checkKind

isType :: Position -> TL -> KindingResult ()
isType p = checkKind p Type

---------------------------- TYPE EQUALITY FRONTEND ----------------------------

type Type = Term

data TypeEqError
  = EEq Equivalence.EqError
  | EKind Kinding.KindingError
  | EContr Position

type TypeEqResult = CtxResult [Kind] (NonEmpty TypeEqError)

checkTypeEQ :: Position -> Type -> Type -> TypeEqResult ()
checkTypeEQ p l r = do
  checkWF p l
  checkWF p r
  l' <- eval l
  r' <- eval r
  first (EEq <$>) (Equivalence.checkEQ l' r')
  where
    checkWF p t =
      if isContractive t
        then fromKinding $ isType p t
        else failWith $ EContr p
    eval = fromKinding . Evaluation.eval
    fromKinding = first (EKind <$>)

isContractive :: Type -> Bool
isContractive = areGuarded HashSet.empty
  where
    areGuarded s (Fix t) = case t of
      TLam t -> case t of
        LVar i -> not $ HashSet.member i s
        LApp _ f x -> areGuarded s f && areGuarded s x
        LAbs _ t -> areGuarded (HashSet.map succ s) t
        LSPair _ l r -> areGuarded s l && areGuarded s r
        LPair l r -> areGuarded s l && areGuarded s r
        LFst _ p -> areGuarded s p
        LSnd _ p -> areGuarded s p
        LDat _ p -> areGuarded s p
        LMul _ p -> areGuarded s p
        LFix _ _ t -> areGuarded (HashSet.insert 0 $ HashSet.map succ s) t
        LMap _ f r -> areGuarded s f && areGuarded s r
      TType _ (TLit d m) -> areGuarded s d && areGuarded s m
      TData _ _ -> True
      TRow _ _ -> True
      TMul _ _ -> True

----------------------------- MULTIPLICITY FRONTEND ----------------------------

type Mult = Term

-- TODO: check <=, literal from number

--------------------------------- ROW FRONTEND ---------------------------------

type Row = Term

-- TODO: rounding, key access

--------------------------- CONSTRUCTORS AND GETTERS ---------------------------

arrow :: Position -> Type -> Type -> Mult -> Type
arrow p d c m = Fix $ TType p $ flip TLit m $ Fix $ TData p $ PArrow d c

forall :: Position -> Kind -> Type -> Mult -> Type
forall p k t m = Fix $ TType p $ flip TLit m $ Fix $ TData p $ PForall k t

spread :: Position -> Connective -> Row -> Mult -> Type
spread p c r m = Fix $ TType p $ flip TLit m $ Fix $ TData p $ PSpread c r

data PullError
  = PKind Kinding.KindingError
  | PNotThe Position DataVariety

data DataVariety
  = VArrow
  | VForall
  | VSpread

type PullResult = CtxResult [ProperKind] (NonEmpty PullError)

pullArrow :: Position -> Type -> PullResult (Type, Type)
pullArrow p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PArrow d c))) _)) -> pure (d, c)
    _ -> failWith $ PNotThe p VArrow

pullForall :: Position -> Type -> PullResult (Kind, Type)
pullForall p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PForall k t))) _)) -> pure (k, t)
    _ -> failWith $ PNotThe p VForall

pullSpread :: Position -> Type -> PullResult (Connective, Row)
pullSpread p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PSpread c r))) _)) -> pure (c, r)
    _ -> failWith $ PNotThe p VSpread

layer t = first (PKind <$>) (Evaluation.eval t >>= Evaluation.unfoldMuPath)
