{-# LANGUAGE LambdaCase #-}

module Core.Type where

import Control.Applicative (Applicative (liftA2))
import Control.Monad ((>=>))
import qualified Core.Type.Equivalence as Equivalence
import qualified Core.Type.Evaluation as Evaluation
import qualified Core.Type.Kinding as Kinding
import Core.Type.Syntax
import Data.Bifunctor (Bifunctor (first))
import Data.Fix (Fix (..), foldFix)
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe)
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
isContractive t = areGuarded t HashSet.empty
  where
    areGuarded = foldFix $ \case
      TLam t -> case t of
        LVar i -> not . HashSet.member i
        LAbs _ t -> t . HashSet.map succ
        LFix _ _ t -> t . HashSet.insert 0 . HashSet.map succ
        t -> and . sequence t
      TType _ t -> and . sequence t
      _ -> const True

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

layer =
  first (PKind <$>)
    . ( Evaluation.eval
          >=> liftA2 ($) (fromMaybe . pure) Equivalence.unfoldMuPath
      )
