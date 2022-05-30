{-# LANGUAGE LambdaCase #-}

module Core.Type where

import Control.Applicative (Applicative (liftA2))
import Control.Arrow ((<<<))
import Control.Monad ((<=<), (>=>))
import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import qualified Core.Type.Equivalence as Equivalence
import qualified Core.Type.Evaluation as Evaluation
import qualified Core.Type.Kinding as Kinding
import Core.Type.Syntax
import Data.Aps (Ap2 (..))
import Data.Bifunctor (Bifunctor (first))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFix)
import Data.Functor ((<&>))
import qualified Data.HashSet as HashSet
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe)
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (Reflected (..), ReifiedEq (..), mkReflected)
import Data.Result (CtxResult (..), Result (..), failWith, mapErrs, runCtx)

------------------------------- KINDING FRONTEND -------------------------------

type Kind = ProperKind

type TL = Term

type KindingResult = Kinding.KindingResult

checkKind :: Position -> Kind -> TL -> KindingResult ()
checkKind = Kinding.checkKind

isType :: Position -> TL -> KindingResult ()
isType p = checkKind p Type

------------------------------- CONTRACTIVENESS --------------------------------

checkContractiveness :: Position -> Type -> CtxResult a (NonEmpty Position) ()
checkContractiveness p t =
  if isContractive t then pure () else failWith p

isContractive :: Type -> Bool
isContractive t = areGuarded t HashSet.empty
  where
    areGuarded = foldFix $ \case
      TLam t -> case t of
        LVar i -> not . HashSet.member i
        LAbs _ t -> t . HashSet.map succ
        LFix _ _ t -> t . HashSet.insert 0 . HashSet.map succ
        t -> and . sequence t
      TMul _ (FreeBi (Pure t)) -> t
      TRow _ (Join (FreeBi (Pure t))) -> t
      t -> const $ and $ sequence t HashSet.empty

---------------------------- TYPE EQUALITY FRONTEND ----------------------------

type Type = Term

data TypeEqError
  = TEq Equivalence.EqError
  | TKind Kinding.KindingError
  | TContr Position

type TypeEqResult = CtxResult [Kind] (NonEmpty TypeEqError)

checkTypeEQ :: Position -> Type -> Type -> TypeEqResult ()
checkTypeEQ p l r = do
  checkWF p l *> checkWF p r
  (l', r') <- liftA2 (,) (eval l) (eval r)
  mapErrs TEq (Equivalence.checkEQ l' r')
  where
    checkWF p t =
      mapErrs TContr (checkContractiveness p t)
        *> mapErrs TKind (isType p t)
    eval = mapErrs TKind . Evaluation.eval

----------------------------- MULTIPLICITY FRONTEND ----------------------------

type Mult = Term

data MultLeError
  = MKind Kinding.KindingError
  | MLe (Equivalence.Offender TL)
  | MContr Position

type MultLeResult = CtxResult [Kind] (NonEmpty MultLeError)

checkMultLE :: Position -> Mult -> Mult -> MultLeResult ()
checkMultLE p m n = do
  checkWF p m *> checkWF p n
  (m', n') <- liftA2 (,) (pullMult m) (pullMult n)
  mapErrs MKind (checkLE' m' n') >>= \case
    Just offender -> failWith $ MLe offender
    Nothing -> pure ()
  where
    checkWF p m =
      mapErrs MContr (checkContractiveness p m)
        *> mapErrs MKind (checkKind p Mult m)
    pullMult m =
      mapErrs MKind (Evaluation.eval m) <&> \case
        Fix (TMul _ m) -> m
        t -> FreeBi (Pure t)
    checkLE' m n = CtxR $ \s -> Ok $
      reify (ReifiedEq $ eq s) $ \p ->
        first unreflect
          <$> Equivalence.checkMultLE (reflect p m) (reflect p n)
    reflect = fmap . mkReflected
    eq s l r = case runCtx s (Equivalence.checkEQ l r) of
      Ok _ -> True
      Err _ -> False

multAdmitting :: Int -> Position -> Mult
multAdmitting n p =
  Fix . TMul p . FreeBi . Free . Ap2 . MLit $
    MultLit {noWeakening = n > 0, noContraction = n < 2}

--------------------------------- ROW FRONTEND ---------------------------------

type Row = Term

-- TODO: rounding, key access

--------------------------- CONSTRUCTORS AND GETTERS ---------------------------

type Data = Term

mktype :: Position -> DataF TL -> Mult -> Type
mktype p = curry $ Fix . TType p . uncurry TLit . first (Fix . TData p)

arrow :: Position -> Type -> Type -> Mult -> Type
arrow p d c = mktype p (PArrow d c)

forall :: Position -> Kind -> Type -> Mult -> Type
forall p k = mktype p . PForall k

spread :: Position -> Connective -> Row -> Mult -> Type
spread p c = mktype p . PSpread c

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

layer :: Term -> PullResult Term
layer =
  mapErrs PKind
    <<< liftA2 fromMaybe pure Equivalence.unfoldMuPath
    <=< Evaluation.eval
