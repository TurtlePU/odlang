{-# LANGUAGE LambdaCase #-}

module Core.Type where

import Control.Applicative (Applicative (..))
import Control.Arrow ((<<<))
import Control.Monad ((<=<), (>=>))
import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Result (CtxResult, Result (..), failWith, mapErrs, runCtx)
import Core.Type.Contract (WellFormed (..))
import qualified Core.Type.Contract as Contract
import qualified Core.Type.Equivalence as Equivalence
import qualified Core.Type.Evaluation as Evaluation
import qualified Core.Type.Kinding as Kinding
import Core.Type.Result (TypeResult)
import Core.Type.Syntax
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Ap2 (Ap2 (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFix)
import Data.Function (on)
import Data.Functor.Identity (Identity (..))
import Data.HashMap.Monoidal (MonoidalHashMap)
import qualified Data.HashMap.Monoidal as MonoidalHashMap
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe)
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (Reflected (..), ReifiedEq (..), mkReflected)

--------------------------- WELL-FORMEDNESS FRONTEND ---------------------------

type Malformed = Term

type TL = Contract.WellFormed

wellFormed :: Position -> Malformed -> TypeResult Contract.ContractError TL
wellFormed = Contract.wellFormed

------------------------------- KINDING FRONTEND -------------------------------

type Kind = ProperKind

checkKind :: Position -> Kind -> TL -> Kinding.KindingResult ()
checkKind p k = Kinding.checkKind p k . unWF

---------------------------- TYPE EQUALITY FRONTEND ----------------------------

type Type = TL

checkTypeEQ :: Type -> Type -> TypeResult Equivalence.EqError ()
checkTypeEQ = Equivalence.checkEQ `on` unWF

----------------------------- MULTIPLICITY FRONTEND ----------------------------

type Mult = TL

checkMultLE :: Mult -> Mult -> TypeResult (Equivalence.Offender TL) ()
checkMultLE m n =
  on checkLE' (Evaluation.liftMult . unWF) m n >>= \case
    Just offender -> failWith $ map (first MkWF) offender
    Nothing -> pure ()
  where
    checkLE' m n = ReaderT $ \s -> Ok $
      reify (ReifiedEq $ eq s) $ \p ->
        map (first unreflect)
          <$> on Equivalence.checkMultLE (mkReflected p <$>) m n
    eq s l r = case runCtx s (Equivalence.checkEQ l r) of
      Ok _ -> True
      Err _ -> False

multAdmitting :: Int -> Position -> Mult
multAdmitting n p =
  MkWF . Fix . TMul p . FreeBi . Free . Ap2 . MLit $
    MultLit {noWeakening = n > 0, noContraction = n < 2}

--------------------------------- ROW FRONTEND ---------------------------------

type Row = TL

data RowRepr = MkRepr
  { reLit :: MonoidalHashMap EntryKey (NonEmpty TL),
    reVar :: [TL]
  }

instance Semigroup RowRepr where
  MkRepr l v <> MkRepr l' v' = MkRepr (l <> l') (v <> v')

instance Monoid RowRepr where
  mempty = MkRepr mempty mempty

rowRepr :: Row -> RowRepr
rowRepr = bifoldMap entry var . Evaluation.liftRow . Identity . unWF
  where
    var = MkRepr mempty . pure . MkWF . runIdentity
    entry (k, v) =
      flip MkRepr mempty . MonoidalHashMap.singleton k . pure $ MkWF v

data RowKey = KLit EntryKey | KRest

data KeyError
  = KKind Kinding.KindingError
  | KAmbiguous Position RowKey

getEntry :: Position -> RowRepr -> RowKey -> TypeResult KeyError (Maybe TL)
getEntry p (MkRepr l _) (KLit k) = case MonoidalHashMap.lookup k l of
  Just (x :| []) -> pure (Just x)
  Just _ -> failWith . KAmbiguous p $ KLit k
  Nothing -> pure Nothing
getEntry p (MkRepr _ v) KRest = case v of
  [MkWF x] ->
    fmap (Just . MkWF) . mapErrs KKind . Evaluation.eval . Fix . TLam $ LRnd p x
  [] -> pure Nothing
  _ -> failWith (KAmbiguous p KRest)

--------------------------- CONSTRUCTORS AND GETTERS ---------------------------

mktype :: Position -> DataF Type -> Mult -> Type
mktype p t = MkWF . Fix . TType p . TLit (Fix . TData p $ unWF <$> t) . unWF

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

type PullResult = TypeResult PullError

pullArrow :: Position -> Type -> PullResult (Type, Type)
pullArrow p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PArrow d c))) _)) -> pure (MkWF d, MkWF c)
    _ -> failWith (PNotThe p VArrow)

pullForall :: Position -> Type -> PullResult (Kind, Type)
pullForall p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PForall k t))) _)) -> pure (k, MkWF t)
    _ -> failWith (PNotThe p VForall)

pullSpread :: Position -> Type -> PullResult (Connective, Row)
pullSpread p =
  layer >=> \case
    Fix (TType _ (TLit (Fix (TData _ (PSpread c r))) _)) -> pure (c, MkWF r)
    _ -> failWith (PNotThe p VSpread)

layer :: Type -> PullResult Term
layer = mapErrs PKind . liftA2 fromMaybe pure Equivalence.unfoldMuPath . unWF
