{-# LANGUAGE LambdaCase #-}

module Core.Type where

import Control.Applicative (Applicative (..))
import Control.Arrow ((<<<), (>>>))
import Control.Composition ((-.), (.*), (.**), (.@), (.@@), (<-=*<))
import Control.Monad ((<=<), (>=>))
import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (Ap2 (..), FreeBi (..))
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Result
import Core.Type.Contract (WellFormed (..))
import qualified Core.Type.Contract as Contract
import qualified Core.Type.Equivalence as Equivalence
import qualified Core.Type.Evaluation as Evaluation
import qualified Core.Type.Kinding as Kinding
import Core.Type.Result (TypeResult)
import Core.Type.Syntax
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFix)
import Data.Function (on)
import Data.Function.Slip (slipl, slipr)
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

wellFormed :: Malformed -> Position -> TypeResult Contract.ContractError TL
wellFormed = Contract.wellFormed

------------------------------- KINDING FRONTEND -------------------------------

type Kind = ProperKind

checkKind :: Kind -> TL -> Position -> Kinding.KindingResult ()
checkKind = unWF .@ Kinding.checkKind

---------------------------- TYPE EQUALITY FRONTEND ----------------------------

type Type = TL

checkTypeEQ :: Type -> Type -> TypeResult Equivalence.EqError ()
checkTypeEQ = Equivalence.checkEQ `on` unWF

----------------------------- MULTIPLICITY FRONTEND ----------------------------

type Mult = TL

checkMultLE :: Mult -> Mult -> TypeResult (Equivalence.Offender TL) ()
checkMultLE = ReaderT .* finish .** slipr check `on` Evaluation.liftMult . unWF
  where
    finish = \case
      Just offender -> failWith $ first MkWF <$> offender
      Nothing -> pure ()
    check s =
      reify (ReifiedEq $ slipl eq s) $
        fmap (first unreflect <$>)
          .** on Equivalence.checkMultLE . fmap . mkReflected
    eq = isOk .** runReaderT .* Equivalence.checkEQ

multAdmitting :: Int -> Position -> Mult
multAdmitting = MkWF .* Fix .* TMul . FreeBi . Free . Ap2 . MLit . body
  where
    body n = MultLit {noWeakening = n > 0, noContraction = n < 2}

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
rowRepr = bifoldMap (uncurry entry) var . Evaluation.liftRow . Identity . unWF
  where
    var = MkRepr mempty . pure . MkWF . runIdentity
    entry = flip MkRepr mempty .* MkWF .@ pure .@ MonoidalHashMap.singleton

data RowKey = KLit EntryKey | KRest

data KeyError
  = KKind Kinding.KindingError
  | KAmbiguous RowKey Position

getEntry :: RowKey -> RowRepr -> Position -> TypeResult KeyError (Maybe TL)
getEntry = \case
  KLit k ->
    reLit >>> MonoidalHashMap.lookup k >>> \case
      Just (x :| []) -> const $ pure (Just x)
      Just _ -> failWith . KAmbiguous (KLit k)
      Nothing -> const $ pure Nothing
  KRest ->
    reVar >>> \case
      [MkWF x] ->
        fmap (Just . MkWF) . mapErrs KKind
          . Evaluation.eval
          . Fix
          . TLam
          . LRnd x
      [] -> const $ pure Nothing
      _ -> failWith . KAmbiguous KRest

--------------------------- CONSTRUCTORS AND GETTERS ---------------------------

mktype :: DataF Type -> Mult -> Position -> Type
mktype =
  MkWF .** Fix .** (TType =<<)
    .* slipr (unWF .@@ TLit .* Fix .* (unWF <$>) .@ flip TData)

data PullError
  = PKind Kinding.KindingError
  | PNotThe DataVariety Position

data DataVariety
  = VArrow
  | VForall
  | VSpread

type PullResult = TypeResult PullError

pullArrow :: Type -> Position -> PullResult (Type, Type)
pullArrow = flip $ layer <-=*< flip finisher
  where
    finisher (Fix (TType (TLit (Fix (TData (PArrow d c) _)) _) _)) =
      const $ pure (MkWF d, MkWF c)
    finisher _ = failWith . PNotThe VArrow

pullForall :: Type -> Position -> PullResult (Kind, Type)
pullForall = flip $ layer <-=*< flip finisher
  where
    finisher (Fix (TType (TLit (Fix (TData (PForall k t) _)) _) _)) =
      const $ pure (k, MkWF t)
    finisher _ = failWith . PNotThe VForall

pullSpread :: Type -> Position -> PullResult (Connective, Row)
pullSpread = flip $ layer <-=*< flip finisher
  where
    finisher (Fix (TType (TLit (Fix (TData (PSpread c r) _)) _) _)) =
      const $ pure (c, MkWF r)
    finisher _ = failWith . PNotThe VSpread

layer :: Type -> PullResult Term
layer = mapErrs PKind . liftA2 fromMaybe pure Equivalence.unfoldMuPath . unWF
