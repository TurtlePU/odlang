{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Core.Type.Equivalence where

import Control.Applicative (Alternative ((<|>)), liftA2)
import Control.Monad ((>=>))
import Control.Monad.FreeBi (FreeBi, iter)
import Core.Type.Evaluation (Substitution (..), eval, shift, substitute, unfoldMuPath)
import Core.Type.Kinding
import Core.Type.Syntax
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Join (Join (..))
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.Fix (Fix (..))
import Data.Foldable (asum)
import qualified Data.HashMap.Strict as HashMap
import Data.HashMultiMap (HashMultiMap (..))
import qualified Data.HashMultiMap as HashMultiMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IndexedBag (IndexedBag)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (Reflected (..), ReifiedEq (..), mkReflected)
import Data.Result (CtxResult (..), Result (..), failWith, mapCtx, runCtx)

------------------------------------- MULT -------------------------------------

type Offender a = IndexedBag a MultLit

checkMultEQ :: Eq a => MultTerm a -> MultTerm a -> Maybe (Offender a)
checkMultEQ l r =
  (fmap (`MultLit` False) <$> eqVia noWeakening)
    <|> (fmap (MultLit False) <$> eqVia noContraction)
  where
    eqVia f = checkBoolEQ (first f l) (first f r)

checkBoolEQ ::
  Eq a =>
  FreeBi MultF Bool a ->
  FreeBi MultF Bool a ->
  Maybe (IndexedBag a Bool)
checkBoolEQ l r =
  checkBoolLE (eval mkDNF l) (eval mkCNF r)
    <|> checkBoolLE (eval mkDNF r) (eval mkCNF l)
  where
    eval f = iter interpT . fmap f

checkBoolLE :: Eq a => DNF a -> CNF a -> Maybe (IndexedBag a Bool)
checkBoolLE (MkDNF dnf) (MkCNF cnf) = asum (liftA2 findSub dnf cnf)
  where
    findSub conj disj =
      if EqBag.isEmpty (conj `EqBag.intersection` disj)
        then Just (sub True conj <> sub False disj)
        else Nothing
    sub val set = val <$ EqBag.toMap set

type NormalForm a = [EqBag a]

newtype CNF a = MkCNF (NormalForm a)

mkCNF :: a -> CNF a
mkCNF = MkCNF . pure . EqBag.singleton

instance Eq a => Boolean (CNF a) where
  join (MkCNF l) (MkCNF r) = MkCNF (liftA2 (<>) l r)
  meet (MkCNF l) (MkCNF r) = MkCNF (l <> r)
  true = MkCNF []
  false = MkCNF [mempty]

newtype DNF a = MkDNF (NormalForm a)

mkDNF :: a -> DNF a
mkDNF = MkDNF . pure . EqBag.singleton

instance Eq a => Boolean (DNF a) where
  join (MkDNF l) (MkDNF r) = MkDNF (l <> r)
  meet (MkDNF l) (MkDNF r) = MkDNF (liftA2 (<>) l r)
  true = MkDNF [mempty]
  false = MkDNF []

------------------------------------ ROWS --------------------------------------

data RowEqError = EVars | EKeys | EUnder EntryKey

checkRowEQ :: (Eq t, Eq r) => RowTerm t r -> RowTerm t r -> [RowEqError]
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey mkUnder litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow = extract . iter fold . fmap fromVar
    fold = \case
      REmpty _ -> mempty
      REntry k v -> fromEntry k v
      RJoin l r -> l <> r
    extract (MkRow (Multi lit) var) = (lit, var)
    mkUnder l = \case
      True -> [EUnder l]
      False -> []

data Row t r = MkRow
  { rowLit :: HashMultiMap EntryKey (EqBag t),
    rowVar :: EqBag r
  }

fromEntry :: EntryKey -> t -> Row t r
fromEntry k =
  flip MkRow EqBag.empty
    . HashMultiMap.singleton k
    . EqBag.singleton

fromVar :: r -> Row t r
fromVar = MkRow HashMultiMap.empty . EqBag.singleton

instance (Eq t, Eq r) => Semigroup (Row t r) where
  MkRow l v <> MkRow l' v' = MkRow (l <> l') (v <> v')

instance (Eq t, Eq r) => Monoid (Row t r) where
  mempty = MkRow mempty mempty

------------------------------ GENERAL EQUIVALENCE -----------------------------

data EqError
  = EMultEq Position Position (Offender Term)
  | ERowEq Position Position (NonEmpty RowEqError)
  | EDataEq Position Position (DataVariety, DataVariety)
  | ETermNeq (Term, Term)
  | EKinding KindingError

data DataVariety
  = VArrow
  | VForall ProperKind
  | VSpread Connective

type EqResult = CtxResult [ProperKind] (NonEmpty EqError)

checkEQ :: Term -> Term -> EqResult ()
checkEQ l = first NonEmpty.fromList . mapCtx (,HashSet.empty) . impl l
  where
    impl :: Term -> Term -> RealEqResult ()
    impl l r =
      checkAssumption (l, r)
        <|> mapCtx
          (HashSet.insert (l, r) <$>)
          ( unfoldingEq l r
              <|> structuralEq l r
              <|> identityEq l r
              <|> extensionalEq l r
          )

    checkAssumption (l, r) = CtxR $ \(_, as) ->
      if HashSet.member (l, r) as || HashSet.member (r, l) as
        then Ok ()
        else Err []

    unfoldingEq l r = do
      k <- fromKinding (synthesizeKind l)
      mGuard (k == Simple Data)
      (unfoldMuPath' l >>= impl r) <|> (unfoldMuPath' r >>= impl l)

    unfoldMuPath' = fromKinding . unfoldMuPath

    identityEq l r = do
      fromKinding (synthesizeKind l) >>= pullRow
      case (l, r) of
        (Fix (TLam (LMap p f l)), r) -> isID p f *> impl l r
        (l, Fix (TLam (LMap p f r))) -> isID p f *> impl l r
        _ -> emptyErr

    pullRow = \case
      Row k -> pure k
      _ -> emptyErr

    structuralEq (Fix l) (Fix r) = case (l, r) of
      (TMul lp lm, TMul rp rm) ->
        checkMultEQ' lm rm >>= \case
          Just offender -> failWith $ EMultEq lp rp offender
          Nothing -> pure ()
      (TRow lp (Join lr), TRow rp (Join rr)) ->
        checkRowEQ' lr rr >>= \case
          e : es -> failWith $ ERowEq lp rp (e :| es)
          [] -> pure ()
      (TData lp ld, TData rp rd) -> case (ld, rd) of
        (PArrow ld lc, PArrow rd rc) -> impl ld rd *> impl lc rc
        (PForall lk lt, PForall rk rt) | lk == rk -> shiftCtx lk $ impl lt rt
        (PSpread lc lt, PSpread rc rt) | lc == rc -> impl lt rt
        (ld, rd) ->
          failWith $ EDataEq lp rp (getDataVariety ld, getDataVariety rd)
      (TLam ll, TLam rl) -> case (ll, rl) of
        (LVar li, LVar ri) | li == ri -> pure ()
        (LApp _ lf lx, LApp _ rf rx) -> impl lf rf *> impl lx rx
        (LAbs lk lb, LAbs rk rb) | lk == rk -> shiftCtx lk $ impl lb rb
        (LFst _ lp, LFst _ rp) -> impl lp rp
        (LSnd _ lp, LSnd _ rp) -> impl lp rp
        (LDat _ lt, LDat _ rt) -> impl lt rt
        (LMul _ lt, LMul _ rt) -> impl lt rt
        (LMap _ lf lr, LMap _ rf rr) -> impl lf rf *> impl lr rr
        (ll, rl) -> failWith $ ETermNeq (Fix $ TLam ll, Fix $ TLam rl)
      (l, r) -> failWith $ ETermNeq (Fix l, Fix r)

    extensionalEq l r = do
      k <- fromKinding (synthesizeKind l)
      mGuard (not $ isPath l && isPath r)
      case k of
        Type -> do
          (ld, lm) <- tyParts l
          (rd, rm) <- tyParts r
          impl ld rd *> impl lm rm
        Simple (_ :*: _) -> pairEq l r
        _ :**: _ -> pairEq l r
        _ -> emptyErr

    pairEq l r = do
      (lf, ls) <- pairParts l
      (rf, rs) <- pairParts r
      impl lf rf *> impl ls rs

    tyParts t =
      (,)
        <$> fromKinding (eval $ Fix $ TLam $ LDat mempty t)
        <*> fromKinding (eval $ Fix $ TLam $ LMul mempty t)

    pairParts p =
      (,)
        <$> fromKinding (eval $ Fix $ TLam $ LFst mempty p)
        <*> fromKinding (eval $ Fix $ TLam $ LSnd mempty p)

    isPath (Fix t) = case t of
      TType _ _ -> False
      TLam t -> case t of
        LVar _ -> True
        LApp _ f _ -> isPath f
        LMap _ f _ -> isPath f
        LFst _ p -> isPath p
        LSnd _ p -> isPath p
        LDat _ t -> isPath t
        LMul _ t -> isPath t
        _ -> False
      _ -> True

    isID :: Position -> Term -> RealEqResult ()
    isID p f = do
      (kx, ky) <- fromKinding $ synthesizeKind f >>= pullArrow p
      mGuard (kx == ky)
      impl f (Fix $ TLam $ LAbs kx $ Fix $ TLam $ LVar 0)

    mGuard b = if b then pure () else emptyErr

    emptyErr = CtxR $ const $ Err []

    fromKinding :: KindingResult a -> RealEqResult a
    fromKinding = mapCtx fst . first (NonEmpty.toList . fmap EKinding)

    shiftCtx :: ProperKind -> RealEqResult a -> RealEqResult a
    shiftCtx k = mapCtx $ bimap (k :) $ HashSet.map $ bimap (shift 1) (shift 1)

    checkMultEQ' ::
      MultTerm Term -> MultTerm Term -> RealEqResult (Maybe (Offender Term))
    checkMultEQ' m m' = CtxR $ \s -> Ok $
      reify (ReifiedEq $ runImpl s) $ \p ->
        first unreflect
          <$> checkMultEQ (mkReflected p <$> m) (mkReflected p <$> m')

    checkRowEQ' ::
      RowTerm Term Term -> RowTerm Term Term -> RealEqResult [RowEqError]
    checkRowEQ' r r' = CtxR $ \s ->
      Ok $
        reify (ReifiedEq $ runImpl s) $
          liftA2 checkRowEQ (reflect r) (reflect r')
      where
        reflect r p = bimap (mkReflected p) (mkReflected p) r

    runImpl :: ([ProperKind], Assumptions) -> Term -> Term -> Bool
    runImpl s l r = case runCtx s $ impl l r of
      Ok _ -> True
      Err _ -> False

    getDataVariety = \case
      PArrow _ _ -> VArrow
      PForall k _ -> VForall k
      PSpread c _ -> VSpread c

type Assumptions = HashSet (Term, Term)

type RealEqResult = CtxResult ([ProperKind], Assumptions) [EqError]
