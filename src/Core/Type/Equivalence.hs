{-# LANGUAGE LambdaCase #-}

module Core.Type.Equivalence where

import Control.Applicative (Alternative ((<|>)), liftA2)
import Control.Monad.FreeBi (FreeBi, iter)
import Core.Type.Evaluation (Substitution (..), runSubstitution, shift)
import Core.Type.Kinding (KindingError, KindingResult, pullArrow, synthesizeKind)
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
import Data.Result (CtxResult (..), Result (..), mapCtx, runCtx)

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
checkEQ l r = CtxR $ \ks -> case runCtx (ks, HashSet.empty) $ impl l r of
  Err (x : xs) -> Err (x :| xs)
  Err [] -> error "empty error list"
  _ -> Ok ()
  where
    impl :: Term -> Term -> RealEqResult ()
    impl l r =
      checkAssumptionOr (l, r) $
        mapCtx (HashSet.insert (l, r) <$>) $
          checkMapId l r
            <|> case (unFix l, unFix r) of
              (TMul p m, TMul p' m') ->
                checkMultEQ' m m' >>= \case
                  Just offender -> failWith $ EMultEq p p' offender
                  Nothing -> pure ()
              (TRow p (Join r), TRow p' (Join r')) ->
                checkRowEQ' r r' >>= \case
                  e : es -> failWith $ ERowEq p p' (e :| es)
                  [] -> pure ()
              (TType p (TLit d m), TType p' (TLit d' m')) ->
                impl d d' *> impl m m'
              (TData p d, TData p' d') -> case (d, d') of
                (PArrow d c, PArrow d' c') -> impl d d' *> impl c c'
                (PForall k t, PForall k' t')
                  | k == k' -> shiftAssumptions $ impl t t'
                (PSpread c t, PSpread c' t') | c == c' -> impl t t'
                (d, d') ->
                  failWith $ EDataEq p p' (getDataVariety d, getDataVariety d')
              (TLam (LFix p k t), t') -> unfoldLFix p k t >>= impl (Fix t')
              (t, TLam (LFix p' k' t')) -> unfoldLFix p' k' t' >>= impl (Fix t)
              -- TODO: extensional pair equality
              (TLam t, TLam t') -> case (t, t') of
                (LVar i, LVar i') | i == i' -> pure ()
                (LApp _ f x, LApp _ f' x') -> impl f f' *> impl x x'
                (LAbs k t, LAbs k' t')
                  | k == k' -> shiftAssumptions $ impl t t'
                (LSPair _ l r, LSPair _ l' r') -> impl l l' *> impl r r'
                (LPair l r, LPair l' r') -> impl l l' *> impl r r'
                (LFst _ t, LFst _ t') -> impl t t'
                (LSnd _ t, LSnd _ t') -> impl t t'
                (LDat _ t, LDat _ t') -> impl t t'
                (LMul _ t, LMul _ t') -> impl t t'
                (LMap _ f r, LMap _ f' r') -> impl f f' *> impl r r'
                (t, t') -> failWith $ ETermNeq (Fix $ TLam t, Fix $ TLam t')
              (t, t') -> failWith $ ETermNeq (Fix t, Fix t')

    checkAssumptionOr (l, r) res = CtxR $ \(ks, as) ->
      if HashSet.member (l, r) as || HashSet.member (r, l) as
        then Ok ()
        else withCtx res (ks, as)

    checkMapId :: Term -> Term -> RealEqResult ()
    checkMapId (Fix l) (Fix r) = case (l, r) of
      (TLam (LMap p f r), r') -> isID p f *> impl r (Fix r')
      (r, TLam (LMap p f' r')) -> isID p f' *> impl (Fix r) r'
      _ -> emptyErr

    isID :: Position -> Term -> RealEqResult ()
    isID p f = do
      (kx, ky) <- fromKinding $ synthesizeKind f >>= pullArrow p
      if kx == ky
        then impl f $ Fix $ TLam $ LAbs kx $ Fix $ TLam $ LVar 0
        else emptyErr

    emptyErr = CtxR $ const $ Err []

    unfoldLFix p k t =
      fromKinding $ flip runSubstitution t $ SubWith $ Fix $ TLam $ LFix p k t

    fromKinding :: KindingResult a -> RealEqResult a
    fromKinding = mapCtx fst . first (NonEmpty.toList . fmap EKinding)

    shiftAssumptions :: RealEqResult a -> RealEqResult a
    shiftAssumptions = mapCtx $ second $ HashSet.map $ bimap (shift 1) (shift 1)

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

    failWith = CtxR . const . Err . pure

type Assumptions = HashSet (Term, Term)

type RealEqResult = CtxResult ([ProperKind], Assumptions) [EqError]
