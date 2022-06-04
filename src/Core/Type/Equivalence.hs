{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Core.Type.Equivalence where

import Algebra.Lattice hiding (Join)
import Control.Applicative (Alternative ((<|>)), liftA2)
import Control.Composition (on, (.*), (.**), (.@))
import Control.Monad (join)
import Control.Monad.FreeBi (FreeBi (FreeBi, runFreeBi), iter)
import Control.Monad.Reader (ReaderT (ReaderT, runReaderT))
import Control.Monad.Result
import Core.Type.Evaluation
import Core.Type.Kinding
import Core.Type.Result (TypeResult)
import Core.Type.Syntax
import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.EqBag (EqBag)
import qualified Data.EqBag as EqBag
import Data.Fix (Fix (..), foldFix)
import Data.Foldable (asum)
import Data.Function.Slip (slipl, slipr)
import Data.Functor.Identity (Identity (..))
import Data.HashMap.Monoidal (MonoidalHashMap (..))
import qualified Data.HashMap.Monoidal as MonoidalHashMap
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Position (Position)
import Data.Reflection (reify)
import Data.Reflection.Instances (Reflected (..), ReifiedEq (..), mkReflected)

------------------------------------- MULT -------------------------------------

type Offender a = [(a, MultLit)]

checkMultEQ :: Eq a => MultTerm a -> MultTerm a -> Maybe (Offender a)
-- ^ Different variables are assumed to be independent
checkMultEQ l r =
  (fmap (second $ flip MultLit False) <$> eqVia noWeakening)
    <|> (fmap (second $ MultLit False) <$> eqVia noContraction)
  where
    eqVia f = on checkBoolEQ (first f) l r

checkMultLE :: Eq a => MultTerm a -> MultTerm a -> Maybe (Offender a)
-- ^ Different variables are assumed to be independent
checkMultLE l r =
  (fmap (second $ flip MultLit False) <$> leVia noWeakening)
    <|> (fmap (second $ MultLit False) <$> leVia noContraction)
  where
    leVia f = checkBoolLE (evalM mkDNF $ first f l) (evalM mkCNF $ first f r)

checkBoolEQ ::
  Eq a =>
  FreeBi MultF Bool a ->
  FreeBi MultF Bool a ->
  Maybe [(a, Bool)]
checkBoolEQ l r =
  checkBoolLE (evalM mkDNF l) (evalM mkCNF r)
    <|> checkBoolLE (evalM mkDNF r) (evalM mkCNF l)

checkBoolLE :: Eq a => DNF a -> CNF a -> Maybe [(a, Bool)]
checkBoolLE (MkDNF dnf) (MkCNF cnf) = asum (liftA2 findSub dnf cnf)
  where
    findSub conj disj =
      if EqBag.isEmpty (conj `EqBag.intersection` disj)
        then Just (sub True conj <> sub False disj)
        else Nothing
    sub = EqBag.values .@ map . flip (,)

type NormalForm a = [EqBag a]

newtype CNF a = MkCNF (NormalForm a)

mkCNF :: a -> CNF a
mkCNF = MkCNF . pure . EqBag.singleton

instance Eq a => Lattice (CNF a) where
  MkCNF l \/ MkCNF r = MkCNF (liftA2 (<>) l r)
  MkCNF l /\ MkCNF r = MkCNF (l <> r)

instance Eq a => BoundedJoinSemiLattice (CNF a) where
  bottom = MkCNF [mempty]

instance Eq a => BoundedMeetSemiLattice (CNF a) where
  top = MkCNF []

newtype DNF a = MkDNF (NormalForm a)

mkDNF :: a -> DNF a
mkDNF = MkDNF . pure . EqBag.singleton

instance Eq a => Lattice (DNF a) where
  MkDNF l \/ MkDNF r = MkDNF (l <> r)
  MkDNF l /\ MkDNF r = MkDNF (liftA2 (<>) l r)

instance Eq a => BoundedJoinSemiLattice (DNF a) where
  bottom = MkDNF []

instance Eq a => BoundedMeetSemiLattice (DNF a) where
  top = MkDNF [mempty]

------------------------------------ ROWS --------------------------------------

data RowEqError = EVars | EKeys | EUnder EntryKey deriving (Eq, Show)

checkRowEQ :: (Eq t, Eq r) => RowTerm t r -> RowTerm t r -> [RowEqError]
-- ^ Different variables are assumed to be independent
checkRowEQ l r =
  let (lLit, lVar) = intoRow l
      (rLit, rVar) = intoRow r
      litNeqs = HashMap.intersectionWith (/=) lLit rLit
   in [EKeys | HashMap.keysSet lLit /= HashMap.keysSet rLit]
        ++ HashMap.foldMapWithKey (\label neq -> [EUnder label | neq]) litNeqs
        ++ [EVars | lVar /= rVar]
  where
    intoRow =
      (\(MkRow lit var) -> (getMonoidalHashMap lit, var))
        . bifoldMap (uncurry entry) var
        . runBiff
    entry =
      flip MkRow EqBag.empty .* EqBag.singleton .@ MonoidalHashMap.singleton
    var = MkRow mempty . EqBag.singleton . runIdentity

data Row t r = MkRow
  { rowLit :: MonoidalHashMap EntryKey (EqBag t),
    rowVar :: EqBag r
  }

instance (Eq t, Eq r) => Semigroup (Row t r) where
  MkRow l v <> MkRow l' v' = MkRow (l <> l') (v <> v')

instance (Eq t, Eq r) => Monoid (Row t r) where
  mempty = MkRow mempty mempty

------------------------------ GENERAL EQUIVALENCE -----------------------------

data EqError
  = EMultEq (Offender Term) Position Position
  | ERowEq (NonEmpty RowEqError) Position Position
  | EDataEq (DataVariety, DataVariety) Position Position
  | ETermNeq (Term, Term)
  | EKinding KindingError
  deriving (Eq, Show)

data DataVariety
  = VArrow
  | VForall ProperKind
  | VSpread Connective
  deriving (Eq, Show)

type EqResult = TypeResult EqError

checkEQ :: Term -> Term -> EqResult ()
-- ^ Terms are assumed to be in a beta-normal form
checkEQ = mapErr NonEmpty.fromList .* mapCtx (,HashSet.empty) .* impl
  where
    impl :: Term -> Term -> RealEqResult ()
    impl l r =
      checkAssumption (l, r)
        <|> mapCtx
          (second $ HashSet.insert (l, r))
          ( unfoldingEq l r
              <|> structuralEq l r
              <|> identityEq l r
              <|> extensionalEq l r
          )

    checkAssumption =
      ReaderT . \(l, r) (_, as) ->
        if HashSet.member (l, r) as || HashSet.member (r, l) as
          then Ok ()
          else Err []

    unfoldingEq l r = do
      k <- fromKinding (synthesizeKind l)
      mGuard (k == Simple Data)
      (unfoldMuPath' l >>= impl r) <|> (unfoldMuPath' r >>= impl l)
      where
        unfoldMuPath' = maybe emptyErr fromKinding . unfoldMuPath

    identityEq l r = do
      fromKinding (synthesizeKind l) >>= pullRow
      case (l, r) of
        (Fix (TLam (LMap f l p)), r) -> isID f p *> impl l r
        (l, Fix (TLam (LMap f r p))) -> isID f p *> impl l r
        _ -> emptyErr
      where
        isID f p = do
          (kx, ky) <- fromKinding (synthesizeKind f >>= flip pullArrow p)
          mGuard (kx == ky)
          impl f . Fix . TLam . LAbs kx . Fix . TLam $ LVar 0

        pullRow = \case
          Row k -> pure k
          _ -> emptyErr

    structuralEq (Fix l) (Fix r) = case (l, r) of
      (TMul lm lp, TMul rm rp) ->
        checkMultEQ' lm rm >>= \case
          Just offender -> failWith $ EMultEq offender lp rp
          Nothing -> pure ()
      (TRow (Join lr) lp, TRow (Join rr) rp) ->
        checkRowEQ' lr rr >>= \case
          e : es -> failWith $ ERowEq (e :| es) lp rp
          [] -> pure ()
      (TData ld lp, TData rd rp) -> case (ld, rd) of
        (PArrow ld lc, PArrow rd rc) -> impl ld rd *> impl lc rc
        (PForall lk lt, PForall rk rt) | lk == rk -> shiftCtx lk $ impl lt rt
        (PSpread lc lt, PSpread rc rt) | lc == rc -> impl lt rt
        (ld, rd) -> failWith $ EDataEq (variety ld, variety rd) lp rp
      (TLam ll, TLam rl) -> case (ll, rl) of
        (LVar li, LVar ri) | li == ri -> pure ()
        (LApp lf lx _, LApp rf rx _) -> impl lf rf *> impl lx rx
        (LAbs lk lb, LAbs rk rb) | lk == rk -> shiftCtx lk $ impl lb rb
        (LFst lp _, LFst rp _) -> impl lp rp
        (LSnd lp _, LSnd rp _) -> impl lp rp
        (LDat lt _, LDat rt _) -> impl lt rt
        (LMul lt _, LMul rt _) -> impl lt rt
        (LMap lf lr _, LMap rf rr _) -> impl lf rf *> impl lr rr
        (LRnd lr _, LRnd rr _) -> impl lr rr
        (ll, rl) -> failWith $ ETermNeq (Fix $ TLam ll, Fix $ TLam rl)
      (l, r) -> failWith $ ETermNeq (Fix l, Fix r)
      where
        shiftCtx k =
          mapCtx . bimap (k :) . HashSet.map $
            bimap (shift 1) (shift 1)

        checkMultEQ' = ReaderT .* Ok .** slipr check
          where
            check s =
              reify (ReifiedEq $ runImpl s) $
                fmap (first unreflect <$>)
                  .** on checkMultEQ . fmap . mkReflected

        checkRowEQ' = ReaderT .* Ok .** slipr check
          where
            check s =
              reify (ReifiedEq $ runImpl s) $
                on checkRowEQ . join bimap . mkReflected

        runImpl = isOk .** slipl (runReaderT .* impl)

        variety = \case
          PArrow _ _ -> VArrow
          PForall k _ -> VForall k
          PSpread c _ -> VSpread c

    extensionalEq l r = do
      k <- fromKinding (synthesizeKind l)
      mGuard . not $ isPath l && isPath r
      case k of
        Type -> extEq (`LDat` mempty) (`LMul` mempty) l r
        Simple (_ :*: _) -> extEq (`LFst` mempty) (`LSnd` mempty) l r
        _ :**: _ -> extEq (`LFst` mempty) (`LSnd` mempty) l r
        _ -> emptyErr
      where
        extEq fst snd l r = do
          let parts = liftA2 (liftA2 (,)) (elam . fst) (elam . snd)
              elam = fromKinding . eval . Fix . TLam
          ((lf, ls), (rf, rs)) <- on (liftA2 (,)) parts l r
          impl lf rf *> impl ls rs

        isPath = foldFix $ \case
          TType _ _ -> False
          TLam t -> case t of
            LVar _ -> True
            LApp f _ _ -> f
            LMap f _ _ -> f
            LFst p _ -> p
            LSnd p _ -> p
            LDat t _ -> t
            LMul t _ -> t
            _ -> False
          _ -> True

    mGuard b = if b then pure () else emptyErr

    emptyErr = ReaderT . const $ Err []

    fromKinding :: KindingResult a -> RealEqResult a
    fromKinding = mapCtx fst . mapErr (NonEmpty.toList . fmap EKinding)

type Assumptions = HashSet (Term, Term)

type RealEqResult = CtxResult ([ProperKind], Assumptions) [] EqError

--------------------------------- MU UNFOLDING ---------------------------------

unfoldMuPath :: Term -> Maybe (KindingResult Term)
unfoldMuPath = fmap eval . substitutePath
  where
    substitutePath (Fix t) = case t of
      TLam t -> case t of
        LFix k t p ->
          Just . flip substitute t . SubWith . Fix . TLam $ LFix k t p
        LFst t p -> Fix . TLam . flip LFst p <$> substitutePath t
        LSnd t p -> Fix . TLam . flip LSnd p <$> substitutePath t
        _ -> Nothing
      t -> Nothing
