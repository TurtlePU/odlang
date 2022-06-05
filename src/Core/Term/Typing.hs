{-# LANGUAGE LambdaCase #-}

module Core.Term.Typing where

import Control.Composition ((.*), (.**), (.***), (.@), (.@@), (.@@@), (>=>))
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Result
import Core.Term.Syntax
import Core.Type
import Core.Type.Contract (WellFormed (..))
import Core.Type.Equivalence (EqError)
import Core.Type.Evaluation (Substitution (SubWith))
import Core.Type.Kinding (KindingError)
import Core.Type.Result (TypeResult)
import Core.Type.Syntax hiding (Term)
import Data.Array (Array, array, (!))
import Data.Array.ST (runSTArray)
import Data.Bifunctor (Bifunctor (second), bimap)
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..))
import Data.Foldable (traverse_)
import Data.Function.Slip (slipl, slipl4, slipr, slipr4)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty)
import Data.Position (Position)
import Data.Traversable (for)

data TypingError
  = TPull PullError
  | TEq EqError
  | TKind KindingError

type TermResult e = CtxResult ([Kind], [Type]) NonEmpty e

type TypingResult = TermResult TypingError

synthesizeType :: Term -> TypingResult Type
-- ^ TODO: positions
synthesizeType = foldFix $ \case
  TVar -> (\[t] -> t) <$> getGamma
  TAbs t c b m -> do
    getGamma >>= traverse_ (multAboveType m)
    slipr mktype m mempty . PArrow t <$> addGamma (replicate c t) b
  TApp f s x -> splitGamma s f $ \tf -> do
    (d, c) <- fromTR TPull (pullArrow tf mempty)
    intoCheck d x $> c
  TGen k t m -> do
    getGamma >>= traverse_ (multAboveType m)
    slipr mktype m mempty . PForall k <$> mapGamma (k :) (shift 1 <$>) t
  TInst f a -> do
    (k, c) <- f >>= fromTR TPull . flip pullForall mempty
    fromTR TKind $ checkKind k a mempty *> subst (SubWith a) c
  TAndI b s m -> do
    b' <- MkBag <$> splitNGamma s (unBag b)
    traverse_ (multAboveType m) b'
    finishRow CAnd b' mempty m
  TAndE a o s b -> error "TODO"
  TWithI b m -> do
    b' <- for b . uncurry $ mapCtx . second . (***)
    traverse_ (multAboveType m) b'
    finishRow CWith b' mempty m
  TWithE w k -> error "TODO"
  TOrI k v r m -> error "TODO"
  TOrE o s c -> error "TODO"
  where
    multAboveType :: Mult -> Type -> TypingResult ()
    multAboveType = error "TODO"

    finishRow ::
      Connective -> RowBag Type -> Position -> Mult -> TypingResult Type
    finishRow =
      pure .*** (slipl mktype <*>) .* slipl (flip PSpread .* mkRow Type . unBag)

    splitGamma ::
      Split2 -> TypingResult a -> (a -> TypingResult b) -> TypingResult b
    splitGamma = ReaderT .** (slipr4 . uncurry) ((.* (!!!)) . (flip .* finish))
      where
        finish k (l, r) = (runCtx (k, l) >=>) . (runCtx (k, r) .)

    splitNGamma ::
      Traversable f =>
      SplitN ->
      Array Int (f (TypingResult a)) ->
      TypingResult (Array Int (f a))
    splitNGamma =
      ReaderT .* (slipr . uncurry) ((.* (!*!)) . (mapM sequence .** finish))
      where
        finish k t a =
          let n = length t `max` length a
           in array
                (0, n - 1)
                [(i, runCtx (k, t ! i) <$> a ! i) | i <- [0, n - 1]]

    getGamma = ReaderT $ Ok . snd
    addGamma = mapGamma id . (++)
    mapGamma f g = mapCtx (bimap f g)

intoCheck :: Type -> TypingResult Type -> TypingResult ()
intoCheck = flip $ (fromTR TEq .) . checkTypeEQ .@ (>>=)

fromTR :: (e -> TypingError) -> TypeResult e a -> TypingResult a
fromTR = mapCtx fst .* mapErrs
