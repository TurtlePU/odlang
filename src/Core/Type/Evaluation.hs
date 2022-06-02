{-# LANGUAGE LambdaCase #-}

module Core.Type.Evaluation where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import Core.Type.Kinding (KindingResult, pullArrow, synthesizeKind)
import Core.Type.Syntax
import Data.Aps (Ap2 (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFix)
import Data.Functor ((<&>))
import Data.Result (mapCtx)

eval :: Term -> KindingResult Term
eval = foldFix $ \case
  TMul p t ->
    sequence t <&> (>>= liftMult) <&> \case
      FreeBi (Pure t) -> t
      t -> Fix $ TMul p t
  TRow p t ->
    sequence t <&> runJoin <&> (>>= liftRow) <&> \case
      FreeBi (Pure t) -> t
      t -> Fix $ TRow p $ Join t
  TType p t -> Fix . TType p <$> sequence t
  TData p t ->
    Fix . TData p <$> case t of
      PForall k t -> PForall k <$> mapCtx (k :) t
      d -> sequence d
  TLam t -> case t of
    LAbs k t -> Fix . TLam . LAbs k <$> mapCtx (k :) t
    LFix p k t -> Fix . TLam . LFix p k <$> mapCtx (Simple k :) t
    t -> sequence t >>= apply
  where
    liftMult (Fix t) = case t of
      TMul _ t -> t
      t -> FreeBi $ Pure $ Fix t
    liftRow (Fix t) = case t of
      TRow _ (Join t) -> t
      t -> FreeBi $ Pure $ Fix t

    apply :: LambdaF Term -> KindingResult Term
    apply = \case
      LApp _ (Fix (TLam (LAbs _ t))) x -> eval $ substitute (SubWith x) t
      LFst _ (Fix (TLam (LSPair _ x _))) -> pure x
      LFst _ (Fix (TLam (LPair x _))) -> pure x
      LSnd _ (Fix (TLam (LSPair _ _ x))) -> pure x
      LSnd _ (Fix (TLam (LPair _ x))) -> pure x
      LDat _ (Fix (TType _ (TLit d _))) -> pure d
      LMul _ (Fix (TType _ (TLit _ m))) -> pure m
      LMap p f (Fix (TLam (LMap q g x))) -> do
        h <- compose p f g
        apply $ LMap (p <> q) h x
      LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (REmpty _))))))) -> do
        (_, ky) <- synthesizeKind f >>= pullArrow p
        fromRow (p <> q) $ REmpty ky
      LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (REntry k v))))))) -> do
        v' <- apply $ LApp p f v
        fromRow (p <> q) $ REntry k v'
      LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (RJoin l r))))))) -> do
        l' <- apply $ LMap p f $ wrapRow q l
        r' <- apply $ LMap p f $ wrapRow q r
        fromRow (p <> q) $
          RJoin (runFreeBi $ liftRow l') (runFreeBi $ liftRow r')
      -- TODO: rounding operational semantics
      t -> pure $ Fix $ TLam t

    compose p f g = do
      (kx, _) <- synthesizeKind g >>= pullArrow p
      g' <- apply $ LApp p (shift 1 g) $ Fix $ TLam $ LVar 0
      f' <- apply $ LApp p (shift 1 f) g'
      pure $ Fix $ TLam $ LAbs kx f'

    wrapRow p = Fix . TRow p . Join . FreeBi
    fromRow p = pure . wrapRow p . Free . Ap2

newtype Substitution = SubWith Term

substitute :: Substitution -> Term -> Term
substitute (SubWith t) = shift (-1) . replace 0 (shift 1 t)
  where
    replace i t (Fix b) = case b of
      TData p d -> Fix $
        TData p $ case d of
          PForall k b -> PForall k $ replace (i + 1) t b
          d -> replace i t <$> d
      TLam b -> case b of
        LVar j | i == j -> t
        LAbs k b -> Fix $ TLam $ LAbs k $ replace (i + 1) t b
        LFix p k b -> Fix $ TLam $ LFix p k $ replace (i + 1) t b
        b -> Fix $ TLam $ replace i t <$> b
      b -> Fix $ replace i t <$> b

shift :: Int -> Term -> Term
shift = shift' 0
  where
    shift' lo inc (Fix t) = Fix $ case t of
      TData p d -> TData p $ case d of
        PForall k t -> PForall k $ shift' (lo + 1) inc t
        d -> shift' lo inc <$> d
      TLam t -> TLam $ case t of
        LVar i | i >= lo -> LVar $ i + inc
        LAbs k t -> LAbs k $ shift' (lo + 1) inc t
        LFix p k t -> LFix p k $ shift' (lo + 1) inc t
        t -> shift' lo inc <$> t
      t -> shift' lo inc <$> t
