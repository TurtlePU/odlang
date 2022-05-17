{-# LANGUAGE LambdaCase #-}

module Core.Type.Evaluation where

import Control.Monad ((>=>))
import Control.Monad.Bifree (Bifree (..), bilift)
import Control.Monad.Free (Free (..), iterA)
import Control.Monad.FreeBi (FreeBi (..))
import Control.Monad.Quad (Quad (..))
import Core.Type.Kinding (KindingResult, pullArrow, synthesizeKind)
import Core.Type.Syntax
import Data.Aps (Ap (..), Ap2 (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFixM)
import Data.Position (Position)

eval :: Term -> KindingResult Term
eval = foldFixM $ \case
  TMul p t -> pure $ case t >>= liftMult of
    FreeBi (Pure t) -> t
    t -> Fix $ TMul p t
  TRow p (Join t) -> pure $ case t >>= liftRow of
    FreeBi (Pure t) -> t
    t -> Fix $ TRow p $ Join t
  TType p (Join (Quad t)) -> pure $ case bilift liftType liftData t of
    BPure t -> t
    t -> Fix $ TType p $ Join $ Quad t
  TData p (Join (Quad t)) -> pure $ case bilift liftData liftType t of
    BPure t -> t
    t -> Fix $ TData p $ Join $ Quad t
  TLam t -> iterA (sequenceA >=> apply) (t >>= liftLam)
  where
    liftMult (Fix t) = case t of
      TMul _ t -> t
      t -> FreeBi $ Pure $ Fix t
    liftType (Fix t) = case t of
      TType _ (Join (Quad t)) -> t
      t -> BPure $ Fix t
    liftData (Fix t) = case t of
      TData _ (Join (Quad t)) -> t
      t -> BPure $ Fix t

liftRow (Fix t) = case t of
  TRow _ (Join t) -> t
  t -> FreeBi $ Pure $ Fix t

liftLam (Fix t) = case t of
  TLam t -> t
  t -> Pure $ Fix t

apply :: LambdaF Term -> KindingResult Term
apply = \case
  LApp _ (Fix (TLam (Free (LAbs _ t)))) x -> _
  LFst _ (Fix (TLam (Free (LSPair _ x _)))) -> pure $ Fix $ TLam x
  LFst _ (Fix (TLam (Free (LPair x _)))) -> pure $ Fix $ TLam x
  LSnd _ (Fix (TLam (Free (LSPair _ _ x)))) -> pure $ Fix $ TLam x
  LSnd _ (Fix (TLam (Free (LPair _ x)))) -> pure $ Fix $ TLam x
  LDat _ (Fix (TType _ (Join (Quad (BFree (Ap (Ap2 (TLit p d _)))))))) ->
    pure $ Fix $ TData p $ Join $ Quad d
  LMul _ (Fix (TType _ (Join (Quad (BFree (Ap (Ap2 (TLit p _ m)))))))) ->
    pure $ Fix $ TMul p m
  LMap p f (Fix (TLam (Free (LMap q g x)))) -> do
    h <- compose p f $ Fix (TLam g)
    apply $ LMap (p <> q) h (Fix (TLam x))
  -- TODO: OpMapID rule
  LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (REmpty _))))))) -> do
    (_, ky) <- synthesizeKind f >>= pullArrow p
    fromRow (p <> q) $ REmpty ky
  LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (REntry k v))))))) -> do
    v' <- apply $ LApp p f v
    fromRow (p <> q) $ REntry k v'
  LMap p f (Fix (TRow q (Join (FreeBi (Free (Ap2 (RJoin l r))))))) -> do
    l' <- apply $ LMap p f $ wrapRow q l
    r' <- apply $ LMap p f $ wrapRow q r
    fromRow (p <> q) $ RJoin (runFreeBi $ liftRow l') (runFreeBi $ liftRow r')
  t -> _
  where
    compose :: Position -> Term -> Term -> KindingResult Term
    compose p f g = do
      (kx, _) <- synthesizeKind g >>= pullArrow p
      g' <- apply $ LApp p (shift g) $ Fix $ TLam $ Free $ LVar 0
      f' <- apply $ LApp p (shift f) g'
      pure $ Fix $ TLam $ Free $ LAbs kx $ liftLam f'

    wrapRow p = Fix . TRow p . Join . FreeBi

    fromRow p = pure . wrapRow p . Free . Ap2
