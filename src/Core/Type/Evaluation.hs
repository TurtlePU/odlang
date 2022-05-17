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
import Data.Fix (Fix (..), foldFix)
import Data.Position (Position)

eval :: Term -> KindingResult Term
eval = foldFix $ \case
  TMul p t -> do
    t' <- sequenceA t
    pure $ case t' >>= liftMult of
      FreeBi (Pure t) -> t
      t -> Fix $ TMul p t
  TRow p t -> do
    Join t' <- sequenceA t
    pure $ case t' >>= liftRow of
      FreeBi (Pure t) -> t
      t -> Fix $ TRow p $ Join t
  TType p t -> do
    Join (Quad t') <- sequenceA t -- TODO: respect context
    pure $ case bilift liftType liftData t' of
      BPure t -> t
      t -> Fix $ TType p $ Join $ Quad t
  TData p t -> do
    Join (Quad t') <- sequenceA t -- TODO: respect context
    pure $ case bilift liftData liftType t' of
      BPure t -> t
      t -> Fix $ TData p $ Join $ Quad t
  TLam t -> apply t
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

    apply :: LambdaF (KindingResult Term) -> KindingResult Term
    apply = \case
      LApp _ (Fix (TLam (LAbs _ t))) x -> runSubstitution (SubWith x) t
      LFst _ (Fix (TLam (LSPair _ x _))) -> pure x
      LFst _ (Fix (TLam (LPair x _))) -> pure x
      LSnd _ (Fix (TLam (LSPair _ _ x))) -> pure x
      LSnd _ (Fix (TLam (LPair _ x))) -> pure x
      LDat _ (Fix (TType _ (Join (Quad (BFree (Ap (Ap2 (TLit p d _)))))))) ->
        pure $ Fix $ TData p $ Join $ Quad d
      LMul _ (Fix (TType _ (Join (Quad (BFree (Ap (Ap2 (TLit p _ m)))))))) ->
        pure $ Fix $ TMul p m
      LMap p f (Fix (TLam (LMap q g x))) -> do
        h <- compose p f g
        apply $ LMap (p <> q) h x
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
        fromRow (p <> q) $
          RJoin (runFreeBi $ liftRow l') (runFreeBi $ liftRow r')
      t -> pure $ Fix $ TLam t

    compose p f g = do
      (kx, _) <- synthesizeKind g >>= pullArrow p
      g' <- apply $ LApp p (shift 1 g) $ Fix $ TLam $ LVar 0
      f' <- apply $ LApp p (shift 1 f) g'
      pure $ Fix $ TLam $ LAbs kx f'

    wrapRow p = Fix . TRow p . Join . FreeBi
    fromRow p = pure . wrapRow p . Free . Ap2

newtype Substitution = SubWith Term

runSubstitution :: Substitution -> Term -> KindingResult Term
runSubstitution (SubWith t) = eval . shift (-1) . replace 0 (shift 1 t)
  where
    replace i t (Fix b) = case b of
      TMul p b -> Fix $ TMul p $ replace i t <$> b
      TRow p r -> Fix $ TRow p $ replace i t <$> r
      TType p u -> Fix $ TType p _
      TData p d -> Fix $ TData p _
      TLam b -> _

shift :: Int -> Term -> Term
shift = shift' 0
  where
    shift' lo inc (Fix t) = Fix $ case t of
      TMul p t -> TMul p $ shift' lo inc <$> t
      TRow p r -> TRow p $ shift' lo inc <$> r
      TType p t -> TType p _
      TData p d -> TData p _
      TLam t -> TLam _
