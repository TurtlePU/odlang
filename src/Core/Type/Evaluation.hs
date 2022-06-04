{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Core.Type.Evaluation where

import Control.Applicative (Applicative (liftA2))
import Control.Category ((<<<))
import Control.Composition ((.*), (.@))
import Control.Monad ((<=<))
import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (Ap2 (..), FreeBi (..))
import Control.Monad.Result (mapCtx)
import Core.Type.Kinding (KindingResult, pullArrow, synthesizeKind)
import Core.Type.Syntax
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..), foldFix)
import Data.Function (on)
import Data.Function.Slip (slipl, slipr)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (Identity))

eval :: Term -> KindingResult Term
eval = foldFix $ \case
  TMul t p -> fmap (flip lowerMult p <<< liftMult <=< id) (sequence t)
  TRow t p ->
    fmap (flip lowerRow p <<< liftRow <=< runBiff <<< runJoin) (sequence t)
  TType t p -> Fix . flip TType p <$> sequence t
  TData t p ->
    Fix . flip TData p <$> case t of
      PForall k t -> PForall k <$> mapCtx (k :) t
      d -> sequence d
  TLam t -> case t of
    LAbs k t -> Fix . TLam . LAbs k <$> mapCtx (k :) t
    LFix k t p -> Fix . TLam . flip (LFix k) p <$> mapCtx (Simple k :) t
    t -> sequence t >>= apply
  where
    lowerMult = \case
      FreeBi (Pure t) -> const t
      t -> Fix . TMul t

    lowerRow = \case
      FreeBi (Pure (Identity t)) -> const t
      t -> Fix . TRow (Join $ Biff t)

    apply :: LambdaF Term -> KindingResult Term
    apply = \case
      LApp (Fix (TLam (LAbs _ t))) x _ -> eval $ substitute (SubWith x) t
      LFst (Fix (TLam (LSPair x _ _))) _ -> pure x
      LFst (Fix (TLam (LPair x _))) _ -> pure x
      LSnd (Fix (TLam (LSPair _ x _))) _ -> pure x
      LSnd (Fix (TLam (LPair _ x))) _ -> pure x
      LDat (Fix (TType (TLit d _) _)) _ -> pure d
      LMul (Fix (TType (TLit _ m) _)) _ -> pure m
      LMap f (Fix (TLam (LMap g x q))) p -> do
        h <- compose f g p
        apply $ LMap h x (p <> q)
      LMap f (Fix (TRow (Join (Biff (FreeBi (Free (Ap2 r))))) q)) p ->
        Fix . flip TRow (p <> q) . Join . Biff . FreeBi . Free . Ap2
          <$> case r of
            REmpty _ -> REmpty . snd <$> (synthesizeKind f >>= flip pullArrow p)
            REntry (k, v) -> REntry . (k,) <$> apply (LApp f v p)
            RJoin l r -> on (liftA2 RJoin) recur l r
              where
                recur = fmap (runFreeBi . liftRow . Identity) . apply . wrapRow
                wrapRow = flip (LMap f) p . flip lowerRow q . FreeBi
      LRnd (Fix (TLam (LMap f r q))) p ->
        apply (LRnd r p) >>= apply . flip (LApp f) q
      LRnd (Fix (TRow (Join (Biff (FreeBi (Free (Ap2 r))))) q)) p -> case r of
        REmpty k -> pure . Fix . TLam . flip LRnd p . Fix $ wrapKind k
          where
            wrapKind = flip TRow q . Join . Biff . FreeBi . Free . Ap2 . REmpty
        REntry (_, v) -> pure v
        RJoin l r -> on (liftA2 unifier) recur l r
          where
            recur = apply . flip LRnd p . flip lowerRow q . FreeBi
            unifier _ _ = error "most-precise-unifier is not defined"
      t -> pure . Fix $ TLam t

    compose f g p = do
      (kx, _) <- synthesizeKind g >>= flip pullArrow p
      g' <- apply . flip (LApp $ shift 1 g) p . Fix . TLam $ LVar 0
      f' <- apply $ LApp (shift 1 f) g' p
      pure . Fix . TLam $ LAbs kx f'

liftMult = \case
  Fix (TMul t _) -> t
  t -> FreeBi (Pure t)

liftRow = \case
  Identity (Fix (TRow (Join (Biff t)) _)) -> t
  t -> FreeBi (Pure t)

newtype Substitution = SubWith {unSub :: Term}

substitute :: Substitution -> Term -> Term
substitute = shift (-1) .* slipl replace 0 . SubWith . shift 1 . unSub
  where
    replace (SubWith t) = foldFix $ \case
      TData d p ->
        Fix . flip TData p . case d of
          PForall k b -> PForall k . b . (+ 1)
          d -> sequence d
      TLam b -> case b of
        LVar j -> \i -> if i == j then t else Fix . TLam $ LVar j
        LAbs k b -> Fix . TLam . LAbs k . b . (+ 1)
        LFix k b p -> Fix . TLam . flip (LFix k) p . b . (+ 1)
        b -> Fix . TLam <$> sequence b
      b -> Fix <$> sequence b

newtype Inc = Inc Int

shift :: Int -> Term -> Term
shift = slipl shift' 0 . Inc
  where
    shift' :: Inc -> Term -> Int -> Term
    shift' (Inc inc) = foldFix $ Fix .* \case
      TData d p -> flip TData p . case d of
        PForall k t -> PForall k . t . (+ 1)
        d -> sequence d
      TLam t -> TLam . case t of
        LVar i -> LVar . (i +) . \lo -> if i >= lo then inc else 0
        LAbs k t -> LAbs k . t . (+ 1)
        LFix k t p -> flip (LFix k) p . t . (+ 1)
        t -> sequence t
      t -> sequence t
