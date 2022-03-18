{-# LANGUAGE LambdaCase #-}

module Core.Term where

import Control.Arrow ((>>>))
import Core.Kind
import Core.TypeLevel
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty (..))
import Position
import Result
import Control.Monad (forM_)

data RowKey

type RowBag = [(RowKey, Term)]

data Split

data SplitN

data Term
  = TVar Position
  | TAbs Position Int TLTerm Term TLTerm
  | TApp Position Split Term Term
  | TGen Position ProperKind Term TLTerm
  | TInst Position Term TLTerm
  | TAndI Position SplitN RowBag TLTerm
  | TAndE Position Split Term [RowKey] Term
  | TWithI Position RowBag TLTerm
  | TWithE Position Term RowKey
  | TOrI Position RowKey Term TLTerm TLTerm
  | TOrE Position Split Term RowBag

data TypingError
  = Kinding KindingError

type TypingErrors = NonEmpty TypingError

type TypingResult = CtxResult ([ProperKind], [TLTerm]) TypingErrors

synthesizeType :: Term -> TypingResult TLTerm
synthesizeType (TVar _) = CtxR $ \(_, [ty]) -> pure ty
synthesizeType (TAbs p n ty tm mul) = do
  isType ty
  getCtx >>= checkSup' mul
  checkSup' (upperBound' p n) [ty]
  KPretype p . PArrow ty <$> addCtx n ty (synthesizeType tm)
synthesizeType _ = _

getCtx :: TypingResult [TLTerm]
getCtx = CtxR $ pure . snd

addCtx :: Int -> TLTerm -> TypingResult a -> TypingResult a
addCtx n = mapCtx . second . (++) . replicate n

isType :: TLTerm -> TypingResult ()
isType = fromKinding . checkKind (Simple Type)

checkSup' :: TLTerm -> [TLTerm] -> TypingResult ()
checkSup' m = fromKinding . checkSup m

fromKinding :: KindingResult a -> TypingResult a
fromKinding = first (fmap Kinding) . mapCtx fst
