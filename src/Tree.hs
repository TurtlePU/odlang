{-# LANGUAGE DeriveTraversable #-}

module Tree where

import Data.Bifunctor (Bifunctor (..))

data Term info var
  = TmUnit info
  | TmVar info var
  | TmAbs info var (Type info) (Term info var)
  | TmApp info (Term info var) (Term info var)
  deriving (Show)

instance Bifunctor Term where
  bimap fi fv (TmUnit i) = TmUnit (fi i)
  bimap fi fv (TmVar i v) = TmVar (fi i) (fv v)
  bimap fi fv (TmAbs i v ty tm) = TmAbs (fi i) (fv v) (fi <$> ty) (bimap fi fv tm)
  bimap fi fv (TmApp i f x) = TmApp (fi i) (bimap fi fv f) (bimap fi fv x)

tmInfo :: Term info var -> info
tmInfo (TmUnit info) = info
tmInfo (TmVar info _) = info
tmInfo (TmAbs info _ _ _) = info
tmInfo (TmApp info _ _) = info

data Type info
  = TyUnit info
  | TyArrow info (Type info) (Type info)
  deriving (Show, Functor, Foldable, Traversable)

tyInfo :: Type info -> info
tyInfo (TyUnit info) = info
tyInfo (TyArrow info _ _) = info
