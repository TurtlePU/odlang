{-# LANGUAGE DeriveTraversable #-}

module Tree where

data TermRec var ty tm
    = TmUnit
    | TmVar var
    | TmAbs var ty tm
    | TmApp tm tm
    | TmTyAbs var tm
    | TmTyApp tm ty
    deriving (Functor, Foldable, Traversable)

data TypeRec var ty
    = TyUnit
    | TyVar var
    | TyArrow ty ty
    | TyForall var ty
    deriving (Functor, Foldable, Traversable)
