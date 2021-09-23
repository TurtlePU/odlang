module Tree where

data Term var
  = TmUnit
  | TmVar var
  | TmAbs var Type (Term var)
  | TmApp (Term var) (Term var)
  deriving (Show)

data Type
  = TyUnit
  | TyArrow Type Type
  deriving (Show)
