module Core.Kind where

data SimpleKind
  = Pretype
  | Type
  | SimpleKind :*: SimpleKind
  deriving (Show, Eq)

data ProperKind
  = Simple SimpleKind
  | Mult
  | Row ProperKind
  | ProperKind :**: ProperKind
  | ProperKind :->: ProperKind
  deriving (Show, Eq)
