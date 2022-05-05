module Core.Pretype where

import Core.Kind (ProperKind)
import Core.Multiplicity (MultTerm)
import Core.Row (RowTerm)

data Connective = CAnd | CWith | COr deriving (Show)

data TypeTerm p r m t
  = TVar t
  | TLit (PreTypeT p r m t) (MultTerm m)

data PreTypeT p r m t
  = PVar p
  | PArrow (TypeTerm p r m t) (TypeTerm p r m t)
  | PForall ProperKind (TypeTerm p r m t)
  | PSpread Connective (RowTerm r (TypeTerm p r m t))
