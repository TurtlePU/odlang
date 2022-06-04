{-# LANGUAGE LambdaCase #-}

module Core.Type.Contract where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import Control.Monad.Identity (Identity (..))
import Control.Monad.Result (failWith, mapErrs)
import Core.Type.Evaluation (eval)
import Core.Type.Kinding (KindingError, synthesizeKind)
import Core.Type.Result (TypeResult)
import Core.Type.Syntax
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (foldFix)
import qualified Data.HashSet as HashSet
import Data.Position (Position)

newtype WellFormed = MkWF {unWF :: Term}

data ContractError
  = CKind KindingError
  | CContr Position

wellFormed :: Term -> Position -> TypeResult ContractError WellFormed
wellFormed t =
  if isContractive t
    then failWith . CContr
    else const $ MkWF <$> mapErrs CKind (synthesizeKind t *> eval t)
  where
    isContractive t = areGuarded t HashSet.empty
    areGuarded = foldFix $ \case
      TLam t -> case t of
        LVar i -> not . HashSet.member i
        LAbs _ t -> t . HashSet.map succ
        LFix _ t _ -> t . HashSet.insert 0 . HashSet.map succ
        t -> and . sequence t
      TMul (FreeBi (Pure t)) _ -> t
      TRow (Join (Biff (FreeBi (Pure (Identity t))))) _ -> t
      t -> const . and $ sequence t HashSet.empty
