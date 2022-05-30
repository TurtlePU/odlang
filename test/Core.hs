module Core (core) where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import Core.Type.Evaluation (Substitution (..), substitute)
import Core.Type.Kinding (synthesizeKind)
import Core.Type.Syntax
import Data.Aps (Ap2 (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..))
import Data.Result (Result (..), runCtx)
import Test.HUnit ((@?=))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

core :: TestTree
core = testGroup "Core" [kinding, typeSubstitution]

kinding :: TestTree
kinding =
  testGroup
    "Kinding"
    [ testCase "Identity" $ synth (labs Type $ var 0) @?= Ok (Type :->: Type),
      testCase "Unit" $ synth (record $ remp Type) @?= Ok (Simple Data),
      testCase "First" $
        synth (lfst $ pair (mlit (False, True), remp (Simple Data))) @?= Ok Mult
    ]
  where
    synth = runCtx [] . synthesizeKind

typeSubstitution :: TestTree
typeSubstitution =
  testGroup
    "Type substitution"
    [ testCase "Simple" $
        substitute (SubWith (var 1)) (pair (var 1, var (-1)))
          @?= pair (var 0, var (-1))
    ]

----------------------------- CONSTRUCTOR HELPERS ------------------------------

lam = Fix . TLam

var = lam . LVar

labs k = lam . LAbs k

lfst = lam . LFst mempty

pair = lam . uncurry LPair

dat = Fix . TData mempty

spread c = dat . PSpread c

record = spread CAnd

row = Fix . TRow mempty . Join . FreeBi . Free . Ap2

remp = row . REmpty

mul = Fix . TMul mempty

mlit = mul . FreeBi . Free . Ap2 . MLit . uncurry MultLit
