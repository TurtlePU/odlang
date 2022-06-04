module Core (core) where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (Ap2 (..), FreeBi (..))
import Control.Monad.Result (Result (..), runCtx)
import Core.Type.Equivalence (checkEQ)
import Core.Type.Evaluation (Substitution (..), eval, substitute)
import Core.Type.Kinding (synthesizeKind)
import Core.Type.Syntax
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..))
import Data.Functor.Identity (Identity (..))
import Test.HUnit ((@?=))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

core :: TestTree
core = testGroup "Core" [kinding, typeSubstitution, typeEvaluation, equality]

kinding :: TestTree
kinding =
  testGroup
    "Kinding"
    [ testCase "Identity" $ synth (lid Type) @?= Ok (Type :->: Type),
      testCase "Unit" $ synth unit @?= Ok (Simple Data),
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

typeEvaluation :: TestTree
typeEvaluation =
  testGroup
    "Type evaluation"
    [ testCase "Pruning" $
        eval' (mul . Pure . row . Pure . Identity $ var 0) @?= Ok (var 0),
      testCase "Application" $ eval' (lapp (lid Type) unit) @?= Ok unit
    ]
  where
    eval' = runCtx [] . eval

equality :: TestTree
equality =
  testGroup
    "Type equality"
    [ testCase "Structural" $ eq unit unit @?= Ok (),
      testCase "Mu-Arrows" $
        eq
          (mu Data . arr unit' $ var' 0)
          (mu Data . arr unit' . arr' unit' $ var' 0)
          @?= Ok ()
    ]
  where
    eq l r = runCtx [] $ checkEQ l r

----------------------------- CONSTRUCTOR HELPERS ------------------------------

lam = Fix . TLam

var = lam . LVar

labs k = lam . LAbs k

lapp = curry $ lam . (\(f, x) -> LApp f x mempty)

mu k = lam . flip (LFix k) mempty

lid = flip labs $ var 0

lfst = lam . flip LFst mempty

pair = lam . uncurry LPair

dat = Fix . flip TData mempty

arr d c = dat $ PArrow d c

spread c = dat . PSpread c

record = spread CAnd

unit = record $ remp Type

row = Fix . flip TRow mempty . Join . Biff . FreeBi

remp = row . Free . Ap2 . REmpty

mul = Fix . flip TMul mempty . FreeBi

mlit = mul . Free . Ap2 . MLit . uncurry MultLit

reg = mlit (False, False)

ty d m = Fix . flip TType mempty $ TLit d m

unit' = ty unit reg

var' i = ty (var i) reg

arr' d c = ty (arr d c) reg
