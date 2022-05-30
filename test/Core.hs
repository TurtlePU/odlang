module Core (core) where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
import Core.Type.Evaluation (Substitution (..), substitute, eval)
import Core.Type.Kinding (synthesizeKind)
import Core.Type.Syntax
import Data.Aps (Ap2 (..))
import Data.Bifunctor.Join (Join (..))
import Data.Fix (Fix (..))
import Data.Result (Result (..), runCtx)
import Test.HUnit ((@?=))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)
import Core.Type.Equivalence (checkEQ)

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
        eval' (mul $ Pure $ row $ Pure $ var 0) @?= Ok (var 0),
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
        eq (mu Data (unit' `arr` var' 0))
           (mu Data (unit' `arr` (unit' `arr'` var' 0))) @?= Ok ()
    ]
  where
    eq l r = runCtx [] $ checkEQ l r

----------------------------- CONSTRUCTOR HELPERS ------------------------------

lam = Fix . TLam

var = lam . LVar

labs k = lam . LAbs k

lapp = curry $ lam . uncurry (LApp mempty)

mu k = lam . LFix mempty k

lid = flip labs $ var 0

lfst = lam . LFst mempty

pair = lam . uncurry LPair

dat = Fix . TData mempty

arr d c = dat $ PArrow d c

spread c = dat . PSpread c

record = spread CAnd

unit = record $ remp Type

row = Fix . TRow mempty . Join . FreeBi

remp = row . Free . Ap2 . REmpty

mul = Fix . TMul mempty . FreeBi

mlit = mul . Free . Ap2 . MLit . uncurry MultLit

reg = mlit (False, False)

ty d m = Fix $ TType mempty $ TLit d m

unit' = ty unit reg

var' i = ty (var i) reg

arr' d c = ty (arr d c) reg
