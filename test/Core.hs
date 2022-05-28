module Core (core) where

import Control.Monad.Free (Free (..))
import Control.Monad.FreeBi (FreeBi (..))
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
core = testGroup "Core" [kinding]

kinding :: TestTree
kinding =
  testGroup
    "Kinding"
    [ testCase "Identity" $ synth (abs Type $ var 0) @?= Ok (Type :->: Type),
      testCase "Unit" $ synth (record $ rem Type) @?= Ok (Simple Data),
      testCase "First" $
        synth (fst $ pair (mlit (False, True), rem (Simple Data))) @?= Ok Mult
    ]
  where
    synth = runCtx [] . synthesizeKind
    lam = Fix . TLam
    var = lam . LVar
    abs k = lam . LAbs k
    fst = lam . LFst mempty
    pair = lam . uncurry LPair
    dat = Fix . TData mempty
    spread c = dat . PSpread c
    record = spread CAnd
    row = Fix . TRow mempty . Join . FreeBi . Free . Ap2
    rem = row . REmpty
    mul = Fix . TMul mempty
    mlit = mul . FreeBi . Free . Ap2 . MLit . uncurry MultLit
