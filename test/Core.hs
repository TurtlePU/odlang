module Core (core) where

import Test.Tasty (TestTree, testGroup)

core :: TestTree
core = testGroup "Core" [kinding]

kinding :: TestTree
kinding = testGroup "Kinding" []
