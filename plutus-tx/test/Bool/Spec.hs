module Bool.Spec (boolTests) where

import PlutusTx.Bool qualified as Tx
import PlutusTx.Builtins as Tx

import Test.Tasty
import Test.Tasty.HUnit
import Prelude (($))

boolTests :: TestTree
boolTests =
  testGroup
    "PlutusTx.Bool tests"
    -- in uplc the &&,|| are treated specially to short-circuit
    -- this makes sures that the Haskell counterparts also short-circuit
    [ testCase "shortcircuit_&&" $ Tx.False Tx.&& Tx.error () @?= Tx.False
    , testCase "shortcircuit_||" $ Tx.True Tx.|| Tx.error () @?= Tx.True
    ]
