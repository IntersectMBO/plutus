module Spec.MultiSigStateMachine(tests) where

import qualified Spec.Size        as Size
import           Test.Tasty       (TestTree, testGroup)
import qualified Test.Tasty.HUnit as HUnit

import qualified Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MS

tests :: TestTree
tests = testGroup "multi sig state machine tests" [
    let val = MS.validator (MS.Params [] 100) in
    HUnit.testCase "script size is reasonable" (Size.reasonable val 300000)
    ]
