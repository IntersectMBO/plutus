module PlutusIR.TypeCheck.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()

test_types :: TestTree
test_types =
  runTestNested ["plutus-ir", "test", "PlutusIR", "TypeCheck"] $
    map
      (goldenTypeFromPir topSrcSpan pTerm)
      [ "letInLet"
      , "listMatch"
      , "maybe"
      , "ifError"
      , "mutuallyRecursiveTypes"
      , "mutuallyRecursiveValues"
      , "nonrec1"
      , "nonrec2"
      , "nonrec3"
      , "nonrec4"
      , "nonrec6"
      , "nonrec7"
      , "nonrec8"
      , "rec1"
      , "rec2"
      , "rec3"
      , "rec4"
      , "nonrecToRec"
      , "nonrecToNonrec"
      , "oldLength"
      , "strictValue"
      , "strictNonValue"
      , "strictNonValue2"
      , "strictNonValue3"
      , "strictValueNonValue"
      , "strictValueValue"
      , "strictNonValueDeep"
      , "even3Eval"
      , "sameNameDifferentEnv"
      , "typeLet"
      , "typeLetRec"
      , -- errors
        "wrongDataConstrReturnType"
      , "nonSelfRecursive"
      , "typeLetWrong"
      ]
