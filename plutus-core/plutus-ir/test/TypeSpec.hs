module TypeSpec where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()

test_types :: TestTree
test_types = runTestNestedIn ["plutus-ir/test"] types

types :: TestNested
types = testNested "types"
    $ map (goldenTypeFromPir topSrcSpan pTerm)
  [ "letInLet"
  ,"listMatch"
  ,"maybe"
  ,"ifError"
  ,"mutuallyRecursiveTypes"
  ,"mutuallyRecursiveValues"
  ,"nonrec1"
  ,"nonrec2"
  ,"nonrec3"
  ,"nonrec4"
  ,"nonrec6"
  ,"nonrec7"
  ,"nonrec8"
  ,"rec1"
  ,"rec2"
  ,"rec3"
  ,"rec4"
  ,"nonrecToRec"
  ,"nonrecToNonrec"
  ,"oldLength"
  ,"strictValue"
  ,"strictNonValue"
  ,"strictNonValue2"
  ,"strictNonValue3"
  ,"strictValueNonValue"
  ,"strictValueValue"
  ,"strictNonValueDeep"
  ,"even3Eval"
  ,"sameNameDifferentEnv"
  , "typeLet"
  , "typeLetRec"
  ]

test_typeErrors :: TestTree
test_typeErrors = runTestNestedIn ["plutus-ir/test"] typeErrors

typeErrors :: TestNested
typeErrors = testNested "type-errors"
    $ map (goldenTypeFromPir topSrcSpan pTerm)
    [ "wrongDataConstrReturnType"
    , "nonSelfRecursive"
    , "typeLet"
    ]
