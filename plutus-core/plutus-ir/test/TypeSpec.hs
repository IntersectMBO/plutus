module TypeSpec where

import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()

types :: TestNested
types = testNested "types"
    $ map (goldenTypeFromPir topSourcePos pTerm)
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
  ]

typeErrors :: TestNested
typeErrors = testNested "type-errors"
    $ map (goldenTypeFromPirCatch topSourcePos pTerm)
    [ "wrongDataConstrReturnType"
    , "nonSelfRecursive"
    ]
