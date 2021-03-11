module TypeSpec where

import           Common
import           TestLib

import           PlutusIR.Parser
import           PlutusIR.Transform.Rename ()

types :: TestNested
types = testNested "types"
    $ map (goldenTypeFromPir topSourcePos term)
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
  ,"even3Eval"
  ,"sameNameDifferentEnv"
  ]

typeErrors :: TestNested
typeErrors = testNested "type-errors"
    $ map (goldenTypeFromPirCatch topSourcePos term)
    [ "wrongDataConstrReturnType"
    , "nonSelfRecursive"
    ]
