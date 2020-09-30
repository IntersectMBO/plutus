module TypeSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename ()

types :: TestNested
types = testNested "types"
    $ map (goldenTypeFromPir term)
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
    $ map (goldenTypeFromPirCatch term)
    [ "wrongDataConstrReturnType"
    , "nonSelfRecursive"
    ]
