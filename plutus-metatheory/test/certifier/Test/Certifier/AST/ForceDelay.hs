module Test.Certifier.AST.ForceDelay where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore

import Data.Text.Encoding qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

import Test.Certifier.AST (testFailure, testSuccess)

-- This would get converted to Error by the full simplifier, but its as
-- useful tests that the decision procedure is agnostic about that.
-- (force (ƛ (delay error) · error)) ==> (ƛ error · error)
testTrivialSuccess1 :: TestTree
testTrivialSuccess1 =
  testSuccess
    "Trivial success"
    ForceDelay
    (Force () (Apply () (LamAbs () (Delay () (Error))) Error))
    (Apply () (LamAbs () Error) Error)

-- FIXME: This isn't yet implemented in the certifier
--  (force [ (force (builtin ifThenElse)) (con bool True) (delay (con integer 1)) (delay (con integer 2)) ] )
-- ==>
-- [ (force (builtin ifThenElse)) (con bool True) (con integer 1) (con integer 2) ]

testIfThenElseSuccess :: TestTree
testIfThenElseSuccess =
  testSuccess
    "ForceDelay over IfThenElse"
    ForceDelay
    (Force ()
        (Apply ()
            (Apply ()
                (Apply ()
                    (Force () (Builtin () PLC.IfThenElse))
                    (mkConstant () (True :: Bool))
                )
                (Delay () (mkConstant () (1 :: Integer)))
            )
            (Delay () (mkConstant () (2 :: Integer)))
        )
    )
    (Apply ()
        (Apply ()
            (Apply ()
                (Force () (Builtin () PLC.IfThenElse))
                (mkConstant () (True :: Bool))
            )
            (mkConstant () (1 :: Integer))
        )
        (mkConstant () (2 :: Integer))
    )

forceDelayASTTests :: TestTree
forceDelayASTTests =
      testGroup "force-delay ast tests"
    [ testTrivialSuccess1

    ]
