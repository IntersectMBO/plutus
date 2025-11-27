module Test.Certifier.AST.ForceDelay where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Quote (Quote, freshName, runQuote)
import UntypedPlutusCore

import Data.Text.Encoding qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

import Test.Certifier.AST (testFailureItem, testSuccessItem)

{-
    Tests derived from the FD constructors:

(0) force : FD (force z) x x' → FD z (force x) x'
(1) delay : FD z x x' → FD (force z) (delay x) x'
(2) app : FD (z · y') x x' → Translation (FD □) y y' → FD z (x · y) (x' · y')
(3) abs : FD (zipwk z) x x' → FD (z · y) (ƛ x) (ƛ x')
(4) last-delay : Translation (FD □) x x' → FD (force □) (delay x) x'
(5) last-abs : Translation (FD □) x x' → FD (□ · y) (ƛ x) (ƛ x')

-}

-- Simple Force-Delay across a single applied Lambda
-- This would get converted to (con integer 1) by the full simplifier, but its
-- a useful test that the decision procedure is agnostic about that.
-- (force (ƛ (delay (con integer 1)) · (con integer 2)))
-- ==> (ƛ (con integer 1) · (con integer 2))
-- Constructors positive: [0,2,3,4]
simpleSuccessBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleSuccessBefore = runQuote $ do
  x <- freshName "x"
  return
    ( Force
        ()
        ( Apply
            ()
            ( LamAbs
                ()
                x
                (Delay () (mkConstant () (1 :: Integer)))
            )
            (mkConstant () (2 :: Integer))
        )
    )

simpleSuccessAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleSuccessAfter = runQuote $ do
  x <- freshName "x"
  return
    ( Apply
        ()
        (LamAbs () x (mkConstant () (1 :: Integer)))
        (mkConstant () (2 :: Integer))
    )

-- Nested application that reverts to Translation,
-- and then more Force-Delay cleanup
-- also tests the traversal of the applied term
-- (force (delay
--      ((ƛ (force (delay ((ƛ (con Two)) · (con Three))))) · (con One))))
-- ==>
-- ((ƛ ((ƛ (con Two)) · (con Three))) · (con One))
-- Constructors positive: [0,1,2,3,5]
nestedBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nestedBefore = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  return
    ( Force
        ()
        ( Delay
            ()
            ( Apply
                ()
                ( LamAbs
                    ()
                    x
                    ( Apply
                        ()
                        ( LamAbs
                            ()
                            y
                            ( Force
                                ()
                                ( Delay
                                    ()
                                    ((mkConstant () (2 :: Integer)))
                                )
                            )
                        )
                        (mkConstant () (3 :: Integer))
                    )
                )
                (mkConstant () (1 :: Integer))
            )
        )
    )

nestedAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nestedAfter = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  return
    ( Apply
        ()
        ( LamAbs
            ()
            x
            ( Apply
                ()
                ( LamAbs
                    ()
                    y
                    (mkConstant () (2 :: Integer))
                )
                (mkConstant () (3 :: Integer))
            )
        )
        (mkConstant () (1 :: Integer))
    )

-- Force traverses ifThenElse
--  (force [
--          (force (builtin ifThenElse))
--          (con bool True)
--          (delay (con integer 1))
--          (delay (con integer 2))
--          ] )
-- ==>
-- [
--     (force (builtin ifThenElse))
--      (con bool True)
--      (con integer 1)
--      (con integer 2)
-- ]
-- Constructors positive: [6]
ifThenElseSuccessBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
ifThenElseSuccessBefore =
  ( Force
      ()
      ( Apply
          ()
          ( Apply
              ()
              ( Apply
                  ()
                  (Force () (Builtin () PLC.IfThenElse))
                  (mkConstant () (True :: Bool))
              )
              (Delay () (mkConstant () (1 :: Integer)))
          )
          (Delay () (mkConstant () (2 :: Integer)))
      )
  )

ifThenElseSuccessAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
ifThenElseSuccessAfter =
  ( Apply
      ()
      ( Apply
          ()
          ( Apply
              ()
              (Force () (Builtin () PLC.IfThenElse))
              (mkConstant () (True :: Bool))
          )
          (mkConstant () (1 :: Integer))
      )
      (mkConstant () (2 :: Integer))
  )

-- "Negative" tests
-- Deliberately fail each constructor.

-- Just lose a force for no reason
-- Constructors violated: [0]
simpleForceBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleForceBreakBefore = (Force () (mkConstant () (1 :: Integer)))

simpleForceBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleForceBreakAfter = (mkConstant () (1 :: Integer))

-- Extra delay removed.
-- Constructors [0,1,4]
-- Constructors violated: [1]
simpleFailBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleFailBefore =
  ( Force
      ()
      ( Delay
          ()
          (Delay () (mkConstant () (1 :: Integer)))
      )
  )

simpleFailAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleFailAfter = (mkConstant () (1 :: Integer))

-- Traverse an application when you shouldn't -- no matching lambda
-- Constructors violated: [2]
simpleAppBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleAppBreakBefore =
  ( Force
      ()
      ( Apply
          ()
          (Delay () (mkConstant () (1 :: Integer)))
          (mkConstant () (2 :: Integer))
      )
  )

simpleAppBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
simpleAppBreakAfter =
  ( Apply
      ()
      (mkConstant () (1 :: Integer))
      (mkConstant () (2 :: Integer))
  )

-- Traverse an application when you shouldn't -- broken applied term
-- Constructors violated: [2,0]
appTermBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
appTermBreakBefore = runQuote $ do
  x <- freshName "x"
  return
    ( Apply
        ()
        (LamAbs () x (mkConstant () (1 :: Integer)))
        (Force () (mkConstant () (2 :: Integer)))
    )

appTermBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
appTermBreakAfter = runQuote $ do
  x <- freshName "x"
  return
    ( Apply
        ()
        (LamAbs () x (mkConstant () (1 :: Integer)))
        (mkConstant () (2 :: Integer))
    )

-- Traverse a lambda when you shouldn't -- no applied term
-- Constructors violated: [3]
lambdaBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lambdaBreakBefore = runQuote $ do
  x <- freshName "x"
  return
    ( Force
        ()
        (LamAbs () x (Delay () (mkConstant () (1 :: Integer))))
    )

lambdaBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lambdaBreakAfter = runQuote $ do
  x <- freshName "x"
  return (LamAbs () x (mkConstant () (1 :: Integer)))

-- Valid force-delay, but invalid sub-tree change.
-- Constructors violated: [4]
lastDelayBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lastDelayBreakBefore = (Force () (Delay () (mkConstant () (1 :: Integer))))

lastDelayBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lastDelayBreakAfter = (mkConstant () (2 :: Integer))

-- Valid force-delay, but invalid sub-tree change after an abstraction.
-- (force (delay ((ƛ (con-integer 1)) · (con-integer 3))))
-- =|=>
-- ((ƛ (con-integer 2)) · (con-integer 3)))
-- Constructors violated: [5]
lastAbsBreakBefore :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lastAbsBreakBefore = runQuote $ do
  x <- freshName "x"
  return
    ( Force
        ()
        ( Delay
            ()
            ( Apply
                ()
                (LamAbs () x (mkConstant () (1 :: Integer)))
                (mkConstant () (3 :: Integer))
            )
        )
    )
lastAbsBreakAfter :: Term Name PLC.DefaultUni PLC.DefaultFun ()
lastAbsBreakAfter = runQuote $ do
  x <- freshName "x"
  return
    ( Apply
        ()
        (LamAbs () x (mkConstant () (2 :: Integer)))
        (mkConstant () (3 :: Integer))
    )

successItems
  :: [ ( String
       , SimplifierStage
       , Term Name PLC.DefaultUni PLC.DefaultFun ()
       , Term Name PLC.DefaultUni PLC.DefaultFun ()
       )
     ]
successItems =
  [
    ( "Simple one lambda"
    , ForceDelay
    , simpleSuccessBefore
    , simpleSuccessAfter
    )
  ,
    ( "Nested"
    , ForceDelay
    , nestedBefore
    , nestedAfter
    )
  ,
    ( "ifThenElse"
    , ForceDelay
    , ifThenElseSuccessBefore
    , ifThenElseSuccessAfter
    )
  ]
failItems
  :: [ ( String
       , SimplifierStage
       , Term Name PLC.DefaultUni PLC.DefaultFun ()
       , Term Name PLC.DefaultUni PLC.DefaultFun ()
       )
     ]
failItems =
  [
    ( "Simple extra delay"
    , ForceDelay
    , simpleFailBefore
    , simpleFailAfter
    )
  ,
    ( "Simple force break"
    , ForceDelay
    , simpleForceBreakBefore
    , simpleForceBreakAfter
    )
  ,
    ( "Simple app break"
    , ForceDelay
    , simpleAppBreakBefore
    , simpleAppBreakAfter
    )
  ,
    ( "App term break"
    , ForceDelay
    , appTermBreakBefore
    , appTermBreakAfter
    )
  ,
    ( "Lambda break"
    , ForceDelay
    , lambdaBreakBefore
    , lambdaBreakAfter
    )
  ,
    ( "Last delay break"
    , ForceDelay
    , lastDelayBreakBefore
    , lastDelayBreakAfter
    )
  ,
    ( "Last abs break"
    , ForceDelay
    , lastAbsBreakBefore
    , lastAbsBreakAfter
    )
  ]

forceDelayASTTests :: TestTree
forceDelayASTTests =
  testGroup "force-delay ast tests" $
    fmap testSuccessItem successItems
      <> fmap testFailureItem failItems
