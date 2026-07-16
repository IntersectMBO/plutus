{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeApplications #-}

module Transform.CaseOfCase.Spec where

import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.BuiltinCostModel (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
  ( defaultBuiltinCostModelForTesting
  , defaultCekMachineCostsForTesting
  )
import PlutusCore.Evaluation.Machine.MachineParameters
  ( CostModel (..)
  , MachineParameters (..)
  , mkMachineVariantParameters
  )
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Pretty
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))
import Transform.Lib (builtinTrue, case_, con, constr, err, ite, sopFalse, sopTrue, var)
import UntypedPlutusCore (DefaultBuiltinPattern, DefaultFun, DefaultUni, Name, Term (..))
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
  ( CekMachineCosts
  , EvaluationResult (..)
  , evaluateCek
  , noEmitter
  , unsafeSplitStructuralOperational
  )
import UntypedPlutusCore.Transform.CaseOfCase (caseOfCase)
import UntypedPlutusCore.Transform.Optimizer (evalOptimizer)

test_caseOfCase :: TestTree
test_caseOfCase =
  testGroup
    "CaseOfCase"
    [ goldenVsSimplified "1" caseOfCase1
    , goldenVsSimplified "2" caseOfCase2
    , goldenVsSimplified "3" caseOfCase3
    , goldenVsSimplified "withError" caseOfCaseWithError
    , testCaseOfCaseWithError
    ]

caseOfCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun PLC.DefaultBuiltinPattern ()
caseOfCase1 =
  case_
    (ite (var "b") sopTrue sopFalse)
    [ con 1 -- True branch
    , con 2 -- False branch
    ]

{-| This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size. -}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun PLC.DefaultBuiltinPattern ()
caseOfCase2 = case_ (ite (var "b") (var "t") sopFalse) [con 1, con 2]

{-| Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @constr 0@ has two parameters, @x@ and @xs@). -}
caseOfCase3 :: Term Name PLC.DefaultUni PLC.DefaultFun PLC.DefaultBuiltinPattern ()
caseOfCase3 =
  case_
    (ite (var "b") (constr 0 [var "x", var "xs"]) sopFalse)
    [var "f", con 2]

{-|

@
  case (force ifThenElse) True True False of
    True -> ()
    False -> _|_
@

Evaluates to `()` because the first case alternative is selected.
(The _|_ is not evaluated because case alternatives are evaluated lazily).

After the `CaseOfCase` transformation the program should evaluate to `()` as well.

@
  force ((force ifThenElse) True (delay ()) (delay _|_))
@ -}
caseOfCaseWithError :: Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()
caseOfCaseWithError = case_ (ite builtinTrue sopTrue sopFalse) [mkConstant @() () (), err]

testCaseOfCaseWithError :: TestTree
testCaseOfCaseWithError =
  testCase "Transformation doesn't evaluate error eagerly" do
    let simplifiedTerm = evalCaseOfCase caseOfCaseWithError
    evaluateUplc simplifiedTerm @?= evaluateUplc caseOfCaseWithError

----------------------------------------------------------------------------------------------------
-- Helper functions --------------------------------------------------------------------------------

evalCaseOfCase
  :: Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()
  -> Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()
evalCaseOfCase term = evalOptimizer $ caseOfCase term

evaluateUplc
  :: UPLC.Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()
  -> EvaluationResult (UPLC.Term Name DefaultUni DefaultFun DefaultBuiltinPattern ())
evaluateUplc = unsafeSplitStructuralOperational . fst <$> evaluateCek noEmitter machineParameters
  where
    costModel :: CostModel CekMachineCosts BuiltinCostModel
    costModel =
      CostModel defaultCekMachineCostsForTesting defaultBuiltinCostModelForTesting

    machineParameters :: DefaultMachineParameters
    machineParameters =
      -- TODO: proper semantic variant. What should def be?
      MachineParameters def def $ mkMachineVariantParameters def costModel

goldenVsSimplified
  :: String -> Term Name PLC.DefaultUni PLC.DefaultFun PLC.DefaultBuiltinPattern () -> TestTree
goldenVsSimplified testName =
  goldenVsString
    testName
    ("untyped-plutus-core/test/Transform/CaseOfCase/" ++ testName ++ ".golden.uplc")
    . pure
    . BSL.fromStrict
    . encodeUtf8
    . render
    . prettyClassicSimple
    . evalCaseOfCase
