{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Transform.CaseOfCase.Spec where

import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import Data.Vector qualified as V
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.BuiltinCostModel (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting,
                                                          defaultCekMachineCostsForTesting)
import PlutusCore.Evaluation.Machine.MachineParameters (CostModel (..), MachineParameters (..),
                                                        mkMachineVariantParameters)
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)
import PlutusCore.MkPlc (mkConstant, mkIterApp)
import PlutusCore.Pretty
import PlutusCore.Quote (freshName, runQuote)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term (..))
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CekMachineCosts, EvaluationResult (..),
                                                 evaluateCek, noEmitter,
                                                 unsafeSplitStructuralOperational)
import UntypedPlutusCore.Transform.CaseOfCase (caseOfCase)
import UntypedPlutusCore.Transform.Simplifier (evalSimplifier)

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

caseOfCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase1 = runQuote do
  b <- freshName "b"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Constr () 0 []
      false = Constr () 1 []
      alts = V.fromList [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{- | This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size.
-}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase2 = runQuote do
  b <- freshName "b"
  t <- freshName "t"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Var () t
      false = Constr () 1 []
      alts = V.fromList [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{- | Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @Constr 0@ has two parameters, @x@ and @xs@).
-}
caseOfCase3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase3 = runQuote do
  b <- freshName "b"
  x <- freshName "x"
  xs <- freshName "xs"
  f <- freshName "f"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Constr () 0 [Var () x, Var () xs]
      false = Constr () 1 []
      altTrue = Var () f
      altFalse = mkConstant @Integer () 2
      alts = V.fromList [altTrue, altFalse]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{- |

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
@
-}
caseOfCaseWithError :: Term Name DefaultUni DefaultFun ()
caseOfCaseWithError =
  Case
    ()
    ( mkIterApp
        (Force () (Builtin () PLC.IfThenElse))
        [ ((), mkConstant @Bool () True)
        , ((), Constr () 0 []) -- True
        , ((), Constr () 1 []) -- False
        ]
    )
    (V.fromList [mkConstant @() () (), Error ()])

testCaseOfCaseWithError :: TestTree
testCaseOfCaseWithError =
  testCase "Transformation doesn't evaluate error eagerly" do
    let simplifiedTerm = evalCaseOfCase caseOfCaseWithError
    evaluateUplc simplifiedTerm @?= evaluateUplc caseOfCaseWithError

----------------------------------------------------------------------------------------------------
-- Helper functions --------------------------------------------------------------------------------

evalCaseOfCase
  :: Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
evalCaseOfCase term = evalSimplifier $ caseOfCase term

evaluateUplc
  :: UPLC.Term Name DefaultUni DefaultFun ()
  -> EvaluationResult (UPLC.Term Name DefaultUni DefaultFun ())
evaluateUplc = unsafeSplitStructuralOperational . fst <$> evaluateCek noEmitter machineParameters
 where
  costModel :: CostModel CekMachineCosts BuiltinCostModel
  costModel =
      CostModel defaultCekMachineCostsForTesting defaultBuiltinCostModelForTesting

  machineParameters :: DefaultMachineParameters
  machineParameters =
      -- TODO: proper semantic variant. What should def be?
      MachineParameters def $ mkMachineVariantParameters def costModel

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name =
  goldenVsString name ("untyped-plutus-core/test/Transform/CaseOfCase/" ++ name ++ ".golden.uplc")
    . pure
    . BSL.fromStrict
    . encodeUtf8
    . render
    . prettyClassicSimple
    . evalCaseOfCase
