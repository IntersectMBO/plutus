{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Transform.CaseOfCase.Test where

import Data.Vector qualified as V
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.BuiltinCostModel (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel,
                                                          defaultCekMachineCosts)
import PlutusCore.Evaluation.Machine.MachineParameters (CostModel (..), MachineParameters,
                                                        mkMachineParameters)
import PlutusCore.MkPlc (mkConstant, mkIterApp)
import PlutusCore.Quote (freshName, runQuote, runQuoteT)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Transform.Simplify.Lib (goldenVsSimplified)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term (..), defaultSimplifyOpts,
                          simplifyTerm)
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CekMachineCosts, CekValue, EvaluationResult (..),
                                                 noEmitter, unsafeEvaluateCek)

test_caseOfCase :: TestTree
test_caseOfCase =
  testGroup
    "CaseOfCase"
    [ goldenVsSimplified "CaseOfCase/1" caseOfCase1
    , goldenVsSimplified "CaseOfCase/2" caseOfCase2
    , goldenVsSimplified "CaseOfCase/3" caseOfCase3
    , caseOfCaseWithError
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

caseOfCaseWithError :: TestTree
caseOfCaseWithError =
  testCase "Transformation doesn't evaluate error eagerly" do
    let
      originalTerm =
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
    simplifiedTerm <- runQuoteT $ simplifyTerm defaultSimplifyOpts def originalTerm
    evaluateUplc simplifiedTerm @?= evaluateUplc originalTerm

evaluateUplc
  :: UPLC.Term Name DefaultUni DefaultFun ()
  -> EvaluationResult (UPLC.Term Name DefaultUni DefaultFun ())
evaluateUplc = fst <$> unsafeEvaluateCek noEmitter machineParameters
 where
  costModel :: CostModel CekMachineCosts BuiltinCostModel =
    CostModel defaultCekMachineCosts defaultBuiltinCostModel
  machineParameters
    :: MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ()) =
      mkMachineParameters def costModel
