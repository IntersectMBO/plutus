-- editorconfig-checker-disable-file
{-# LANGUAGE TypeFamilies #-}
module Spec.Eval (tests) where

import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.MkPlc
import PlutusCore.StdLib.Data.Unit
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.EvaluationContext (evalCtxForTesting)
import PlutusLedgerApi.V1 as Api
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Test.DeBruijn.Bad
import UntypedPlutusCore.Test.DeBruijn.Good

import Data.Either
import Test.Tasty
import Test.Tasty.HUnit

{- NOTE [Direct UPLC code]
For this test-suite we write the programs directly in the UPLC AST,
bypassing the GHC typechecker & compiler, the PIR typechecker & compiler and the PLC typechecker.
The reason is that users can submit such hand-crafted code, and we want to test how it behaves.
Because this is part of our API, we have to be careful not to change the behaviour of even weird untypeable programs.
In particular, We test both the offline part (Scripts module) and the online part (API module).
-}

type T = Term DeBruijn DefaultUni DefaultFun ()

-- | Evaluates using the Scripts module.
testScripts :: TestTree
testScripts = "v1-scripts" `testWith` evalAPI vasilPV

{-| Evaluates scripts as they will be evaluated on-chain, by using the evaluation function we provide for the ledger.
Notably, this goes via serialising and deserialising the program, so we can see any errors that might arise from that.
-}
testAPI :: TestTree
testAPI = "v1-api" `testWith` evalAPI vasilPV

evalAPI :: ProtocolVersion -> T -> Bool
evalAPI pv t =
    -- handcraft a serialised script
    let s :: SerialisedScript = serialiseUPLC $ Program () PLC.plcVersion100 t
    in isRight $ snd $ Api.evaluateScriptRestricting pv Quiet evalCtxForTesting (unExRestrictingBudget enormousBudget) s []

{-| Test a given eval function against the expected results.
These tests are modified from untyped-plutus-core-test:Evaluation.FreeVars
to accommodate the fact that the eval functions in the API
will do prior conformance checking (i.e. deserialization and scope checking).
-}
testWith :: String -> (T -> Bool) -> TestTree
testWith str evalFn = testGroup str $ fmap (uncurry testCase)
    [("delay0", evalFn (Delay () $ Var () $ DeBruijn 0) @?= False) -- fails at scopechecking
    ,("fun0var0", evalFn fun0var0 @?= False) -- fails at scopechecking
    ,("const0var0", evalFn (const0 @@ [unitval, fun0var0]) @?= False) -- fails at scopechecking
    ,("iteLazy0" , evalFn iteLazy0 @?= False) -- fails at scopechecking
    ,("iteStrict0", evalFn iteStrict0 @?= False) -- fails at scopechecking
    ,("illITELazy", evalFn illITELazy @?= True) -- a type error that the machine cannot catch
    ,("illITEStrict", evalFn illITEStrict @?= True) -- a type error that the machine cannot catch
    ,("illAdd", evalFn illAdd @?= False) -- type error is caught by the machine
    ,("illOverAppBuiltin", evalFn illOverAppBuiltin @?= False) -- type error is caught by the machine
    ,("illOverAppFun", evalFn illOverAppFun @?= False) -- type error is caught by the machine
    ]

testUnlifting :: TestTree
testUnlifting = testCase "check unlifting behaviour changes in Vasil" $ do
    -- Before Vasil the behavior of this was different, but since the behavior was never
    -- exercised on chain, it was safe to be switched to the new behavior (jedi mind trick).
    evalAPI alonzoPV illPartialBuiltin @?= True
    evalAPI vasilPV illPartialBuiltin @?= True

tests :: TestTree
tests = testGroup "eval"
            [ testScripts
            , testAPI
            , testUnlifting
            ]
