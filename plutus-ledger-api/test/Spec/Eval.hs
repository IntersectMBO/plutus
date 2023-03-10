-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module Spec.Eval (tests) where

import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.MkPlc
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.EvaluationContext (evalCtxForTesting)
import PlutusLedgerApi.V1 as Api
import UntypedPlutusCore as UPLC

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

-- (delay outOfScope)
-- Interesting example because it is a delayed value, which would definitely blow up if forced.
-- The evaluation result (success or failure) depends on how the machine handles `dischargeCekValue`.
outDelay :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outDelay = Delay () outOfScope

-- (lam x outOfScope)
-- Interesting example because it is a lambda (delayed) value, which would definitely blow up if applied.
-- The evaluation result (success or failure) depends on how the machine handles `dischargeCekValue`.
outLam :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outLam = mkLam outOfScope

-- [(lam x (lam y x)) (con bool True) (lam x outOfScope)]
-- Interesting example because it is a `const x y` where x is a value and y is out-of-scope.
-- The evaluation result (success or failure) depends on how the machine
-- ignores  the irrelevant to the computation) part of the environment.
outConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outConst = mkIterApp () (mkLam $ mkLam $ Var () $ DeBruijn 2) [true, outLam]

-- [(force (builtin ifThenElse)) (con bool True) (con bool True) outOfScope]
-- Both branches are evaluate *before* the predicate, so it is clear that this should fail in every case.
outITEStrict :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outITEStrict = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , true -- then
         , outOfScope -- else
         ]
-- [(force (builtin ifThenElse)) (con bool True) (delay true) (delay outOfScope)]
-- The branches are *lazy*. The evaluation result (success or failure) depends on how the machine
-- ignores  the irrelevant to the computation) part of the environment.
outITELazy :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outITELazy = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , Delay () true -- then
         , Delay () outOfScope -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (con bool  True) (con unit ())]
-- Note that the branches have **different** types. The machine cannot catch such a type error.
illITEStrict :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITEStrict = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , true -- then
         , unit -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (lam x (con bool  True)) (lam x (con unit ()))]
-- The branches are *lazy*. Note that the branches have **different** types. The machine cannot catch such a type error.
illITELazy :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITELazy = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , mkLam true -- then
         , Delay () true -- else
         ]
-- [(builtin addInteger) (con integer 1) (con unit ())]
-- Interesting because it involves a runtime type-error of a builtin.
illAdd :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illAdd = mkIterApp ()
         (Builtin () AddInteger)
         [ one
         , unit
         ]

-- [(builtin addInteger) (con integer 1) (con integer 1) (con integer 1)]
-- Interesting because it involves a (builtin) over-saturation type-error, which the machine can recognize.
illOverSat :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illOverSat = mkIterApp ()
             (Builtin () AddInteger)
             [ one
             , one
             , one]

-- [(lam x x) (con integer 1) (con integer 1)]
-- Interesting because it involves a (lambda) over-saturation type-error, which the machine can recognize.
illOverApp :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illOverApp = mkIterApp ()
             (mkLam $ Var () $ DeBruijn 1) -- id
             [ one
             , one
             ]

illTypedPartialBuiltin :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illTypedPartialBuiltin = Apply () (Builtin () AddInteger) (mkConstant () True)

-- Evaluates using the Scripts module.
testScripts :: TestTree
testScripts = "v1-scripts" `testWith` evalAPI vasilPV

{-| Evaluates scripts as they will be evaluated on-chain, by using the evaluation function we provide for the ledger.
Notably, this goes via serialising and deserialising the program, so we can see any errors that might arise from that.
-}
testAPI :: TestTree
testAPI = "v1-api" `testWith` evalAPI vasilPV

evalAPI :: ProtocolVersion -> UPLC.Term DeBruijn DefaultUni DefaultFun () -> Bool
evalAPI pv t =
    -- handcraft a serialised script
    let s :: SerialisedScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 t
    in isRight $ snd $ Api.evaluateScriptRestricting pv Quiet evalCtxForTesting (unExRestrictingBudget enormousBudget) s []

-- Test a given eval function against the expected results.
testWith :: String -> (UPLC.Term DeBruijn DefaultUni DefaultFun () -> Bool) -> TestTree
testWith str evalFn = testCase str $ do
    evalFn outDelay @?= False
    evalFn outLam @?= False
    evalFn outConst @?= False
    evalFn outITEStrict @?= False
    evalFn outITELazy @?= False
    evalFn illITEStrict @?= True
    evalFn illITELazy @?= True
    evalFn illAdd @?= False
    evalFn illOverSat @?= False
    evalFn illOverApp @?= False

testUnlifting :: TestTree
testUnlifting = testCase "check unlifting behaviour changes in Vasil" $ do
    -- This used to behave differently but was changed, this witnesses the change
    evalAPI alonzoPV illTypedPartialBuiltin @?= True
    evalAPI vasilPV illTypedPartialBuiltin @?= True

tests :: TestTree
tests = testGroup "eval"
            [ testScripts
            , testAPI
            , testUnlifting
            ]

true :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
true = mkConstant @Bool () True

one :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
one = mkConstant @Integer () 1

unit :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
unit = mkConstant @() () ()

-- a helper to intro a lam, debruijn binders are always 0-indexed
mkLam :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
mkLam = LamAbs () (DeBruijn 0)

-- a sufficient large debruijn index for testing
outOfScope :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outOfScope = Var () (DeBruijn 9999999)
