{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Evaluation.DynamicBuiltins.Logging
    ( test_logging
    ) where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Evaluator
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty                         (PrettyConst)

import           Language.PlutusCore.StdLib.Data.List               as Plc
import           Language.PlutusCore.StdLib.Data.Unit

import           Evaluation.DynamicBuiltins.Common

import           Control.Monad.Except
import           Data.Proxy
import           Test.Tasty
import           Test.Tasty.HUnit

dynamicIntegerToStringName :: DynamicBuiltinName
dynamicIntegerToStringName = DynamicBuiltinName "integerToString"

dynamicIntegerToStringMeaning
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String)
    => DynamicBuiltinNameMeaning uni
dynamicIntegerToStringMeaning = DynamicBuiltinNameMeaning sch show (\_ -> ExBudget 1 1) where
    sch = Proxy @Integer `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicIntegerToString :: Term tyname name uni ()
dynamicIntegerToString = dynamicBuiltinNameAsTerm dynamicIntegerToStringName

handleDynamicIntegerToString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String)
    => OnChainHandler "integerToString" f uni r r
handleDynamicIntegerToString = handleDynamicByMeaning dynamicIntegerToStringMeaning

evaluateHandlersCek
    :: ( MonadError (Error uni ()) m, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, Typeable uni, uni `Everywhere` PrettyConst
       )
    => (AnEvaluator (OnChain '[] Term) uni m (EvaluationResultDef uni) ->
            OnChainEvaluator names Term uni r)
    -> OnChain names Term TyName Name uni ()
    -> r
evaluateHandlersCek = evaluateHandlersBy typecheckEvaluateCek

test_logInt :: TestTree
test_logInt = testCase "logInt" $ do
    let term
            = Apply () dynamicLog
            . Apply () dynamicIntegerToString
            $ mkConstant @Integer @DefaultUni () 1

    let eval1 = evaluateHandlersCek (handleDynamicIntegerToString . handleDynamicLog)
    let eval2 = evaluateHandlersCek (handleDynamicLog . handleDynamicIntegerToString)
    (logs1, errOrRes1) <- eval1 $ OnChain term
    (logs2, errOrRes2) <- eval2 $ OnChain term
    isRight errOrRes1 @?= True
    isRight errOrRes2 @?= True
    logs1 @?= ["1"]
    logs2 @?= ["1"]

test_logInts :: TestTree
test_logInts = testCase "logInts" $ do
    let term = runQuote $ do
            let integer = mkTyBuiltin @Integer @DefaultUni ()
            u <- freshName () "u"
            x <- freshName () "x"

            return
                $ mkIterApp () (mkIterInst () foldList [integer, unit])
                    [   LamAbs () u unit
                      . LamAbs () x integer
                      . Apply () dynamicLog
                      . Apply () dynamicIntegerToString
                      $ Var () x
                    , unitval
                    , mkIterApp () Plc.enumFromTo
                        [ mkConstant @Integer () 1
                        , mkConstant @Integer () 10
                        ]
                    ]

    let eval1 = evaluateHandlersCek (handleDynamicIntegerToString . handleDynamicLog)
    let eval2 = evaluateHandlersCek (handleDynamicLog . handleDynamicIntegerToString)
    (logs1, errOrRes1) <- liftIO . eval1 $ OnChain term
    (logs2, errOrRes2) <- liftIO . eval2 $ OnChain term
    isRight errOrRes1 @?= True
    isRight errOrRes2 @?= True
    logs1 @?= Prelude.map show [1 .. 10 :: Integer]
    logs2 @?= Prelude.map show [1 .. 10 :: Integer]

test_logging :: TestTree
test_logging =
    testGroup "logging"
        [ test_logInt
        , test_logInts
        ]
