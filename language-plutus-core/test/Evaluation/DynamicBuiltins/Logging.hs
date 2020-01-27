{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.DynamicBuiltins.Logging
    ( test_logging
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.MkPlc

import           Language.PlutusCore.StdLib.Data.List as Plc
import           Language.PlutusCore.StdLib.Data.Unit

import           Evaluation.DynamicBuiltins.Common

import           Control.Monad.Except
import           Data.Either                          (isRight)
import           Data.Proxy
import           Test.Tasty
import           Test.Tasty.HUnit

dynamicIntegerToStringName :: DynamicBuiltinName
dynamicIntegerToStringName = DynamicBuiltinName "integerToString"

dynamicIntegerToStringMeaning :: DynamicBuiltinNameMeaning
dynamicIntegerToStringMeaning = DynamicBuiltinNameMeaning sch show where
    sch = Proxy @Integer `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicIntegerToString :: Term tyname name ()
dynamicIntegerToString = dynamicBuiltinNameAsTerm dynamicIntegerToStringName

handleDynamicIntegerToString :: OnChainHandler "integerToString" f r r
handleDynamicIntegerToString = handleDynamicByMeaning dynamicIntegerToStringMeaning

evaluateHandlersCek
    :: MonadError (Error ()) m
    => (AnEvaluator (OnChain '[] Term) m EvaluationResultDef -> OnChainEvaluator names Term r)
    -> OnChain names Term TyName Name ()
    -> r
evaluateHandlersCek = evaluateHandlersBy typecheckEvaluateCek

test_logInt :: TestTree
test_logInt = testCase "logInt" $ do
    let term
            = Apply () dynamicLog
            . Apply () dynamicIntegerToString
            $ Constant () (BuiltinInt () 1)

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
            let integer = TyBuiltin () TyInteger
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
                        [ Constant () $ BuiltinInt () 1
                        , Constant () $ BuiltinInt () 10
                        ]
                    ]

    let eval1 = evaluateHandlersCek (handleDynamicIntegerToString . handleDynamicLog)
    let eval2 = evaluateHandlersCek (handleDynamicLog . handleDynamicIntegerToString)
    (logs1, errOrRes1) <- liftIO . eval1 $ OnChain term
    (logs2, errOrRes2) <- liftIO . eval2 $ OnChain term
    isRight errOrRes1 @?= True
    isRight errOrRes2 @?= True
    logs1 @?= map show [1 .. 10 :: Integer]
    logs2 @?= map show [1 .. 10 :: Integer]

test_logging :: TestTree
test_logging =
    testGroup "logging"
        [ test_logInt
        , test_logInts
        ]
