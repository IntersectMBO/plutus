{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Logging
    ( test_logging
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Unit

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.IO.Class
import           Data.Functor.Identity
import           Test.Tasty
import           Test.Tasty.HUnit

handleDynamicIntToString :: OnChainHandler "intToString" f r r
handleDynamicIntToString = handleDynamicByMeaning dynamicIntToStringMeaning

evaluateHandlersCek
    :: (Evaluator (OnChain '[] Term) Identity -> OnChainEvaluator names Term r)
    -> OnChain names Term TyName Name ()
    -> r
evaluateHandlersCek = evaluateHandlersBy (\means -> Identity . evaluateCek means)

test_logInt :: TestTree
test_logInt = testCase "logInt" $ do
    let size = 4
        term
            = Apply () dynamicLog
            . Apply () (TyInst () dynamicIntToString (TyInt () size))
            $ Constant () (BuiltinInt () size 1)

    let eval1 = evaluateHandlersCek (handleDynamicIntToString . handleDynamicLog)
    let eval2 = evaluateHandlersCek (handleDynamicLog . handleDynamicIntToString)
    (logs1, _) <- eval1 $ OnChain term
    (logs2, _) <- eval2 $ OnChain term
    logs1 @?= ["1"]
    logs2 @?= ["1"]

test_logInts :: TestTree
test_logInts = testCase "logInts" $ do
    let term = runQuote $ do
            let size = 4
                int4 = TyApp () (TyBuiltin () TyInteger) (TyInt () size)
            unit         <- getBuiltinUnit
            unitval      <- getBuiltinUnitval
            foldList     <- getBuiltinFoldList
            biEnumFromTo <- getBuiltinEnumFromTo
            u <- freshName () "u"
            x <- freshName () "x"

            return
                $ mkIterApp () (mkIterInst () foldList [int4, unit])
                    [   LamAbs () u unit
                      . LamAbs () x int4
                      . Apply () dynamicLog
                      . Apply () (TyInst () dynamicIntToString (TyInt () size))
                      $ Var () x
                    , unitval
                    , mkIterApp () (TyInst () biEnumFromTo (TyInt () size))
                        [ Constant () $ BuiltinInt () size 1
                        , Constant () $ BuiltinInt () size 10
                        ]
                    ]

    let eval1 = evaluateHandlersCek (handleDynamicIntToString . handleDynamicLog)
    let eval2 = evaluateHandlersCek (handleDynamicLog . handleDynamicIntToString)
    (logs1, _) <- liftIO . eval1 $ OnChain term
    (logs2, _) <- liftIO . eval2 $ OnChain term
    logs1 @?= map show [1 .. 10 :: Int]
    logs2 @?= map show [1 .. 10 :: Int]

test_logging :: TestTree
test_logging =
    testGroup "logging"
        [ test_logInt
        , test_logInts
        ]
