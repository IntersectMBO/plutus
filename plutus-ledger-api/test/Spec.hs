{-# LANGUAGE BlockArguments #-}

module Main where

import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.Examples
import PlutusLedgerApi.Test.V1.EvaluationContext qualified as V1
import PlutusLedgerApi.Test.V3.EvaluationContext qualified as V3
import PlutusLedgerApi.V1 as V1
import PlutusLedgerApi.V3 as V3
import PlutusPrelude
import Spec.CBOR.DeserialiseFailureInfo qualified
import Spec.ContextDecoding qualified
import Spec.CostModelParams qualified
import Spec.Data.CostModelParams qualified
import Spec.Data.Eval qualified
import Spec.Data.Versions qualified
import Spec.Eval qualified
import Spec.Interval qualified
import Spec.ScriptDecodeError qualified
import Spec.V1.Data.Value qualified as Data.Value
import Spec.V1.Value qualified as Value
import Spec.Versions qualified

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Writer
import Data.Int (Int64)

main :: IO ()
main = defaultMain tests

v1_evalCtxForTesting :: V1.EvaluationContext
v1_evalCtxForTesting =
  fst . unsafeFromRight . runWriterT . V1.mkEvaluationContext $
    fmap snd V1.costModelParamsForTesting

{-| Constructing a V3 context with the first 223 parameters.
As a result, the cost model parameters for `integerToByteString`
and `byteStringToInteger` should be set to large numbers, preventing
them from being used. -}
v3_evalCtxTooFewParams :: V3.EvaluationContext
v3_evalCtxTooFewParams =
  fst . unsafeFromRight . runWriterT $
    V3.mkEvaluationContext . take 223 $
      fmap snd V3.costModelParamsForTesting

alwaysTrue :: TestTree
alwaysTrue =
  testCase "always true script returns true" $
    let script =
          either (error . show) id $
            V1.deserialiseScript alonzoPV (alwaysSucceedingNAryFunction 2)
        (_, res) =
          V1.evaluateScriptCounting
            alonzoPV
            V1.Quiet
            v1_evalCtxForTesting
            script
            [I 1, I 2]
     in assertBool "succeeds" (isRight res)

alwaysFalse :: TestTree
alwaysFalse =
  testCase "always false script returns false" $
    let script =
          either (error . show) id $
            V1.deserialiseScript alonzoPV (alwaysFailingNAryFunction 2)
        (_, res) =
          V1.evaluateScriptCounting
            alonzoPV
            V1.Quiet
            v1_evalCtxForTesting
            script
            [I 1, I 2]
     in assertBool "fails" (isLeft res)

unavailableBuiltins :: TestTree
unavailableBuiltins =
  testCase "builtins are unavailable before Alonzo" $
    let res = V1.deserialiseScript maryPV summingFunction
     in assertBool "fails" (isLeft res)

availableBuiltins :: TestTree
availableBuiltins =
  testCase "builtins are available after Alonzo" $
    let res = V1.deserialiseScript alonzoPV summingFunction
     in assertBool "succeeds" (isRight res)

integerToByteStringExceedsBudget :: TestTree
integerToByteStringExceedsBudget =
  testCase "integerToByteString should exceed budget" $
    let script =
          either (error . show) id $
            V3.deserialiseScript changPV integerToByteStringFunction
        (_, res) =
          V3.evaluateScriptCounting
            changPV
            V3.Quiet
            v3_evalCtxTooFewParams
            script
            (I 1)
     in case res of
          Left _ -> assertFailure "fails"
          Right (ExBudget cpu _mem) ->
            assertBool
              "did not exceed budget"
              (cpu >= fromIntegral (maxBound :: Int64))

saltedFunction :: TestTree
saltedFunction =
  let evaluate ss ss' args =
        let s = either (error . show) id $ V1.deserialiseScript alonzoPV ss
            s' = either (error . show) id $ V1.deserialiseScript alonzoPV ss'
         in ( V1.evaluateScriptCounting
                alonzoPV
                V1.Quiet
                v1_evalCtxForTesting
                s
                args
            , V1.evaluateScriptCounting
                alonzoPV
                V1.Quiet
                v1_evalCtxForTesting
                s'
                args
            )
   in testGroup
        "salted function"
        [ testProperty "saturated" \(n :: Word8) salt fWhich ->
            let f =
                  ( if fWhich
                      then alwaysSucceedingNAryFunction
                      else alwaysFailingNAryFunction
                  )
                    (fromInteger (toInteger n))
                f' = saltFunction salt f
                args = replicate (fromEnum n) $ I 1
                ((_, res), (_, res')) = evaluate f f' args
             in cover 25 (isRight res) "success" $
                  cover 25 (isLeft res) "fail" $
                    void res
                      === void res'
                      .&&. fWhich
                        === isRight res
        , testProperty "unsaturated" \(n :: Word8) (n' :: Word8) salt fWhich ->
            let f =
                  ( if fWhich
                      then alwaysSucceedingNAryFunction
                      else alwaysFailingNAryFunction
                  )
                    (fromInteger (toInteger n) + fromInteger (toInteger n') + 1)
                f' = saltFunction salt f
                args = replicate (fromEnum n) $ I 1
                ((_, res), (_, res')) = evaluate f f' args
             in cover 25 (isRight res) "success" $
                  void res === void res'
        , testProperty
            "oversaturated"
            \(n :: Word8) (n' :: Word8) salt fWhich ->
              let f =
                    ( if fWhich
                        then alwaysSucceedingNAryFunction
                        else alwaysFailingNAryFunction
                    )
                      (fromInteger (toInteger n))
                  f' = saltFunction salt f
                  args = replicate (fromEnum n + fromEnum n' + 1) $ I 1
                  ((_, res), (_, res')) = evaluate f f' args
               in cover 25 (isLeft res) "fail" $
                    void res === void res'
        , testProperty "salt" \(n :: Word8) salt salt' fWhich ->
            let f =
                  ( if fWhich
                      then alwaysSucceedingNAryFunction
                      else alwaysFailingNAryFunction
                  )
                    (fromInteger (toInteger n))
                f' = saltFunction salt f
                f'' = saltFunction salt' f
             in salt /= salt' ==> f' /= f''
        ]

tests :: TestTree
tests =
  testGroup
    "plutus-ledger-api"
    [ testGroup
        "basic evaluation tests"
        [ alwaysTrue
        , alwaysFalse
        , saltedFunction
        , unavailableBuiltins
        , availableBuiltins
        , integerToByteStringExceedsBudget
        ]
    , testGroup
        "Common"
        [ Spec.Interval.tests
        , Spec.CBOR.DeserialiseFailureInfo.tests
        , Spec.ScriptDecodeError.tests
        ]
    , testGroup
        "Context-dependent tests"
        [ testGroup
            "Original"
            [ Spec.Eval.tests
            , Spec.Versions.tests
            , runTestNested ["CostModel", "Params"] [Spec.CostModelParams.tests]
            , Spec.ContextDecoding.tests
            , Value.test_Value
            ]
        , testGroup
            "Data"
            [ Spec.Data.Eval.tests
            , Spec.Data.Versions.tests
            , runTestNested
                ["CostModel", "Data", "Params"]
                [Spec.Data.CostModelParams.tests]
            , Data.Value.test_Value
            ]
        ]
    ]
