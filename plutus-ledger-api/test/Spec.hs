-- editorconfig-checker-disable-file
module Main where

import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.Examples
import PlutusLedgerApi.Test.V1.EvaluationContext qualified as V1
import PlutusLedgerApi.V1 as V1
import PlutusPrelude
import Spec.CBOR.DeserialiseFailureInfo qualified
import Spec.CostModelParams qualified
import Spec.Eval qualified
import Spec.Interval qualified
import Spec.NoThunks qualified
import Spec.Versions qualified

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Writer

main :: IO ()
main = defaultMain tests

v1_evalCtxForTesting :: EvaluationContext
v1_evalCtxForTesting = fst $ unsafeFromRight $ runWriterT $ V1.mkEvaluationContext (fmap snd V1.costModelParamsForTesting)

alwaysTrue :: TestTree
alwaysTrue = testCase "always true script returns true" $
    let script = either (error . show) id $ V1.deserialiseScript alonzoPV (alwaysSucceedingNAryFunction 2)
        (_, res) = evaluateScriptCounting alonzoPV Quiet v1_evalCtxForTesting script [I 1, I 2]
    in assertBool "succeeds" (isRight res)

alwaysFalse :: TestTree
alwaysFalse = testCase "always false script returns false" $
    let script = either (error . show) id $ V1.deserialiseScript alonzoPV (alwaysFailingNAryFunction 2)
        (_, res) = evaluateScriptCounting alonzoPV Quiet v1_evalCtxForTesting script [I 1, I 2]
    in assertBool "fails" (isLeft res)

unavailableBuiltins :: TestTree
unavailableBuiltins = testCase "builtins are unavailable before Alonzo" $
    let res = V1.deserialiseScript maryPV summingFunction
    in assertBool "fails" (isLeft res)

availableBuiltins :: TestTree
availableBuiltins = testCase "builtins are available after Alonzo" $
    let res = V1.deserialiseScript alonzoPV summingFunction
    in assertBool "succeeds" (isRight res)

saltedFunction :: TestTree
saltedFunction =
    let evaluate ss ss' args =
            let s = either (error . show) id $ V1.deserialiseScript alonzoPV ss
                s' = either (error . show) id $ V1.deserialiseScript alonzoPV ss'
             in ( evaluateScriptCounting alonzoPV Quiet v1_evalCtxForTesting s args
                , evaluateScriptCounting alonzoPV Quiet v1_evalCtxForTesting s' args
                )
    in testGroup "salted function"
    [ testProperty "saturated" $ \(n :: Word8) salt fWhich ->
        let f = (if fWhich then alwaysSucceedingNAryFunction else alwaysFailingNAryFunction) $ fromInteger $ toInteger n
            f' = saltFunction salt f
            args = replicate (fromEnum n) $ I 1
            ((_, res), (_, res')) = evaluate f f' args
        in cover 25 (isRight res) "success" $
           cover 25 (isLeft res) "fail" $
            void res === void res'
            .&&. fWhich === isRight res
    , testProperty "unsaturated" $ \(n :: Word8) (n' :: Word8) salt fWhich ->
        let f = (if fWhich then alwaysSucceedingNAryFunction else alwaysFailingNAryFunction) $
                fromInteger (toInteger n) + fromInteger (toInteger n') + 1
            f' = saltFunction salt f
            args = replicate (fromEnum n) $ I 1
            ((_, res), (_, res')) = evaluate f f' args
        in cover 25 (isRight res) "success" $
           void res === void res'
    , testProperty "oversaturated" $ \(n :: Word8) (n' :: Word8) salt fWhich ->
        let f = (if fWhich then alwaysSucceedingNAryFunction else alwaysFailingNAryFunction) $
                fromInteger (toInteger n)
            f' = saltFunction salt f
            args = replicate (fromEnum n + fromEnum n' + 1) $ I 1
            ((_, res), (_, res')) = evaluate f f' args
        in cover 25 (isLeft res) "fail" $
            void res === void res'
    , testProperty "salt" $ \(n :: Word8) salt salt' fWhich ->
        let f = (if fWhich then alwaysSucceedingNAryFunction else alwaysFailingNAryFunction) $ fromInteger $ toInteger n
            f' = saltFunction salt f
            f'' = saltFunction salt' f
        in salt /= salt' ==> f' /= f''
    ]


tests :: TestTree
tests = testGroup "plutus-ledger-api" [
    testGroup "basic evaluation tests" [
        alwaysTrue
        , alwaysFalse
        , saltedFunction
        , unavailableBuiltins
        , availableBuiltins
    ]
    , Spec.Interval.tests
    , Spec.Eval.tests
    , Spec.Versions.tests
    , Spec.CostModelParams.tests
    , Spec.NoThunks.tests
    , Spec.CBOR.DeserialiseFailureInfo.tests
    ]
