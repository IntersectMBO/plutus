module Main(main) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad (void)
import Data.Either
import Data.Word (Word8)
import Plutus.Ledger.Test.EvaluationContext (evalCtxForTesting)
import Plutus.Ledger.Test.Examples
import Plutus.Ledger.Test.ProtocolVersions
import Plutus.V1.Ledger.Api
import Spec.Builtins qualified
import Spec.CostModelParams qualified
import Spec.Eval qualified
import Spec.Interval qualified

main :: IO ()
main = defaultMain tests

alwaysTrue :: TestTree
alwaysTrue = testCase "always true script returns true" $
    let (_, res) = evaluateScriptCounting alonzoPV Quiet evalCtxForTesting (alwaysSucceedingNAryFunction 2) [I 1, I 2]
    in assertBool "succeeds" (isRight res)

alwaysFalse :: TestTree
alwaysFalse = testCase "always false script returns false" $
    let (_, res) = evaluateScriptCounting alonzoPV Quiet evalCtxForTesting (alwaysFailingNAryFunction 2) [I 1, I 2]
    in assertBool "fails" (isLeft res)

unavailableBuiltins :: TestTree
unavailableBuiltins = testCase "builtins are unavailable before Alonzo" $
    let (_, res) = evaluateScriptCounting maryPV Quiet evalCtxForTesting summingFunction []
    in assertBool "fails" (isLeft res)

availableBuiltins :: TestTree
availableBuiltins = testCase "builtins are available after Alonzo" $
    let (_, res) = evaluateScriptCounting alonzoPV Quiet evalCtxForTesting summingFunction []
    in assertBool "succeeds" (isRight res)

saltedFunction :: TestTree
saltedFunction =
    let evaluate f f' args =
            ( evaluateScriptCounting alonzoPV Quiet evalCtxForTesting f args
            , evaluateScriptCounting alonzoPV Quiet evalCtxForTesting f' args
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
    , Spec.Builtins.tests
    , Spec.CostModelParams.tests
    ]
