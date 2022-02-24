module Main(main) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad (void)
import Data.Either
import Data.Word (Word8)
import Plutus.V1.Ledger.Api
import Plutus.V1.Ledger.EvaluationContext (evalCtxForTesting)
import Plutus.V1.Ledger.Examples
import Spec.Eval qualified
import Spec.Interval qualified

main :: IO ()
main = defaultMain tests

alwaysTrue :: TestTree
alwaysTrue = testCase "always true script returns true" $
    let (_, res) = evaluateScriptCounting Quiet evalCtxForTesting (alwaysSucceedingNAryFunction 2) [I 1, I 2]
    in assertBool "succeeds" (isRight res)

alwaysFalse :: TestTree
alwaysFalse = testCase "always false script returns false" $
    let (_, res) = evaluateScriptCounting Quiet evalCtxForTesting (alwaysFailingNAryFunction 2) [I 1, I 2]
    in assertBool "fails" (isLeft res)

saltedFunction :: TestTree
saltedFunction =
    let evaluate f f' args =
            ( evaluateScriptCounting Quiet evalCtxForTesting f args
            , evaluateScriptCounting Quiet evalCtxForTesting f' args
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
    alwaysTrue
    , alwaysFalse
    , saltedFunction
    , Spec.Interval.tests
    , Spec.Eval.tests
    ]
