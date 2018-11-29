-- | Tests of dynamic strings and characters.

{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.String
    ( test_dynamicStrings
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.StdLib.Data.Unit

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.IO.Class                     (liftIO)
import           Hedgehog                                   hiding (Size, Var)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

test_stringRoundtrip :: TestTree
test_stringRoundtrip = testProperty "stringRoundtrip" . property $ do
    str <- forAll $ Gen.string (Range.linear 0 20) Gen.unicode
    let mayStr' = runQuote (makeDynamicBuiltin str) >>= sequence . readDynamicBuiltinCek
    Just (Right str) === mayStr'

test_plcListOfStringsRoundtrip :: TestTree
test_plcListOfStringsRoundtrip = testProperty "listOfStringsRoundtrip" . property $ do
    strs <- forAll . fmap PlcList . Gen.list (Range.linear 0 10) $ Gen.string (Range.linear 0 10) Gen.unicode
    let mayStrs' = runQuote (makeDynamicBuiltin strs) >>= sequence . readDynamicBuiltinCek
    Just (Right strs) === mayStrs'

-- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that appends a char to
-- the contents of an external 'IORef' and assemble all the resulting terms together in a single term
-- where all characters are passed to lambdas and ignored, so that only 'unitval' is returned in the end.
-- After evaluation of the CEK machine finishes, read the 'IORef' and check that you got the exact same
-- sequence of 'Char's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only handle
-- pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
test_collectChars :: TestTree
test_collectChars = testProperty "collectChars" . property $ do
    str <- forAll $ Gen.string (Range.linear 0 20) Gen.unicode
    (str', errOrRes) <- liftIO . withEmitEvaluateBy evaluateCekCatch TypedBuiltinDyn $ \emit ->
        runQuote $ do
            unit        <- getBuiltinUnit
            unitval     <- getBuiltinUnitval
            ignore <- do
                x <- freshName () "x"
                y <- freshName () "y"
                return
                    . LamAbs () x unit
                    . LamAbs () y unit
                    $ Var () y
            let step arg rest = mkIterApp () ignore [Apply () emit arg, rest]
            chars <- traverse unsafeMakeDynamicBuiltin str
            return $ foldr step unitval chars
    case errOrRes of
        Left _                      -> failure
        Right EvaluationFailure     -> failure
        Right (EvaluationSuccess _) -> return ()
    str === str'

test_dynamicStrings :: TestTree
test_dynamicStrings =
    testGroup "dynamicStrings"
        [ test_stringRoundtrip
        , test_plcListOfStringsRoundtrip
        , test_collectChars
        ]
