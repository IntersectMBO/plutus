-- | Tests of dynamic strings and characters.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module DynamicBuiltins.MakeRead
    ( test_dynamicMakeRead
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Unit
import           PlutusPrelude

import           Language.PlutusCore.Interpreter.CekMachine

import           DynamicBuiltins.Common

import           Control.Monad.IO.Class                     (liftIO)
import           Hedgehog                                   hiding (Size, Var)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of a different type.
readMakeHetero
    :: (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b)
    => a -> Maybe (Either (Error ()) (Either CekMachineException b))
readMakeHetero =
    makeDynamicBuiltin >=> reoption . traverse sequence . typecheckReadDynamicBuiltinCek mempty

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of the same type.
readMake
    :: KnownDynamicBuiltinType a => a -> Maybe (Either (Error ()) (Either CekMachineException a))
readMake = readMakeHetero

dynamicBuiltinRoundtrip :: (KnownDynamicBuiltinType a, Show a, Eq a) => Gen a -> Property
dynamicBuiltinRoundtrip genX = property $ do
    x <- forAll genX
    case readMake x of
        Nothing                 -> fail "EvaluationFailure"
        Just (Left err)         -> fail $ "Type error" ++ prettyPlcCondensedErrorClassicString err
        Just (Right (Left err)) -> fail $ "Evaluation error" ++ show err
        Just (Right (Right x')) -> x === x'

test_stringRoundtrip :: TestTree
test_stringRoundtrip =
    testProperty "stringRoundtrip" . dynamicBuiltinRoundtrip $
        Gen.string (Range.linear 0 20) Gen.unicode

test_plcListOfStringsRoundtrip :: TestTree
test_plcListOfStringsRoundtrip =
    testProperty "listOfStringsRoundtrip" . dynamicBuiltinRoundtrip $
        fmap PlcList . Gen.list (Range.linear 0 10) $
            Gen.string (Range.linear 0 10) Gen.unicode

test_plcListOfPairsRoundtrip :: TestTree
test_plcListOfPairsRoundtrip =
    testProperty "listOfPairsRoundtrip" . dynamicBuiltinRoundtrip $
        fmap PlcList . Gen.list (Range.linear 0 10) $
            (,) . PlcList <$> Gen.list (Range.linear 0 10) Gen.unicode <*> Gen.unicode

test_plcListOfSumsRoundtrip :: TestTree
test_plcListOfSumsRoundtrip =
    testProperty "listOfSumsRoundtrip" . dynamicBuiltinRoundtrip $
        fmap PlcList . Gen.list (Range.linear 0 10) $
            Gen.choice
                [ Left . PlcList <$> Gen.list (Range.linear 0 10) Gen.unicode
                , Right <$> Gen.unicode
                ]

-- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that appends a char to
-- the contents of an external 'IORef' and assemble all the resulting terms together in a single
-- term where all characters are passed to lambdas and ignored, so that only 'unitval' is returned
-- in the end.
-- After evaluation of the CEK machine finishes, read the 'IORef' and check that you got the exact
-- same sequence of 'Char's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only
-- handle pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
test_collectChars :: TestTree
test_collectChars = testProperty "collectChars" . property $ do
    str <- forAll $ Gen.string (Range.linear 0 20) Gen.unicode
    (str', errOrRes) <- liftIO . withEmitEvaluateBy typecheckEvaluateCek TypedBuiltinDyn $ \emit ->
        let step arg rest = mkIterApp () sequ [Apply () emit arg, rest]
            chars = map unsafeMakeDynamicBuiltin str
            in foldr step unitval chars
    case errOrRes of
        Left _                      -> failure
        Right EvaluationFailure     -> failure
        Right (EvaluationSuccess _) -> return ()
    str === str'

test_noticeEvaluationFailure :: TestTree
test_noticeEvaluationFailure =
    testCase "noticeEvaluationFailure" . assertBool "'EvaluationFailure' ignored" . isNothing $ do
        _ <- readMake True
        _ <- readMakeHetero @(EvaluationResult ()) @() EvaluationFailure
        readMake 'a'

test_ignoreEvaluationFailure :: TestTree
test_ignoreEvaluationFailure =
    testCase "ignoreEvaluationFailure" . assertBool "'EvaluationFailure' not ignored" . isJust $ do
        _ <- readMake True
        _ <- readMake @(EvaluationResult ()) EvaluationFailure
        readMake 'a'

test_EvaluationFailure :: TestTree
test_EvaluationFailure =
    testGroup "EvaluationFailure"
        [ test_noticeEvaluationFailure
        , test_ignoreEvaluationFailure
        ]

test_dynamicMakeRead :: TestTree
test_dynamicMakeRead =
    testGroup "dynamicMakeRead"
        [ test_stringRoundtrip
        , test_plcListOfStringsRoundtrip
        , test_plcListOfPairsRoundtrip
        , test_plcListOfSumsRoundtrip
        , test_collectChars
        , test_EvaluationFailure
        ]
