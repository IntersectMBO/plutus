-- | Tests of dynamic strings and characters.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.DynamicBuiltins.MakeRead
    ( test_dynamicMakeRead
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Pretty

import           Evaluation.DynamicBuiltins.Common

import           Hedgehog                                         hiding (Size, Var)
import qualified Hedgehog.Gen                                     as Gen
import qualified Hedgehog.Range                                   as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of a different type.
readMakeHetero
    :: ( KnownType (Term TyName Name DefaultUni DefaultFun ()) a
       , KnownType (Term TyName Name DefaultUni DefaultFun ()) b
       )
    => a -> EvaluationResult b
readMakeHetero x = do
    xTerm <- makeKnown @(Term TyName Name DefaultUni DefaultFun ()) x
    case extractEvaluationResult <$> typecheckReadKnownCek defBuiltinsRuntime xTerm of
        Left err          -> error $ "Type error" ++ displayPlcCondensedErrorClassic err
        Right (Left err)  -> error $ "Evaluation error: " ++ show err
        Right (Right res) -> res

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of the same type.
readMake :: KnownType (Term TyName Name DefaultUni DefaultFun ()) a => a -> EvaluationResult a
readMake = readMakeHetero

dynamicBuiltinRoundtrip
    :: (KnownType (Term TyName Name DefaultUni DefaultFun ()) a, Show a, Eq a)
    => Gen a -> Property
dynamicBuiltinRoundtrip genX = property $ do
    x <- forAll genX
    case readMake x of
        EvaluationFailure    -> fail "EvaluationFailure"
        EvaluationSuccess x' -> x === x'

test_stringRoundtrip :: TestTree
test_stringRoundtrip =
    testProperty "stringRoundtrip" . dynamicBuiltinRoundtrip $
        Gen.string (Range.linear 0 20) Gen.unicode

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
    return ()
-- TODO: fixme.
{-
    str <- forAll $ Gen.string (Range.linear 0 20) Gen.unicode
    (str', errOrRes) <- liftIO . withEmitEvaluateBy typecheckEvaluateCek mempty $ \emit ->
        let step arg rest = mkIterApp () sequ [Apply () emit arg, rest]
            chars = map (mkConstant @Char @DefaultUni ()) str
            in foldr step unitval chars
    case errOrRes of
        Left _                      -> failure
        Right EvaluationFailure     -> failure
        Right (EvaluationSuccess _) -> return ()
    str === str'
-}

test_noticeEvaluationFailure :: TestTree
test_noticeEvaluationFailure =
    testCase "noticeEvaluationFailure" . assertBool "'EvaluationFailure' ignored" $
        isEvaluationFailure $ do
            _ <- readMake True
            _ <- readMakeHetero @(EvaluationResult ()) @() EvaluationFailure
            readMake 'a'

test_dynamicMakeRead :: TestTree
test_dynamicMakeRead =
    testGroup "dynamicMakeRead"
        [ test_stringRoundtrip
        , test_collectChars
        , test_noticeEvaluationFailure
        ]
