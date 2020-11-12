-- | Tests of dynamic strings and characters.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.DynamicBuiltins.MakeRead
    ( test_dynamicMakeRead
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc                                  hiding (error)
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Unit

import           Evaluation.DynamicBuiltins.Common

import           Control.Monad.IO.Class
import           Hedgehog                                                   hiding (Size, Var)
import qualified Hedgehog.Gen                                               as Gen
import qualified Hedgehog.Range                                             as Range
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog

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

-- | Generate a bunch of 'String's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that appends a char to
-- the contents of an external 'IORef' and assemble all the resulting terms together in a single
-- term where all characters are passed to lambdas and ignored, so that only 'unitval' is returned
-- in the end.
-- After evaluation of the CEK machine finishes, read the 'IORef' and check that you got the exact
-- same sequence of 'String's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only
-- handle pure things and 'unsafePerformIO' is the way to pretend an effectful thing is pure.
test_collectStrings :: TestTree
test_collectStrings = testProperty "collectStrings" . property $ do
    strs <- forAll . Gen.list (Range.linear 0 10) $ Gen.string (Range.linear 0 20) Gen.unicode
    (strs', errOrRes) <- liftIO . withEmit $ \emit -> do
        let runtime = toBuiltinsRuntime (DefaultFunDyn emit) defaultCostModel
            step arg rest = mkIterApp () sequ
                [ Apply () (Builtin () Trace) $ mkConstant @String @DefaultUni () arg
                , rest
                ]
            term = foldr step unitval strs
        pure $ typecheckEvaluateCek runtime term
    case errOrRes of
        Left _                      -> failure
        Right EvaluationFailure     -> failure
        Right (EvaluationSuccess _) -> return ()
    strs === strs'

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
        , test_collectStrings
        , test_noticeEvaluationFailure
        ]
