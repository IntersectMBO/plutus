{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.MakeRead
    ( test_makeRead
    ) where

import PlutusCore qualified as TPLC
import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Pretty
import PlutusCore.StdLib.Data.Unit

import UntypedPlutusCore as UPLC (Name, Term, TyName)

import Evaluation.Builtins.Common

import Hedgehog hiding (Size, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

import Data.Text (Text)

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of a different type.
readMakeHetero
    :: ( MakeKnown (TPLC.Term TyName Name DefaultUni DefaultFun ()) a
       , ReadKnown (UPLC.Term Name DefaultUni DefaultFun ()) b
       )
    => a -> EvaluationResult b
readMakeHetero x = do
    xTerm <- makeKnownOrFail @_ @(TPLC.Term TyName Name DefaultUni DefaultFun ()) x
    case extractEvaluationResult <$> typecheckReadKnownCek TPLC.defaultCekParameters xTerm of
        Left err          -> error $ "Type error" ++ displayPlcCondensedErrorClassic err
        Right (Left err)  -> error $ "Evaluation error: " ++ show err
        Right (Right res) -> res

-- | Convert a Haskell value to a PLC term and then convert back to a Haskell value
-- of the same type.
readMake
    :: ( MakeKnown (TPLC.Term TyName Name DefaultUni DefaultFun ()) a
       , ReadKnown (UPLC.Term Name DefaultUni DefaultFun ()) a
       )
    => a -> EvaluationResult a
readMake = readMakeHetero

builtinRoundtrip
    :: ( MakeKnown (TPLC.Term TyName Name DefaultUni DefaultFun ()) a
       , ReadKnown (UPLC.Term Name DefaultUni DefaultFun ()) a
       , Show a, Eq a
       )
    => Gen a -> Property
builtinRoundtrip genX = property $ do
    x <- forAll genX
    case readMake x of
        EvaluationFailure    -> fail "EvaluationFailure"
        EvaluationSuccess x' -> x === x'

test_textRoundtrip :: TestTree
test_textRoundtrip =
    testProperty "textRoundtrip" . builtinRoundtrip $
        Gen.text (Range.linear 0 20) Gen.unicode

-- | Generate a bunch of 'text's, put each of them into a 'Term', apply a builtin over
-- each of these terms such that being evaluated it calls a Haskell function that appends a char to
-- the contents of an external 'IORef' and assemble all the resulting terms together in a single
-- term where all characters are passed to lambdas and ignored, so that only 'unitval' is returned
-- in the end.
-- After evaluation of the CEK machine finishes, read the 'IORef' and check that you got the exact
-- same sequence of 'text's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only
-- handle pure things and 'unsafePerformIO' is the way to pretend an effectful thing is pure.
test_collectText :: TestTree
test_collectText = testProperty "collectText" . property $ do
    strs <- forAll . Gen.list (Range.linear 0 10) $ Gen.text (Range.linear 0 20) Gen.unicode
    let step arg rest = mkIterApp () (tyInst () (builtin () Trace) unit)
            [ mkConstant @Text @DefaultUni () arg
            , rest
            ]
        term = foldr step unitval (reverse strs)
    strs' <- case typecheckEvaluateCek TPLC.defaultCekParameters term of
        Left _                             -> failure
        Right (EvaluationFailure, _)       -> failure
        Right (EvaluationSuccess _, strs') -> return strs'
    strs === strs'

test_noticeEvaluationFailure :: TestTree
test_noticeEvaluationFailure =
    testCase "noticeEvaluationFailure" . assertBool "'EvaluationFailure' ignored" $
        isEvaluationFailure $ do
            _ <- readMake True
            _ <- readMakeHetero @(EvaluationResult ()) @() EvaluationFailure
            readMake ("a"::Text)

test_makeRead :: TestTree
test_makeRead =
    testGroup "makeRead"
        [ test_textRoundtrip
        , test_collectText
        , test_noticeEvaluationFailure
        ]
