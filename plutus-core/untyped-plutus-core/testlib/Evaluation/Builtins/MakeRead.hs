{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.Builtins.MakeRead
  ( test_makeRead
  ) where

import PlutusCore qualified as TPLC
import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as TPLC
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Pretty
import PlutusCore.StdLib.Data.Unit
import PlutusPrelude

import UntypedPlutusCore as UPLC (Name, Term, TyName)

import Evaluation.Builtins.Common

import Data.String (fromString)
import Hedgehog hiding (Size, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Text (Text)

{-| Lift a Haskell value into a PLC term, evaluate it and unlift the result back to the original
Haskell value. -}
makeRead
  :: ( MakeKnown (TPLC.Term TyName Name DefaultUni DefaultFun ()) a
     , ReadKnown (UPLC.Term Name DefaultUni DefaultFun ()) a
     )
  => a -> EvaluationResult a
makeRead x = do
  xTerm <- makeKnownOrFail @_ @(TPLC.Term TyName Name DefaultUni DefaultFun ()) x
  case splitStructuralOperational
    <$> typecheckReadKnownCek
      def
      TPLC.defaultBuiltinCostModelForTesting
      xTerm of
    Left err -> error $ "Type error" ++ displayPlcCondensedErrorClassic err
    Right (Left err) -> error $ "Evaluation error: " ++ show err
    Right (Right res) -> res

builtinRoundtrip
  :: ( MakeKnown (TPLC.Term TyName Name DefaultUni DefaultFun ()) a
     , ReadKnown (UPLC.Term Name DefaultUni DefaultFun ()) a
     , Show a
     , Eq a
     )
  => Gen a -> Property
builtinRoundtrip genX = property $ do
  x <- forAll genX
  case makeRead x of
    EvaluationFailure -> fail "EvaluationFailure"
    EvaluationSuccess x' -> x === x'

test_textRoundtrip :: TestTree
test_textRoundtrip =
  testPropertyNamed "textRoundtrip" "textRoundtrip" . builtinRoundtrip $
    Gen.text (Range.linear 0 20) Gen.unicode

{-| Generate a bunch of 'text's, put each of them into a 'Term' and apply the @Trace@ builtin over
each of these terms and assemble all the resulting terms together in a single term where all
characters are passed to lambdas and ignored, so that only 'unitval' is returned in the end.

After evaluation of the CEK machine finishes, check that the logs contains the exact same
sequence of 'text's that was originally generated. -}
test_collectText :: BuiltinSemanticsVariant DefaultFun -> TestTree
test_collectText semVar = testPropertyNamed (show semVar) (fromString $ show semVar) . property $ do
  strs <- forAll . Gen.list (Range.linear 0 10) $ Gen.text (Range.linear 0 20) Gen.unicode
  let step arg rest =
        mkIterAppNoAnn
          (tyInst () (builtin () Trace) unit)
          [ mkConstant @Text @DefaultUni () arg
          , rest
          ]
      term = foldr step unitval (reverse strs)
  strs' <- case typecheckEvaluateCek semVar TPLC.defaultBuiltinCostModelForTesting term of
    Left _ -> failure
    Right (EvaluationFailure, _) -> failure
    Right (EvaluationSuccess _, strs') -> return strs'
  strs === strs'

test_makeRead :: TestTree
test_makeRead =
  testGroup
    "makeRead"
    [ test_textRoundtrip
    , testGroup "collectText" $ map test_collectText enumerate
    ]
