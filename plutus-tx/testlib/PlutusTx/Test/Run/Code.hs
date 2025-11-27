{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module PlutusTx.Test.Run.Code
  ( module Eval
  , evaluationResultMatchesHaskell
  , assertEvaluatesSuccessfully
  , assertEvaluatesWithError
  , assertResult
  ) where

import Prelude

import Data.Text qualified as Text
import PlutusCore.Pretty
import PlutusCore.Test (TestNested, assertEqualPretty, embed)
import PlutusTx qualified as Tx
import PlutusTx.Code (CompiledCode)
import PlutusTx.Eval as Eval
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import Test.Tasty (TestName)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase)
import UntypedPlutusCore (DefaultUni)

{-| Evaluate 'CompiledCode' and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties. -}
evaluationResultMatchesHaskell
  :: Tx.Lift DefaultUni hask
  => CompiledCode a
  -> (forall r. (Eq r, Show r) => r -> r -> k)
  -> hask
  -> k
evaluationResultMatchesHaskell actual =
  cekResultMatchesHaskellValue (compiledCodeToTerm actual)

assertEvaluatesSuccessfully :: CompiledCode a -> Assertion
assertEvaluatesSuccessfully code = do
  case evaluateCompiledCode code of
    EvalResult {evalResult = Right _} -> pure ()
    EvalResult {evalResult = Left err, evalResultTraces} ->
      assertFailure $
        Text.unpack $
          Text.unlines
            [ "Evaluation failed with an error:"
            , render (prettyPlcClassicSimple err)
            , "Evaluation traces:"
            , Text.unlines evalResultTraces
            ]

assertEvaluatesWithError :: CompiledCode a -> Assertion
assertEvaluatesWithError code = do
  case evaluateCompiledCode code of
    EvalResult {evalResult = Left _} -> pure ()
    EvalResult {evalResult = Right _, evalResultTraces} ->
      assertFailure $
        Text.unpack $
          Text.unlines
            [ "Evaluation succeeded, but expected an error."
            , "Evaluation traces:"
            , Text.unlines evalResultTraces
            ]

assertResult :: TestName -> CompiledCode Bool -> TestNested
assertResult name code =
  evaluationResultMatchesHaskell
    code
    (\p h -> embed $ testCase name $ assertEqualPretty name p h)
    True
