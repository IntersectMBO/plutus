{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=SumsOfProducts #-}

module Spec.ReturnUnit.V3 where

import PlutusLedgerApi.Common (DefaultFun)
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.V3.EvaluationContext qualified as V3
import PlutusLedgerApi.V3 as V3
import PlutusPrelude
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude (BuiltinUnit, check)
import PlutusTx.TH (compile)

import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.HUnit

import Control.Monad.Writer

tests :: TestTree
tests =
  testGroup
    "Plutus V3 validators must evaluate to BuiltinUnit"
    [ expectSuccess "should succeed" good (I 1)
    , expectFailure "returns Bool" returnsBool (I 1)
    , expectFailure "too many parameters" tooManyParameters (I 1)
    ]

evalCtx :: V3.EvaluationContext DefaultFun
evalCtx =
  fst . unsafeFromRight . runWriterT . V3.mkEvaluationContext $
    fmap snd V3.costModelParamsForTesting

expectSuccess ::
  forall a.
  TestName ->
  CompiledCode (BuiltinData -> a) ->
  -- | Script argument
  Data ->
  TestTree
expectSuccess name code arg = testCase name $ case res of
  Left _  -> assertFailure "fails"
  Right _ -> pure ()
  where
    sScript = serialiseCompiledCode code
    script = either (error . show) id $ V3.deserialiseScript changPV sScript
    (_, res) = V3.evaluateScriptCounting changPV V3.Quiet evalCtx script arg

expectFailure ::
  forall a.
  TestName ->
  CompiledCode (BuiltinData -> a) ->
  -- | Script argument
  Data ->
  TestTree
expectFailure name code arg = testCase name $ case res of
  Left InvalidReturnValue -> pure ()
  Left _                  -> assertFailure "evaluation failed for a different reason"
  Right _                 -> assertFailure "evaluation succeeded"
  where
    sScript = serialiseCompiledCode code
    script = either (error . show) id $ V3.deserialiseScript changPV sScript
    (_, res) = V3.evaluateScriptCounting changPV V3.Quiet evalCtx script arg

good :: CompiledCode (BuiltinData -> BuiltinUnit)
good =
  $$( compile
        [||
        \d ->
          let n = PlutusTx.unsafeFromBuiltinData d
           in check (PlutusTx.greaterThanInteger n 0)
        ||]
    )

returnsBool :: CompiledCode (BuiltinData -> Bool)
returnsBool =
  $$( compile
        [||
        \d ->
          let n = PlutusTx.unsafeFromBuiltinData d
           in PlutusTx.greaterThanInteger n 0
        ||]
    )

tooManyParameters :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinUnit)
tooManyParameters =
  $$( compile
        [||
        \d _ ->
          let n = PlutusTx.unsafeFromBuiltinData d
           in check (PlutusTx.greaterThanInteger n 0)
        ||]
    )
