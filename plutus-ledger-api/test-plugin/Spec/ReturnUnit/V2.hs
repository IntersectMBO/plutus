{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

module Spec.ReturnUnit.V2 where

import PlutusLedgerApi.Common (DefaultFun)
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Test.V2.EvaluationContext qualified as V2
import PlutusLedgerApi.V2 as V2
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
    "Plutus V2 validators may evaluate to any value"
    [ expectSuccess "should succeed" good (I 1)
    , expectSuccess "returns Bool" returnsBool (I 1)
    , expectSuccess "too many parameters" tooManyParameters (I 1)
    ]

evalCtx :: V2.EvaluationContext DefaultFun
evalCtx =
  fst . unsafeFromRight . runWriterT . V2.mkEvaluationContext $
    fmap snd V2.costModelParamsForTesting

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
    script = either (error . show) id $ V2.deserialiseScript changPV sScript
    (_, res) = V2.evaluateScriptCounting changPV V2.Quiet evalCtx script [arg]

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
