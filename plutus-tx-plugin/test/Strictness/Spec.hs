{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Strictness.Spec where

import Test.Tasty.Extras

import PlutusTx qualified as Tx
import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNestedGhc
    "Strictness"
    [ goldenEvalCekCatch "lambda-default" $ [lambdaDefault `unsafeApplyCode` bot]
    , goldenPirReadable "lambda-default" lambdaDefault
    , goldenUPlcReadable "lambda-default" lambdaDefault

    -- FIXME: This should not crash, but it currently does.
    , goldenEvalCekCatch "lambda-nonstrict" $ [lambdaNonStrict `unsafeApplyCode` bot]
    , goldenPirReadable "lambda-nonstrict" lambdaNonStrict
    , goldenUPlcReadable "lambda-nonstrict" lambdaNonStrict

    , goldenEvalCekCatch "lambda-strict" $ [lambdaStrict `unsafeApplyCode` bot]
    , goldenPirReadable "lambda-strict" lambdaStrict
    , goldenUPlcReadable "lambda-strict" lambdaStrict

    -- FIXME: This should crash (because the `Strict` extension is on), but it currently doesn't.
    , goldenEvalCekCatch "let-default" $ [letDefault `unsafeApplyCode` one]
    , goldenPirReadable "let-default" letDefault
    , goldenUPlcReadable "let-default" letDefault

    , goldenEvalCekCatch "let-nonstrict" $ [letNonStrict `unsafeApplyCode` one]
    , goldenPirReadable "let-nonstrict" letNonStrict
    , goldenUPlcReadable "let-nonstrict" letNonStrict

    -- FIXME: This should crash, but it currently doesn't.
    , goldenEvalCekCatch "let-strict" $ [letStrict `unsafeApplyCode` one]
    , goldenPirReadable "let-strict" letStrict
    , goldenUPlcReadable "let-strict" letStrict
    ]

lambdaDefault :: CompiledCode (Integer -> Integer -> Integer)
lambdaDefault =
  $$( compile
        [||
        \n -> \m -> n PlutusTx.+ m
        ||]
    )

lambdaNonStrict :: CompiledCode (Integer -> Integer -> Integer)
lambdaNonStrict =
  $$( compile
        [||
        \(~n) -> \m -> n PlutusTx.+ m
        ||]
    )

lambdaStrict :: CompiledCode (Integer -> Integer -> Integer)
lambdaStrict =
  $$( compile
        [||
        \(!n) -> \m -> n PlutusTx.+ m
        ||]
    )

letDefault :: CompiledCode (Integer -> Integer)
letDefault =
  $$( compile
        [||
        \m ->
          let n = PlutusTx.error () m
           in if m PlutusTx.< 0 then n PlutusTx.+ n else m
        ||]
    )

letNonStrict :: CompiledCode (Integer -> Integer)
letNonStrict =
  $$( compile
        [||
        \m ->
          let ~n = PlutusTx.error () m
           in if m PlutusTx.< 0 then n PlutusTx.+ n else m
        ||]
    )

letStrict :: CompiledCode (Integer -> Integer)
letStrict =
  $$( compile
        [||
        \m ->
          let !n = PlutusTx.error () m
           in if m PlutusTx.< 0 then n PlutusTx.+ n else m
        ||]
    )

bot :: CompiledCode Integer
bot = $$(compile [|| PlutusTx.error () ||])

one :: CompiledCode Integer
one = Tx.liftCodeDef 1
