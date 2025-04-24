{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE Strict          #-}
{-# LANGUAGE TemplateHaskell #-}

module Strictness.Spec where

import Test.Tasty.Extras

import PlutusTx qualified as Tx
import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested "Strictness" . pure $ testNestedGhc
    [ goldenBundle "lambda-default" lambdaDefault (lambdaDefault `unsafeApplyCode` bot)
    -- FIXME: This should not crash, but it currently does.
    , goldenBundle "lambda-nonstrict" lambdaNonStrict (lambdaNonStrict `unsafeApplyCode` bot)
    , goldenBundle "lambda-strict" lambdaStrict (lambdaStrict `unsafeApplyCode` bot)
    -- FIXME: This should crash (because the `Strict` extension is on), but it currently doesn't.
    , goldenBundle "let-default" letDefault (letDefault `unsafeApplyCode` one)
    , goldenBundle "let-nonstrict" letNonStrict (letNonStrict `unsafeApplyCode` one)
    -- FIXME: This should crash, but it currently doesn't.
    , goldenBundle "let-strict" letStrict (letStrict `unsafeApplyCode` one)
    ]

lambdaDefault :: CompiledCode (Integer -> Integer -> Integer)
lambdaDefault = $$(compile [|| \n m -> n PlutusTx.+ m ||])

lambdaNonStrict :: CompiledCode (Integer -> Integer -> Integer)
lambdaNonStrict = $$(compile [|| \(~n) m -> n PlutusTx.+ m ||])

lambdaStrict :: CompiledCode (Integer -> Integer -> Integer)
lambdaStrict = $$(compile [|| \(!n) m -> n PlutusTx.+ m ||])

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
