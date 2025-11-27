{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoNegativeLiterals #-}
{-# LANGUAGE NoStrict #-}

{-| This module tests that integer literals are handled correctly when both @Strict@
and @NegativeLiterals@ are off. These two extensions affect the Core we get.

See Note [Running PIR and UPLC Simplifiers in Integer Literal Tests]. -}
module IntegerLiterals.NoStrict.NoNegativeLiterals.Spec where

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test

import Test.Tasty.Extras

tests :: TestNested
tests =
  testNested "IntegerLiterals" . pure $
    testNestedGhc
      [ goldenPirReadable "integerLiterals-NoStrict-NoNegativeLiterals" integerLiterals
      ]

integerLiterals :: CompiledCode (Integer -> Integer)
integerLiterals =
  $$( compile
        [||
        \x ->
          let !smallStrict = 123
              !smallNegStrict = -321
              !bigStrict = 12345678901234567890
              !bigNegStrict = -11223344556677889900
              !bigDoubleNegStrict = -(-13579246801357924680)
              ~smallLazy = 456
              ~smallNegLazy = -654
              ~bigLazy = 98765432109876543210
              ~bigNegLazy = -99887766554433221100
              ~bigDoubleNegLazy = -(-24680135792468013579)
           in x
                PlutusTx.* smallStrict
                PlutusTx.+ smallNegStrict
                PlutusTx.+ bigStrict
                PlutusTx.+ bigNegStrict
                PlutusTx.+ bigDoubleNegStrict
                PlutusTx.+ smallLazy
                PlutusTx.+ smallNegLazy
                PlutusTx.+ bigLazy
                PlutusTx.+ bigNegLazy
                PlutusTx.+ bigDoubleNegLazy
        ||]
    )
