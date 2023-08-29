{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}

{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE NoStrict              #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

-- | This module tests that integer literals are handled correctly, when @Strict@ is off
-- and @NegativeLiterals@ is on. These two extensions affect the Core we get. When
-- @NegativeLiterals@ is on, we can get @IN@ for negative integers.
--
-- See Note [Running PIR and UPLC Simplifiers in Integer literals Tests].
module IntegerLiterals.NoStrict.NegativeLiterals.Spec where

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

import Test.Tasty.Extras

tests :: TestNested
tests = testNestedGhc "IntegerLiterals"
  [ goldenPir "integerLiterals-NoStrict-NegativeLiterals" integerLiterals
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
           in x PlutusTx.* smallStrict
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

{- Note [Running PIR and UPLC Simplifiers in Integer Literal Tests]

The Integer literal tests run the PIR and UPLC simplifiers, because (1) we want to verify that
integerNegate is compiled away; (2) it is easier to tell from the optimized PIR whether or not
the signs of the numbers are correct, which is ultimately what we care about.
-}
