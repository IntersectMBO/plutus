{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# LANGUAGE NoStrict            #-}

-- | We use this module to ensure that integer literals are handled correctly by all
-- supported GHC versions, when @Strict@ is off (we get different Core depending on
-- whether or not @Strict@ is on).
module IntegerLiteral.NoStrict where

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)

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
