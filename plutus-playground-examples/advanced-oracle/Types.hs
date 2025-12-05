{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module Types where

import PlutusTx
import PlutusTx.Prelude

data OracleDatum = OracleDatum
    { odPrice :: Integer
    }
PlutusTx.makeIsDataIndexed ''OracleDatum [('OracleDatum, 0)]
