{-# LANGUAGE DataKinds           #-} 
{-# LANGUAGE NoImplicitPrelude   #-} 
{-# LANGUAGE TemplateHaskell     #-} 
{-# LANGUAGE ScopedTypeVariables #-} 

module SimpleValidator where 

import PlutusTx 
import PlutusTx.Prelude 
import Plutus.V2.Ledger.Api 

-- A simple validator that always succeeds 

{-# INLINABLE mkValidator #-} 

mkValidator :: BuiltinData -> BuiltinData -> BuiltinData -> () 
mkValidator _ _ _ = () 

validator :: Validator 
validator = mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||]) 
