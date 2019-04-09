{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}
-- this adds source notes which helps the plugin give better errors
{-# OPTIONS_GHC   -g #-}
{-# OPTIONS_GHC -O0                 #-}
module Test where 

import qualified Language.PlutusTx.Code as Code
import qualified Ledger.Value.TH as Value
import qualified Ledger.Map.TH as Map
import qualified Language.PlutusTx as P

i :: Integer
i = Code.sizePlc $ $$(P.compile [|| $$(Map.all @Int @Int) ||])

-- OK
-- valueOf
-- symbols
-- scale
-- plus

-- unionWith
-- unionVal


-- NOT OK
-- eq
-- gt
-- checkBinRel
-- checkPred
-- unionVal