module Marlowe.Extended.Template where

import Marlowe.Extended (Contract)
import Marlowe.Extended.Metadata (MetaData)

-- TODO: This actually belongs to Marlowe.Extended.Metadata
--       https://github.com/input-output-hk/plutus/pull/2855#discussion_r593138086
type ContractTemplate
  = { metaData :: MetaData
    , extendedContract :: Contract
    }
