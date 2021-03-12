module Marlowe.Extended.Template where

import Marlowe.Extended (Contract)
import Marlowe.Extended.Metadata (MetaData)

type ContractTemplate
  = { metaData :: MetaData
    , extendedContract :: Contract
    }
