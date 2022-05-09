module Plutus.V1.Ledger.ProtocolVersions where

import Plutus.ApiCommon

-- Based on https://github.com/input-output-hk/cardano-ledger/wiki/First-Block-of-Each-Era

shelleyPV :: ProtocolVersion
shelleyPV = ProtocolVersion 2 0

allegraPV :: ProtocolVersion
allegraPV = ProtocolVersion 3 0

maryPV :: ProtocolVersion
maryPV = ProtocolVersion 4 0

alonzoPV :: ProtocolVersion
alonzoPV = ProtocolVersion 5 0

vasilPV :: ProtocolVersion
vasilPV = ProtocolVersion 7 0
