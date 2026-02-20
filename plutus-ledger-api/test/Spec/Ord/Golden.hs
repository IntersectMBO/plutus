{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| Golden tests for deriveOrd instances in plutus-ledger-api.
These tests capture the exact generated code for types where manual Ord instances
were replaced with deriveOrd, providing confidence that derived instances match
the original manual implementations. -}
module Spec.Ord.Golden (ordGoldenTests) where

import PlutusTx.Ord (deriveOrd)
import PlutusTx.Test.Golden (goldenCodeGen)
import Test.Tasty (TestTree)
import Test.Tasty.Extras (runTestNested)

-- V1 types
import PlutusLedgerApi.V1.Interval qualified as V1

-- V3 types
import PlutusLedgerApi.V3.Contexts qualified as V3

ordGoldenTests :: TestTree
ordGoldenTests =
  runTestNested
    ["test", "Spec", "Ord", "Golden"]
    [ -- V1 types
      $(goldenCodeGen "V1.Extended" (deriveOrd ''V1.Extended))
    , -- V3 types
      $(goldenCodeGen "V3.ProtocolVersion" (deriveOrd ''V3.ProtocolVersion))
    ]
