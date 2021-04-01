module Marlowe.DeinstantiatorTests where

import Prelude
import Data.BigInteger (fromInt)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested ((/\))
import Examples.PureScript.Escrow as Escrow
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Extended (TemplateContent(..), fillTemplate, toCore)
import Marlowe.Semantics (Contract)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (assertFalse, equal)

all :: TestSuite
all =
  suite "Deinstantiator Tests" do
    test "Escrow" do
      let
        mFilledEscrow :: Maybe Contract
        mFilledEscrow =
          toCore
            ( fillTemplate
                ( TemplateContent
                    { slotContent:
                        Map.fromFoldable
                          [ "Buyer's deposit timeout" /\ fromInt 10
                          , "Buyer's dispute timeout" /\ fromInt 50
                          , "Seller's response timeout" /\ fromInt 100
                          , "Timeout for arbitrage" /\ fromInt 1000
                          ]
                    , valueContent:
                        Map.fromFoldable
                          [ "Price" /\ fromInt 450
                          ]
                    }
                )
                Escrow.contractTemplate.extendedContract
            )
      assertFalse "Could not instantiate Escrow contract" (mFilledEscrow == Nothing)
      equal (Just Escrow.contractTemplate) (maybe Nothing findTemplate mFilledEscrow)
      pure unit
