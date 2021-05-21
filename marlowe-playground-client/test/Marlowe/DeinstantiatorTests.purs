module Marlowe.DeinstantiatorTests where

import Prelude
import Data.BigInteger (fromInt)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested ((/\))
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.CouponBondGuaranteed as CouponBondGuaranteed
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
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
                          [ "Buyer's deposit timeout" /\ fromInt 60
                          , "Buyer's dispute timeout" /\ fromInt 180
                          , "Seller's response timeout" /\ fromInt 240
                          , "Timeout for arbitrage" /\ fromInt 360
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
    test "Escrow with collateral" do
      let
        mFilledEscrowWithCollateral :: Maybe Contract
        mFilledEscrowWithCollateral =
          toCore
            ( fillTemplate
                ( TemplateContent
                    { slotContent:
                        Map.fromFoldable
                          [ "Collateral deposit by seller timeout" /\ fromInt 60
                          , "Deposit of collateral by buyer timeout" /\ fromInt 120
                          , "Deposit of price by buyer timeout" /\ fromInt 180
                          , "Dispute by buyer timeout" /\ fromInt 300
                          , "Seller's response timeout" /\ fromInt 360
                          ]
                    , valueContent:
                        Map.fromFoldable
                          [ "Collateral amount" /\ fromInt 500
                          , "Price" /\ fromInt 500
                          ]
                    }
                )
                EscrowWithCollateral.contractTemplate.extendedContract
            )
      assertFalse "Could not instantiate Escrow with collateral contract" (mFilledEscrowWithCollateral == Nothing)
      equal (Just EscrowWithCollateral.contractTemplate) (maybe Nothing findTemplate mFilledEscrowWithCollateral)
    test "Zero Coupon Bond" do
      let
        mFilledZeroCouponBond :: Maybe Contract
        mFilledZeroCouponBond =
          toCore
            ( fillTemplate
                ( TemplateContent
                    { slotContent:
                        Map.fromFoldable
                          [ "Initial exchange deadline" /\ fromInt 60
                          , "Maturity exchange deadline" /\ fromInt 150
                          ]
                    , valueContent:
                        Map.fromFoldable
                          [ "Discounted price" /\ fromInt 50
                          , "Notional price" /\ fromInt 100
                          ]
                    }
                )
                ZeroCouponBond.contractTemplate.extendedContract
            )
      assertFalse "Could not instantiate Zero Coupon Bond contract" (mFilledZeroCouponBond == Nothing)
      equal (Just ZeroCouponBond.contractTemplate) (maybe Nothing findTemplate mFilledZeroCouponBond)
    test "Coupon Bond Guaranteed" do
      let
        mFilledCouponBondGuaranteed :: Maybe Contract
        mFilledCouponBondGuaranteed =
          toCore
            ( fillTemplate
                ( TemplateContent
                    { slotContent: mempty
                    , valueContent:
                        Map.fromFoldable
                          [ "Interest instalment" /\ fromInt 10
                          , "Principal" /\ fromInt 1000
                          ]
                    }
                )
                CouponBondGuaranteed.contractTemplate.extendedContract
            )
      assertFalse "Could not instantiate Coupon Bond Guaranteed contract" (mFilledCouponBondGuaranteed == Nothing)
      equal (Just CouponBondGuaranteed.contractTemplate) (maybe Nothing findTemplate mFilledCouponBondGuaranteed)
