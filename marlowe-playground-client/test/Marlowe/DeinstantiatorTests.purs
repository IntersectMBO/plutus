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
import Marlowe.Extended (toCore)
import Marlowe.Template (TemplateContent(..), fillTemplate)
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
                          [ "Payment deadline" /\ fromInt 600
                          , "Complaint response deadline" /\ fromInt 1800
                          , "Complaint deadline" /\ fromInt 2400
                          , "Mediation deadline" /\ fromInt 3600
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
    test "Zero Coupon Bond" do
      let
        mFilledZeroCouponBond :: Maybe Contract
        mFilledZeroCouponBond =
          toCore
            ( fillTemplate
                ( TemplateContent
                    { slotContent:
                        Map.fromFoldable
                          [ "Loan deadline" /\ fromInt 600
                          , "Payback deadline" /\ fromInt 1500
                          ]
                    , valueContent:
                        Map.fromFoldable
                          [ "Interest" /\ fromInt 50
                          , "Amount" /\ fromInt 100
                          ]
                    }
                )
                ZeroCouponBond.contractTemplate.extendedContract
            )
      assertFalse "Could not instantiate Zero Coupon Bond contract" (mFilledZeroCouponBond == Nothing)
      equal (Just ZeroCouponBond.contractTemplate) (maybe Nothing findTemplate mFilledZeroCouponBond)
