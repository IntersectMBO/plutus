module Template.Library
  ( defaultTemplate
  , templates
  ) where

import Prelude
import Marlowe.Extended (Action(..), Case(..), Contract(..), Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..))
import Template.Types (Template)

-- we could potentially just hard code these here for now, but it would be
-- better to fetch them from the library; in any case, I'm hard coding some
-- approximations of what these might look like to help get the ball rolling
defaultTemplate :: Template
defaultTemplate =
  { name: "Sample escrow contract 1"
  , type_: "Escrow"
  , description: "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction."
  , extendedContract: When [ Case (Deposit (Role "alice") (Role "alice") (Token "" "") (ConstantParam "amount")) (When [ Case (Choice (ChoiceId "choice" (Role "alice")) [ Bound zero one ]) (When [ Case (Choice (ChoiceId "choice" (Role "bob")) [ Bound zero one ]) (If (ValueEQ (ChoiceValue (ChoiceId "choice" (Role "alice"))) (ChoiceValue (ChoiceId "choice" (Role "bob")))) (If (ValueEQ (ChoiceValue (ChoiceId "choice" (Role "alice"))) (Constant zero)) (Pay (Role "alice") (Party (Role "bob")) (Token "" "") (ConstantParam "amount") Close) Close) (When [ Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound one one ]) Close, Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound zero zero ]) (Pay (Role "alice") (Party (Role "bob")) (Token "" "") (ConstantParam "amount") Close) ] (SlotParam "arbitrageTimeout") Close)) ] (SlotParam "bobTimeout") (When [ Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound one one ]) Close, Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound zero zero ]) (Pay (Role "alice") (Party (Role "bob")) (Token "" "") (ConstantParam "amount") Close) ] (SlotParam "arbitrageTimeout") Close)) ] (SlotParam "aliceTimeout") (When [ Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound one one ]) Close, Case (Choice (ChoiceId "choice" (Role "carol")) [ Bound zero zero ]) (Pay (Role "alice") (Party (Role "bob")) (Token "" "") (ConstantParam "amount") Close) ] (SlotParam "arbitrageTimeout") Close)) ] (SlotParam "depositSlot") Close
  }

templates :: Array Template
templates =
  [ defaultTemplate
  , { name: "Sample escrow contract 2"
    , type_: "Escrow"
    , description: "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction."
    , extendedContract: Close
    }
  , { name: "Sample zero coupon bond contract 1"
    , type_: "Zero Coupon Bond"
    , description: "A zero-coupon bond is a debt security that does not pay interest but instead trades at a deep discount, rendering a profit at maturity, when the bond is redeemed for its full face value."
    , extendedContract: Close
    }
  , { name: "Sample zero coupon bond contract 2"
    , type_: "Zero Coupon Bond"
    , description: "A zero-coupon bond is a debt security that does not pay interest but instead trades at a deep discount, rendering a profit at maturity, when the bond is redeemed for its full face value."
    , extendedContract: Close
    }
  , { name: "Sample coupon bond guaranteed contract 1"
    , type_: "Coupon Bond Guaranteed"
    , description: "A guaranteed bond is a debt security that offers a secondary guarantee that interest and principal payments will be made by a third party, should the issuer default. It can be backed by a bond insurance company, a fund or group entity, a government authority, or the corporate parents of subsidiaries or joint ventures that are issuing bonds."
    , extendedContract: Close
    }
  , { name: "Sample coupon bond guaranteed contract 2"
    , type_: "Coupon Bond Guaranteed"
    , description: "A guaranteed bond is a debt security that offers a secondary guarantee that interest and principal payments will be made by a third party, should the issuer default. It can be backed by a bond insurance company, a fund or group entity, a government authority, or the corporate parents of subsidiaries or joint ventures that are issuing bonds."
    , extendedContract: Close
    }
  , { name: "Sample swap contract 1"
    , type_: "Swap"
    , description: "A swap is a derivative contract through which two parties exchange the cash flows or liabilities from two different financial instruments. Most swaps involve cash flows based on a notional principal amount such as a loan or bond, although the instrument can be almost anything. Usually, the principal does not change hands. Each cash flow comprises one leg of the swap. One cash flow is generally fixed, while the other is variable and based on a benchmark interest rate, floating currency exchange rate or index price."
    , extendedContract: Close
    }
  , { name: "Sample swap contract 2"
    , type_: "Swap"
    , description: "A swap is a derivative contract through which two parties exchange the cash flows or liabilities from two different financial instruments. Most swaps involve cash flows based on a notional principal amount such as a loan or bond, although the instrument can be almost anything. Usually, the principal does not change hands. Each cash flow comprises one leg of the swap. One cash flow is generally fixed, while the other is variable and based on a benchmark interest rate, floating currency exchange rate or index price."
    , extendedContract: Close
    }
  ]
