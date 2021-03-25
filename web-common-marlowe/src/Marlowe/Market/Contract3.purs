module Marlowe.Market.Contract3
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.Map (fromFoldable)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (Action(..), Case(..), Contract(..), ContractType(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData =
  { contractType: ZeroCouponBond
  , contractName: "Zero Coupon Bond"
  , contractDescription: "A simple loan. The investor pays the issuer the discounted price at the start, and is repaid the full (notional) price at the end."
  , roleDescriptions:
      fromFoldable
        [ "Investor" /\ "The party that buys the bond at a discounted price, i.e. makes the loan."
        , "Issuer" /\ "The party that issues the bond, i.e. receives the loan."
        ]
  , slotParameterDescriptions:
      fromFoldable
        [ "Initial exchange deadline" /\ "The \"Investor\" must deposit the discounted price of the bond before this deadline or the offer will expire."
        , "Maturity exchange deadline" /\ "The \"Issuer\" must deposit the full price of the bond before this deadline or it will default."
        ]
  , valueParameterDescriptions:
      fromFoldable
        [ "Discounted price" /\ "The price in Lovelace of the Zero Coupon Bond at the start date."
        , "Notional" /\ "The full price in Lovelace of the Zero Coupon Bond."
        ]
  , choiceDescriptions: mempty
  }

extendedContract :: Contract
extendedContract =
  When
    [ Case
        ( Deposit
            (Role "Investor")
            (Role "Investor")
            (Token "" "")
            (ConstantParam "Discounted price")
        )
        ( Pay
            (Role "Investor")
            (Party (Role "Issuer"))
            (Token "" "")
            (ConstantParam "Discounted price")
            ( When
                [ Case
                    ( Deposit
                        (Role "Issuer")
                        (Role "Issuer")
                        (Token "" "")
                        (ConstantParam "Notional")
                    )
                    ( Pay
                        (Role "Issuer")
                        (Party (Role "Investor"))
                        (Token "" "")
                        (ConstantParam "Notional")
                        Close
                    )
                ]
                (SlotParam "Maturity exchange deadline")
                Close
            )
        )
    ]
    (SlotParam "Initial exchange deadline")
    Close
