module Marlowe.Market.Contract2
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
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData =
  { contractType: EscrowWithCollateral
  , contractName: "Escrow with collateral"
  , contractDescription: "Regulates a money exchange between a \"Buyer\" and a \"Seller\" using a collateral from both parties to incentivize collaboration. If there is a disagreement the collateral is burned."
  , roleDescriptions:
      fromFoldable
        [ "Buyer" /\ "The party that pays for the item on sale."
        , "Seller" /\ "The party that sells the item and gets the money if the exchange is successful."
        ]
  , slotParameterDescriptions:
      fromFoldable
        [ "Collateral deposit by seller timeout" /\ "The deadline by which the \"Seller\" must deposit the \"Collateral amount\" in the contract."
        , "Deposit of collateral by buyer timeout" /\ "The deadline by which the \"Buyer\" must deposit the \"Collateral amount\" in the contract."
        , "Deposit of price by buyer timeout" /\ "The deadline by which the \"Buyer\" must deposit the \"Price\" in the contract."
        , "Dispute by buyer timeout" /\ "The deadline by which, if the \"Buyer\" has not opened a dispute, the \"Seller\" will be paid."
        , "Seller's response timeout" /\ "The deadline by which, if the \"Seller\" has not responded to the dispute, the \"Buyer\" will be refunded."
        ]
  , valueParameterDescriptions:
      fromFoldable
        [ "Collateral amount" /\ "The amount of Lovelace to be deposited by both parties at the start of the contract to serve as an incentive for collaboration."
        , "Price" /\ "The amount of Lovelace to be paid by the \"Buyer\" as part of the exchange."
        ]
  , choiceDescriptions:
      fromFoldable
        [ "Confirm problem" /\ "Acknowledge that there was a problem and a refund must be granted."
        , "Dispute problem" /\ "The \"Seller\" disagrees with the \"Buyer\" about the claim that something went wrong and the collateral will be burnt."
        , "Everything is alright" /\ "The exchange was successful and the \"Buyer\" agrees to pay the \"Seller\"."
        , "Report problem" /\ "The \"Buyer\" claims not having received the product that was paid for as agreed and would like a refund."
        ]
  }

extendedContract :: Contract
extendedContract =
  When
    [ Case
        ( Deposit
            (Role "Seller")
            (Role "Seller")
            (Token "" "")
            (ConstantParam "Collateral amount")
        )
        ( When
            [ Case
                ( Deposit
                    (Role "Buyer")
                    (Role "Buyer")
                    (Token "" "")
                    (ConstantParam "Collateral amount")
                )
                ( When
                    [ Case
                        ( Deposit
                            (Role "Seller")
                            (Role "Buyer")
                            (Token "" "")
                            (ConstantParam "Price")
                        )
                        ( When
                            [ Case
                                ( Choice
                                    ( ChoiceId
                                        "Everything is alright"
                                        (Role "Buyer")
                                    )
                                    [ Bound zero zero ]
                                )
                                Close
                            , Case
                                ( Choice
                                    ( ChoiceId
                                        "Report problem"
                                        (Role "Buyer")
                                    )
                                    [ Bound one one ]
                                )
                                ( Pay
                                    (Role "Seller")
                                    (Account (Role "Buyer"))
                                    (Token "" "")
                                    (ConstantParam "Price")
                                    ( When
                                        [ Case
                                            ( Choice
                                                ( ChoiceId
                                                    "Confirm problem"
                                                    (Role "Seller")
                                                )
                                                [ Bound one one ]
                                            )
                                            Close
                                        , Case
                                            ( Choice
                                                ( ChoiceId
                                                    "Dispute problem"
                                                    (Role "Seller")
                                                )
                                                [ Bound zero zero ]
                                            )
                                            ( Pay
                                                (Role "Seller")
                                                (Party (PK "0000000000000000000000000000000000000000000000000000000000000000"))
                                                (Token "" "")
                                                (ConstantParam "Collateral amount")
                                                ( Pay
                                                    (Role "Buyer")
                                                    (Party (PK "0000000000000000000000000000000000000000000000000000000000000000"))
                                                    (Token "" "")
                                                    (ConstantParam "Collateral amount")
                                                    Close
                                                )
                                            )
                                        ]
                                        (SlotParam "Seller's response timeout")
                                        Close
                                    )
                                )
                            ]
                            (SlotParam "Dispute by buyer timeout")
                            Close
                        )
                    ]
                    (SlotParam "Deposit of price by buyer timeout")
                    Close
                )
            ]
            (SlotParam "Deposit of collateral by buyer timeout")
            ( Pay
                (Role "Seller")
                (Party (Role "Seller"))
                (Token "" "")
                (ConstantParam "Collateral amount")
                Close
            )
        )
    ]
    (SlotParam "Collateral deposit by seller timeout")
    Close
