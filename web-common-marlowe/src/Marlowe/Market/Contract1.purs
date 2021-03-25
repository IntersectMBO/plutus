module Marlowe.Market.Contract1
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
  { contractType: Escrow
  , contractName: "Simple escrow"
  , contractDescription: "Regulates a money exchange between a \"Buyer\" and a \"Seller\". If there is a disagreement, an \"Arbiter\" will decide whether the money is refunded or paid to the \"Seller\"."
  , roleDescriptions:
      fromFoldable
        [ "Arbiter" /\ "The party that will choose who gets the money in the event of a disagreement between the \"Buyer\" and the \"Seller\" about the outcome."
        , "Buyer" /\ "The party that wants to buy the item. Payment is made to the seller if they acknowledge receiving the item. "
        , "Seller" /\ "The party that wants to sell the item. They receive the payment if the exchange is uneventful."
        ]
  , slotParameterDescriptions:
      fromFoldable
        [ "Buyer's deposit timeout" /\ "Deadline by which the \"Buyer\" must deposit the selling  \"Price\" in the contract."
        , "Buyer's dispute timeout" /\ "Deadline by which, if the \"Buyer\" has not opened a dispute, the \"Seller\" will be paid."
        , "Seller's response timeout" /\ "Deadline by which, if the \"Seller\" has not responded to the dispute, the \"Buyer\" will be refunded."
        , "Timeout for arbitrage" /\ "Deadline by which, if the \"Arbiter\" has not resolved the dispute, the \"Buyer\" will be refunded."
        ]
  , valueParameterDescriptions:
      fromFoldable
        [ "Price" /\ "Amount of Lovelace to be paid by the \"Buyer\" for the item." ]
  , choiceDescriptions:
      fromFoldable
        [ "Confirm problem" /\ "Acknowledge there was a problem and a refund must be granted."
        , "Dismiss claim" /\ "The \"Arbiter\" does not see any problem with the exchange and the \"Seller\" must be paid."
        , "Dispute problem" /\ "The \"Seller\" disagrees with the \"Buyer\" about the claim that something went wrong."
        , "Everything is alright" /\ "The transaction was uneventful, \"Buyer\" agrees to pay the \"Seller\"."
        , "Report problem" /\ "The \"Buyer\" claims not having received the product that was paid for as agreed and would like a refund."
        ]
  }

extendedContract :: Contract
extendedContract =
  When
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
                            ( When
                                [ Case
                                    ( Choice
                                        ( ChoiceId
                                            "Dismiss claim"
                                            (Role "Arbiter")
                                        )
                                        [ Bound zero zero ]
                                    )
                                    ( Pay
                                        (Role "Buyer")
                                        (Party (Role "Seller"))
                                        (Token "" "")
                                        (ConstantParam "Price")
                                        Close
                                    )
                                , Case
                                    ( Choice
                                        ( ChoiceId
                                            "Confirm problem"
                                            (Role "Arbiter")
                                        )
                                        [ Bound one one ]
                                    )
                                    Close
                                ]
                                (SlotParam "Timeout for arbitrage")
                                Close
                            )
                        ]
                        (SlotParam "Seller's response timeout")
                        Close
                    )
                )
            ]
            (SlotParam "Buyer's dispute timeout")
            Close
        )
    ]
    (SlotParam "Buyer's deposit timeout")
    Close
