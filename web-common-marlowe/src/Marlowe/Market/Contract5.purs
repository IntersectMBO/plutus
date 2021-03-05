module Marlowe.Market.Contract5
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.Map (fromFoldable)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (Action(..), Case(..), Contract(..), ContractTemplate, ContractType(..), MetaData, Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData =
  { contractType: S
  , contractDescription: "A swap is a derivative contract through which two parties exchange the cash flows or liabilities from two different financial instruments. Most swaps involve cash flows based on a notional principal amount such as a loan or bond, although the instrument can be almost anything. Usually, the principal does not change hands. Each cash flow comprises one leg of the swap. One cash flow is generally fixed, while the other is variable and based on a benchmark interest rate, floating currency exchange rate or index price."
  , roleDescriptions:
      fromFoldable
        [ "alice" /\ "about the alice role"
        , "bob" /\ "about the bob role"
        ]
  , slotParameterDescriptions:
      fromFoldable
        [ "aliceTimeout" /\ "about the aliceTimeout"
        , "arbitrageTimeout" /\ "about the arbitrageTimeout"
        , "bobTimeout" /\ "about the bobTimeout"
        , "depositSlot" /\ "about the depositSlot"
        ]
  , valueParameterDescriptions:
      fromFoldable
        [ "amount" /\ "about the amount" ]
  , choiceDescriptions:
      fromFoldable
        [ "choice" /\ "about the choice" ]
  }

extendedContract :: Contract
extendedContract =
  When
    [ Case
        ( Deposit
            (Role "alice")
            (Role "alice")
            (Token "" "")
            (ConstantParam "amount")
        )
        ( When
            [ Case
                ( Choice
                    ( ChoiceId
                        "choice"
                        (Role "alice")
                    )
                    [ Bound zero one ]
                )
                ( When
                    [ Case
                        ( Choice
                            ( ChoiceId
                                "choice"
                                (Role "bob")
                            )
                            [ Bound zero one ]
                        )
                        ( If
                            ( ValueEQ
                                ( ChoiceValue
                                    ( ChoiceId
                                        "choice"
                                        (Role "alice")
                                    )
                                )
                                ( ChoiceValue
                                    ( ChoiceId
                                        "choice"
                                        (Role "bob")
                                    )
                                )
                            )
                            ( If
                                ( ValueEQ
                                    ( ChoiceValue
                                        ( ChoiceId
                                            "choice"
                                            (Role "alice")
                                        )
                                    )
                                    (Constant zero)
                                )
                                ( Pay
                                    (Role "alice")
                                    (Party (Role "bob"))
                                    (Token "" "")
                                    (ConstantParam "amount")
                                    Close
                                )
                                Close
                            )
                            ( When
                                [ Case
                                    ( Choice
                                        ( ChoiceId
                                            "choice"
                                            (Role "carol")
                                        )
                                        [ Bound one one ]
                                    )
                                    Close
                                , Case
                                    ( Choice
                                        ( ChoiceId
                                            "choice"
                                            (Role "carol")
                                        )
                                        [ Bound one one ]
                                    )
                                    ( Pay
                                        (Role "alice")
                                        (Party (Role "bob"))
                                        (Token "" "")
                                        (ConstantParam "amount")
                                        Close
                                    )
                                ]
                                (SlotParam "arbitrageTimeout")
                                Close
                            )
                        )
                    ]
                    (SlotParam "bobTimeout")
                    ( When
                        [ Case
                            ( Choice
                                ( ChoiceId
                                    "choice"
                                    (Role "carol")
                                )
                                [ Bound one one ]
                            )
                            Close
                        , Case
                            ( Choice
                                ( ChoiceId
                                    "choice"
                                    (Role "carol")
                                )
                                [ Bound one one ]
                            )
                            ( Pay
                                (Role "alice")
                                (Party (Role "bob"))
                                (Token "" "")
                                (ConstantParam "amount")
                                Close
                            )
                        ]
                        (SlotParam "arbitrageTimeout")
                        Close
                    )
                )
            ]
            (SlotParam "aliceTimeout")
            ( When
                [ Case
                    ( Choice
                        ( ChoiceId
                            "choice"
                            (Role "carol")
                        )
                        [ Bound one one ]
                    )
                    Close
                , Case
                    ( Choice
                        ( ChoiceId
                            "choice"
                            (Role "carol")
                        )
                        [ Bound zero zero ]
                    )
                    ( Pay
                        (Role "alice")
                        (Party (Role "bob"))
                        (Token "" "")
                        (ConstantParam "amount")
                        Close
                    )
                ]
                (SlotParam "arbitrageTimeout")
                Close
            )
        )
    ]
    (SlotParam "depositSlot")
    Close
