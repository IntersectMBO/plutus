module Marlowe.Market.Contract2
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.Map (fromFoldable)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (Action(..), Case(..), Contract(..), ContractType(..), Observation(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData =
  { contractType: EscrowWithCollatoral
  , contractName: "Escrow with Collatoral"
  , contractDescription: "Variation of Escrow contract that relies on a mutual collateral insteead of trusted third-party."
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
