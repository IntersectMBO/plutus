module Marlowe.Market.Contract5
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (fromInt) as BigInteger
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
  { contractType: Swap
  , contractName: "Swap of Ada and dollar tokens"
  , contractDescription: "Takes Ada from one party and dollar tokens from another party, and it swaps them atomically."
  , roleDescriptions:
      fromFoldable
        [ "Ada provider" /\ "The party that provides the Ada."
        , "Dollar provider" /\ "The party that provides the dollar tokens."
        ]
  , slotParameterDescriptions:
      fromFoldable
        [ "Timeout for Ada deposit" /\ "Deadline by which Ada must be deposited."
        , "Timeout for dollar deposit" /\ "Deadline by which dollars tokens must be deposited (must be after the deadline for Ada deposit)."
        ]
  , valueParameterDescriptions:
      fromFoldable
        [ "Amount of Ada" /\ "Amount of Ada to be exchanged for dollars."
        , "Amount of dollars" /\ "Amount of dollars tokens to be exchanged for Ada."
        ]
  , choiceDescriptions: mempty
  }

extendedContract :: Contract
extendedContract =
  When
    [ Case
        ( Deposit
            (Role "Ada provider")
            (Role "Ada provider")
            (Token "" "")
            ( MulValue
                (Constant $ BigInteger.fromInt 1000000)
                (ConstantParam "Amount of Ada")
            )
        )
        ( When
            [ Case
                ( Deposit
                    (Role "Dollar provider")
                    (Role "Dollar provider")
                    (Token "85bb65" "dollar")
                    (ConstantParam "Amount of dollars")
                )
                ( Pay
                    (Role "Ada provider")
                    (Party (Role "Dollar provider"))
                    (Token "" "")
                    ( MulValue
                        (Constant $ BigInteger.fromInt 1000000)
                        (ConstantParam "Amount of Ada")
                    )
                    ( Pay
                        (Role "Dollar provider")
                        (Party (Role "Ada provider"))
                        (Token "85bb65" "dollar")
                        (ConstantParam "Amount of dollars")
                        Close
                    )
                )
            ]
            (SlotParam "Timeout for dollar deposit")
            Close
        )
    ]
    (SlotParam "Timeout for Ada deposit")
    Close
