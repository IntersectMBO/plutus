module Examples.PureScript.Escrow
  ( contractTemplate
  , fullExtendedContract
  , metaData
  , fixedTimeoutContract
  , defaultSlotContent
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Data.Map as Map
import Data.Map (Map)
import Data.Tuple.Nested (type (/\), (/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Template (TemplateContent(..), fillTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..), ChoiceName)

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract: fullExtendedContract }

fixedTimeoutContract :: Contract
fixedTimeoutContract =
  fillTemplate
    ( TemplateContent
        { slotContent: defaultSlotContent
        , valueContent: Map.empty
        }
    )
    fullExtendedContract

defaultSlotContent :: Map String BigInteger
defaultSlotContent =
  Map.fromFoldable
    [ "Payment deadline" /\ fromInt 600
    , "Complaint response deadline" /\ fromInt 1800
    , "Complaint deadline" /\ fromInt 2400
    , "Mediation deadline" /\ fromInt 3600
    ]

metaData :: MetaData
metaData = Metadata.escrow

ada :: Token
ada = Token "" ""

buyer :: Party
buyer = Role "Buyer"

seller :: Party
seller = Role "Seller"

arbiter :: Party
arbiter = Role "Mediator"

price :: Value
price = ConstantParam "Price"

depositTimeout :: Timeout
depositTimeout = SlotParam "Payment deadline"

disputeTimeout :: Timeout
disputeTimeout = SlotParam "Complaint response deadline"

answerTimeout :: Timeout
answerTimeout = SlotParam "Complaint deadline"

arbitrageTimeout :: Timeout
arbitrageTimeout = SlotParam "Mediation deadline"

choice :: ChoiceName -> Party -> BigInteger -> Contract -> Case
choice choiceName chooser choiceValue continuation =
  Case
    ( Choice (ChoiceId choiceName chooser)
        [ Bound choiceValue choiceValue ]
    )
    continuation

deposit :: Timeout -> Contract -> Contract -> Contract
deposit timeout timeoutContinuation continuation =
  When [ Case (Deposit seller buyer ada price) continuation ]
    timeout
    timeoutContinuation

choices :: Timeout -> Party -> Contract -> Array (BigInteger /\ ChoiceName /\ Contract) -> Contract
choices timeout chooser timeoutContinuation list =
  When
    ( do
        (choiceValue /\ choiceName /\ continuation) <- list
        pure $ choice choiceName chooser choiceValue continuation
    )
    timeout
    timeoutContinuation

sellerToBuyer :: Contract -> Contract
sellerToBuyer = Pay seller (Account buyer) ada price

paySeller :: Contract -> Contract
paySeller = Pay buyer (Party seller) ada price

fullExtendedContract :: Contract
fullExtendedContract =
  deposit depositTimeout Close
    $ choices disputeTimeout buyer Close
        [ (zero /\ "Everything is alright" /\ Close)
        , ( one /\ "Report problem"
              /\ ( sellerToBuyer
                    $ choices answerTimeout seller Close
                        [ (one /\ "Confirm problem" /\ Close)
                        , ( zero /\ "Dispute problem"
                              /\ choices arbitrageTimeout arbiter Close
                                  [ (zero /\ "Dismiss claim" /\ paySeller Close)
                                  , (one /\ "Confirm problem" /\ Close)
                                  ]
                          )
                        ]
                )
          )
        ]
