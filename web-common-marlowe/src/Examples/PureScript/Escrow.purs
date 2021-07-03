module Examples.PureScript.Escrow
  ( contractTemplate
  , fullExtendedContract
  , metaData
  , fixedTimeoutContract
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Data.Map as Map
import Data.Tuple.Nested (type (/\), (/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Template (TemplateContent(..), fillTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..), ChoiceName)

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract: fixedTimeoutContract }

fixedTimeoutContract :: Contract
fixedTimeoutContract =
  fillTemplate
    ( TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Buyer's deposit timeout" /\ fromInt 600
              , "Buyer's dispute timeout" /\ fromInt 1800
              , "Seller's response timeout" /\ fromInt 2400
              , "Timeout for arbitrage" /\ fromInt 3600
              ]
        , valueContent: Map.empty
        }
    )
    fullExtendedContract

metaData :: MetaData
metaData = Metadata.escrow

ada :: Token
ada = Token "" ""

buyer :: Party
buyer = Role "Buyer"

seller :: Party
seller = Role "Seller"

arbiter :: Party
arbiter = Role "Arbiter"

price :: Value
price = ConstantParam "Price"

depositTimeout :: Timeout
depositTimeout = SlotParam "Buyer's deposit timeout"

disputeTimeout :: Timeout
disputeTimeout = SlotParam "Buyer's dispute timeout"

answerTimeout :: Timeout
answerTimeout = SlotParam "Seller's response timeout"

arbitrageTimeout :: Timeout
arbitrageTimeout = SlotParam "Timeout for arbitrage"

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
