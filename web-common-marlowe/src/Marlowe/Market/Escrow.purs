module Marlowe.Market.Escrow
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Tuple.Nested (type (/\), (/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Party(..), Token(..), ChoiceName)

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

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

extendedContract :: Contract
extendedContract =
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
