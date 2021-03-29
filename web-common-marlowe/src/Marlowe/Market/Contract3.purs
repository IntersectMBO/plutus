module Marlowe.Market.Contract3
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData = Metadata.zeroCouponBond

ada :: Token
ada = Token "" ""

discountedPrice :: Value
discountedPrice = ConstantParam "Discounted price"

notional :: Value
notional = ConstantParam "Notional"

investor :: Party
investor = Role "Investor"

issuer :: Party
issuer = Role "Issuer"

initialExchange :: Timeout
initialExchange = SlotParam "Initial exchange deadline"

maturityExchangeTimeout :: Timeout
maturityExchangeTimeout = SlotParam "Maturity exchange deadline"

transfer :: Timeout -> Party -> Party -> Value -> Contract -> Contract
transfer timeout from to amount continuation =
  When
    [ Case (Deposit from from ada amount)
        (Pay from (Party to) ada amount continuation)
    ]
    timeout
    Close

extendedContract :: Contract
extendedContract =
  transfer initialExchange investor issuer discountedPrice
    $ transfer maturityExchangeTimeout issuer investor notional
        Close
