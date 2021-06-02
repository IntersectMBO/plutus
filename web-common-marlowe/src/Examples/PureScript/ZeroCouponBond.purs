module Examples.PureScript.ZeroCouponBond
  ( contractTemplate
  , fullExtendedContract
  , metaData
  , fixedTimeoutContract
  ) where

import Prelude
import Data.BigInteger (fromInt)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Template (TemplateContent(..), fillTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract: fixedTimeoutContract }

fixedTimeoutContract :: Contract
fixedTimeoutContract =
  fillTemplate
    ( TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Initial exchange deadline" /\ fromInt 60
              , "Maturity exchange deadline" /\ fromInt 150
              ]
        , valueContent:
            Map.empty
        }
    )
    fullExtendedContract

metaData :: MetaData
metaData = Metadata.zeroCouponBond

ada :: Token
ada = Token "" ""

discountedPrice :: Value
discountedPrice = ConstantParam "Discounted price"

notionalPrice :: Value
notionalPrice = ConstantParam "Notional price"

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

fullExtendedContract :: Contract
fullExtendedContract =
  transfer initialExchange investor issuer discountedPrice
    $ transfer maturityExchangeTimeout issuer investor notionalPrice
        Close
