module Examples.PureScript.ZeroCouponBond
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
import Data.Tuple.Nested ((/\))
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Template (TemplateContent(..), fillTemplate)
import Marlowe.Semantics (Party(..), Token(..))

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
    [ "Initial exchange deadline" /\ fromInt 600
    , "Maturity exchange deadline" /\ fromInt 1500
    ]

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
