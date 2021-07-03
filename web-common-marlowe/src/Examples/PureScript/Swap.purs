module Examples.PureScript.Swap
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
              [ "Timeout for Ada deposit" /\ fromInt 600
              , "Timeout for dollar deposit" /\ fromInt 1200
              ]
        , valueContent:
            Map.empty
        }
    )
    fullExtendedContract

metaData :: MetaData
metaData = Metadata.swap

ada :: Token
ada = Token "" ""

lovelacePerAda :: Value
lovelacePerAda = Constant (fromInt 1000000)

amountOfAda :: Value
amountOfAda = ConstantParam "Amount of Ada"

amountOfLovelace :: Value
amountOfLovelace = MulValue lovelacePerAda amountOfAda

amountOfDollars :: Value
amountOfDollars = ConstantParam "Amount of dollars"

adaDepositTimeout :: Timeout
adaDepositTimeout = SlotParam "Timeout for Ada deposit"

dollarDepositTimeout :: Timeout
dollarDepositTimeout = SlotParam "Timeout for dollar deposit"

dollars :: Token
dollars = Token "85bb65" "dollar"

type SwapParty
  = { party :: Party
    , currency :: Token
    , amount :: Value
    }

adaProvider :: SwapParty
adaProvider =
  { party: Role "Ada provider"
  , currency: ada
  , amount: amountOfLovelace
  }

dollarProvider :: SwapParty
dollarProvider =
  { party: Role "Dollar provider"
  , currency: dollars
  , amount: amountOfDollars
  }

makeDeposit :: SwapParty -> Timeout -> Contract -> Contract -> Contract
makeDeposit src timeout timeoutContinuation continuation =
  When
    [ Case (Deposit src.party src.party src.currency src.amount)
        continuation
    ]
    timeout
    timeoutContinuation

makePayment :: SwapParty -> SwapParty -> Contract -> Contract
makePayment src dest continuation = Pay src.party (Party $ dest.party) src.currency src.amount continuation

fullExtendedContract :: Contract
fullExtendedContract =
  makeDeposit adaProvider adaDepositTimeout Close
    $ makeDeposit dollarProvider dollarDepositTimeout Close
    $ makePayment adaProvider dollarProvider
    $ makePayment dollarProvider adaProvider
        Close
