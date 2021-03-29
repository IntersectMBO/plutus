module Marlowe.Market.Contract5
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (fromInt)
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

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

extendedContract :: Contract
extendedContract =
  makeDeposit adaProvider adaDepositTimeout Close
    $ makeDeposit dollarProvider dollarDepositTimeout Close
    $ makePayment adaProvider dollarProvider
    $ makePayment dollarProvider adaProvider
        Close
