-- | Misc. useful lenses.
module Playground.Lenses where

import Data.Function ((<<<))
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Ledger.Value (CurrencySymbol, TokenName, _CurrencySymbol, _TokenName)

_currencySymbol :: Lens' CurrencySymbol String
_currencySymbol = _CurrencySymbol <<< prop (SProxy :: SProxy "unCurrencySymbol")

_tokenName :: Lens' TokenName String
_tokenName = _TokenName <<< prop (SProxy :: SProxy "unTokenName")

_amount :: forall r a. Lens' { amount :: a | r } a
_amount = prop (SProxy :: SProxy "amount")

_recipient :: forall r a. Lens' { recipient :: a | r } a
_recipient = prop (SProxy :: SProxy "recipient")

_endpointName :: forall r a. Lens' { endpointName :: a | r } a
_endpointName = prop (SProxy :: SProxy "endpointName")
