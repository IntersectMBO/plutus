-- | Misc. useful lenses.
module Playground.Lenses where

import Data.Function ((<<<))
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription, _EndpointDescription)
import Ledger.Value (CurrencySymbol, TokenName, _CurrencySymbol, _TokenName)

_currencySymbol :: Lens' CurrencySymbol String
_currencySymbol = _CurrencySymbol <<< prop (SProxy :: SProxy "unCurrencySymbol")

_tokenName :: Lens' TokenName String
_tokenName = _TokenName <<< prop (SProxy :: SProxy "unTokenName")

_amount :: forall r a. Lens' { amount :: a | r } a
_amount = prop (SProxy :: SProxy "amount")

_recipient :: forall r a. Lens' { recipient :: a | r } a
_recipient = prop (SProxy :: SProxy "recipient")

_endpointDescription :: forall r a. Lens' { endpointDescription :: a | r } a
_endpointDescription = prop (SProxy :: SProxy "endpointDescription")

_getEndpointDescription :: Lens' EndpointDescription String
_getEndpointDescription = _EndpointDescription <<< prop (SProxy :: SProxy "getEndpointDescription")

_schema :: forall r a. Lens' { schema :: a | r } a
_schema = prop (SProxy :: SProxy "schema")
