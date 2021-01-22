-- | Misc. useful lenses.
module Playground.Lenses where

import Data.Function ((<<<))
import Data.Map (Map)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Ledger.Index (UtxoIndex, _UtxoIndex)
import Plutus.V1.Ledger.Tx (TxOut, TxOutRef)
import Plutus.V1.Ledger.TxId (TxId)
import Plutus.V1.Ledger.Value (CurrencySymbol, TokenName, _CurrencySymbol, _TokenName)

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

_getEndpointDescription :: forall s r a. Newtype s { getEndpointDescription :: a | r } => Lens' s a
_getEndpointDescription = _Newtype <<< prop (SProxy :: SProxy "getEndpointDescription")

_endpointValue :: forall s r a. Newtype s { unEndpointValue :: a | r } => Lens' s a
_endpointValue = _Newtype <<< prop (SProxy :: SProxy "unEndpointValue")

_schema :: forall r a. Lens' { schema :: a | r } a
_schema = prop (SProxy :: SProxy "schema")

_txConfirmed :: forall s r a. Newtype s { unTxConfirmed :: a | r } => Lens' s a
_txConfirmed = _Newtype <<< prop (SProxy :: SProxy "unTxConfirmed")

_contractInstanceTag :: forall s r a. Newtype s { unContractInstanceTag :: a | r } => Lens' s a
_contractInstanceTag = _Newtype <<< prop (SProxy :: SProxy "unContractInstanceTag")

_txId :: Lens' TxId String
_txId = _Newtype <<< prop (SProxy :: SProxy "getTxId")

_utxoIndexEntries :: Lens' UtxoIndex (Map TxOutRef TxOut)
_utxoIndexEntries = _UtxoIndex <<< prop (SProxy :: SProxy "getIndex")

_aeDescription :: forall s r a. Newtype s { aeDescription :: a | r } => Lens' s a
_aeDescription = _Newtype <<< prop (SProxy :: SProxy "aeDescription")

_aeMetadata :: forall s r a. Newtype s { aeMetadata :: a | r } => Lens' s a
_aeMetadata = _Newtype <<< prop (SProxy :: SProxy "aeMetadata")
