-- | Utility functions for creating script contexts.
module PlutusBenchmark.Marlowe.Util
  ( -- * Conversion
    lovelace
  , makeInput
  , makeOutput
  , makeRedeemerMap
  , makeDatumMap
  , makeBuiltinData
  ) where

import Codec.Serialise (deserialise)
import PlutusLedgerApi.V2
  ( Address (Address)
  , BuiltinData
  , Credential (..)
  , Datum (Datum)
  , DatumHash
  , LedgerBytes (getLedgerBytes)
  , OutputDatum (NoOutputDatum, OutputDatumHash)
  , Redeemer (Redeemer)
  , ScriptHash
  , ScriptPurpose
  , TxId
  , TxInInfo (..)
  , TxOut (..)
  , TxOutRef (TxOutRef)
  , Value
  , adaSymbol
  , adaToken
  , dataToBuiltinData
  , fromBuiltin
  , singleton
  )

import Data.ByteString.Lazy qualified as LBS (fromStrict)
import PlutusTx.AssocMap qualified as AM (Map, singleton)

-- | Integer to lovelace.
lovelace :: Integer -> Value
lovelace = singleton adaSymbol adaToken

-- Construct a `TxInInfo`.
makeInput
  :: TxId
  -> Integer
  -> Credential
  -> Value
  -> Maybe DatumHash
  -> Maybe ScriptHash
  -> TxInInfo
makeInput txId txIx credential value datum script =
  TxInInfo
    (TxOutRef txId txIx)
    (makeOutput credential value datum script)

-- Construct a `TxOut`.
makeOutput
  :: Credential
  -> Value
  -> Maybe DatumHash
  -> Maybe ScriptHash
  -> TxOut
makeOutput credential value =
  TxOut (Address credential Nothing) value
    . maybe NoOutputDatum OutputDatumHash

-- Construct a map of redeemers.
makeRedeemerMap
  :: ScriptPurpose
  -> LedgerBytes
  -> AM.Map ScriptPurpose Redeemer
makeRedeemerMap = (. (Redeemer . makeBuiltinData)) . AM.singleton

-- Construct a map of datum hashes to datums.
makeDatumMap :: DatumHash -> LedgerBytes -> AM.Map DatumHash Datum
makeDatumMap = (. (Datum . makeBuiltinData)) . AM.singleton

-- Convert ledger bytes to builtin data.
makeBuiltinData :: LedgerBytes -> BuiltinData
makeBuiltinData =
  dataToBuiltinData
    . deserialise
    . LBS.fromStrict
    . fromBuiltin
    . getLedgerBytes
