{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Ledger.Orphans where

import           Crypto.Hash                (Digest, SHA256)
import qualified Data.Aeson.Extras          as JSON
import           Data.Bifunctor             (bimap)
import           Data.ByteString
import qualified Data.Text                  as Text
import           Data.Typeable
import           IOTS                       (IotsType (iotsDefinition))
import qualified Language.PlutusTx.AssocMap as Map
import           Language.PlutusTx.Data
import           Plutus.V1.Ledger.Ada
import           Plutus.V1.Ledger.Address
import           Plutus.V1.Ledger.Bytes
import           Plutus.V1.Ledger.Crypto
import           Plutus.V1.Ledger.Interval
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Slot
import           Plutus.V1.Ledger.Tx
import           Plutus.V1.Ledger.TxId
import           Plutus.V1.Ledger.Value
import           Web.HttpApiData            (FromHttpApiData (..), ToHttpApiData (..))

deriving anyclass instance IotsType Address
deriving anyclass instance IotsType Slot
deriving anyclass instance IotsType Tx
deriving anyclass instance IotsType TxOutRef
deriving anyclass instance IotsType TxInType
deriving anyclass instance IotsType TxIn
deriving anyclass instance IotsType TxOutType
deriving anyclass instance IotsType TxOut
deriving anyclass instance IotsType TxOutTx
deriving anyclass instance IotsType TxId

deriving anyclass instance IotsType Ada
deriving anyclass instance IotsType CurrencySymbol
deriving anyclass instance IotsType TokenName
deriving anyclass instance IotsType Value

deriving anyclass instance IotsType PubKey
deriving anyclass instance IotsType PubKeyHash
deriving anyclass instance IotsType Signature

instance ToHttpApiData PrivateKey where
    toUrlPiece = toUrlPiece . getPrivateKey

instance FromHttpApiData PrivateKey where
    parseUrlPiece a = PrivateKey <$> parseUrlPiece a

deriving anyclass instance (Typeable a, IotsType a) => IotsType (Interval a)
deriving anyclass instance (Typeable a, IotsType a) => IotsType (Extended a)
deriving anyclass instance (Typeable a, IotsType a) => IotsType (UpperBound a)
deriving anyclass instance (Typeable a, IotsType a) => IotsType (LowerBound a)

instance IotsType LedgerBytes where
  iotsDefinition = iotsDefinition @String
instance ToHttpApiData LedgerBytes where
    toUrlPiece = JSON.encodeByteString . bytes
instance FromHttpApiData LedgerBytes where
    parseUrlPiece = bimap Text.pack fromBytes . JSON.tryDecode

instance IotsType Script where
  iotsDefinition = iotsDefinition @String
deriving anyclass instance IotsType Validator
instance IotsType ValidatorHash where
    iotsDefinition = iotsDefinition @LedgerBytes
deriving anyclass instance IotsType Redeemer
instance IotsType RedeemerHash where
    iotsDefinition = iotsDefinition @LedgerBytes
deriving anyclass instance IotsType Datum
instance IotsType DatumHash where
    iotsDefinition = iotsDefinition @LedgerBytes
deriving anyclass instance IotsType MonetaryPolicy
instance IotsType MonetaryPolicyHash where
    iotsDefinition = iotsDefinition @LedgerBytes

instance IotsType (Digest SHA256) where
  iotsDefinition = iotsDefinition @String

instance IotsType ByteString where
  iotsDefinition = iotsDefinition @String

instance IotsType Data where
  iotsDefinition = iotsDefinition @String

instance (Typeable k, Typeable v, IotsType k, IotsType v) =>
         IotsType (Map.Map k v)
