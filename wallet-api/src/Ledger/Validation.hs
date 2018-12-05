{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | A model of the types involved in validating transactions. These types are intented to
--   be used in PLC scripts.
module Ledger.Validation
  ( Height(..) -- ** Transactions and related types
  , PendingTxOutRef(..)
              -- ** Hashes (see note [Hashes in validator scripts])
  , DataScriptHash(..)
  , RedeemerHash(..)
  , ValidatorHash(..)
  , TxHash(..)
  , plcDataScriptHash
  , plcValidatorDigest
  , plcRedeemerHash
  , plcTxHash
              -- * Pending transactions
  , PendingTx(..)
  , PendingTxOut(..)
  , PendingTxIn(..)
  , PendingTxOutType(..)
              -- * Oracles
  , Signed(..)
  , OracleValue(..)
  ) where

import           Codec.Serialise              (Serialise, deserialiseOrFail, serialise)
import           Crypto.Hash                  (Digest, SHA256, hash)
import           Data.Aeson                   (FromJSON, ToJSON (toJSON), withText)
import qualified Data.Aeson                   as JSON
import           Data.Bifunctor               (first)
import qualified Data.ByteArray               as BA
import qualified Data.ByteString.Base64       as Base64
import qualified Data.ByteString.Lazy         as BSL
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Swagger.Internal.Schema (ToSchema (declareNamedSchema), paramSchemaToSchema, plain)
import qualified Data.Text.Encoding           as TE
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import           Ledger.Types                 (PubKey (..), Signature (..), Value (..))
import qualified Ledger.Types                 as Ledger

-- Ignore newtype warnings related to `Oracle` and `Signed` because it causes
-- problems with the plugin
--
-- TODO: Remove annotation once `newtype Oracle = (...)` works
{-# ANN module "HLint: ignore Use newtype instead of data" #-}

data PendingTxOutType
  = PubKeyTxOut PubKey -- ^ Pub key address
  | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])
  deriving (Generic)

-- | Output of a pending transaction.
data PendingTxOut = PendingTxOut
  { pendingTxOutValue  :: Value
  , pendingTxOutHashes :: Maybe (ValidatorHash, DataScriptHash) -- ^ Hashes of validator script and data script
  , pendingTxOutData   :: PendingTxOutType
  } deriving (Generic)

data PendingTxOutRef = PendingTxOutRef
  { pendingTxOutRefId  :: TxHash -- ^ Transaction whose outputs are consumed
  , pendingTxOutRefIdx :: Int -- ^ Index into the referenced transaction's list of outputs
  , pendingTxOutSigs   :: [Signature]
  } deriving (Generic)

-- | Input of a pending transaction.
data PendingTxIn = PendingTxIn
  { pendingTxInRef       :: PendingTxOutRef
  , pendingTxInRefHashes :: Maybe (ValidatorHash, RedeemerHash) -- ^ Hashes of validator and redeemer scripts
  , pendingTxInValue     :: Value -- ^ Value consumed by this txn input
  } deriving (Generic)

-- | A pending transaction as seen by validator scripts.
data PendingTx a = PendingTx
  { pendingTxInputs      :: [PendingTxIn] -- ^ Transaction inputs
  , pendingTxOutputs     :: [PendingTxOut]
  , pendingTxFee         :: Value
  , pendingTxForge       :: Value
  , pendingTxBlockHeight :: Height
  , pendingTxSignatures  :: [Signature]
  , pendingTxOwnHash     :: a -- ^ Hash of the validator script that is currently running
  } deriving (Functor, Generic)

-- `OracleValue a` is the value observed at a time signed by
-- an oracle.
data OracleValue a =
  OracleValue (Signed (Height, a))
  deriving (Generic)

data Signed a =
  Signed (PubKey, a)
  deriving (Generic)

{- Note [Hashes in validator scripts]

We need to deal with hashes of four different things in a validator script:

1. Transactions
2. Validator scripts
3. Data scripts
4. Redeemer scripts

The mockchain code in [[Ledger.Types]] only deals with the hashes of(1)
and (2), and uses the [[Ledger.TxId']] and `Digest SHA256` types for
them.

In PLC validator scripts the situation is different: First, they need to work
with hashes of (1-4). Second, the `Digest SHA256` type is not available in PLC
- we have to represent all hashes as `ByteStrings`.

To ensure that we only compare hashes of the correct type inside a validator
script, we define a newtype for each of them, as well as functions for creating
them from the correct types in Haskell, and for comparing them (in
`Language.Plutus.Runtime.TH`).

-}
-- | PLC runtime representation of a `Digest SHA256`
newtype ValidatorHash =
  ValidatorHash BSL.ByteString
  deriving stock (Eq, Generic)
  deriving newtype (Serialise)

instance ToSchema ValidatorHash where
  declareNamedSchema _ = plain . paramSchemaToSchema $ (Proxy :: Proxy String)

instance ToJSON ValidatorHash where
  toJSON = JSON.String . TE.decodeUtf8 . Base64.encode . BSL.toStrict . serialise

instance FromJSON ValidatorHash where
  parseJSON = withText "ValidatorScript" $ \s -> do
    let ev = do
          eun64 <- Base64.decode . TE.encodeUtf8 $ s
          first show $ deserialiseOrFail $ BSL.fromStrict eun64
    case ev of
      Left e  -> fail e
      Right v -> pure v

newtype DataScriptHash =
  DataScriptHash BSL.ByteString
  deriving (Eq, Generic)

newtype RedeemerHash =
  RedeemerHash BSL.ByteString
  deriving (Eq, Generic)

newtype TxHash =
  TxHash BSL.ByteString
  deriving (Eq, Generic)

plcDataScriptHash :: Ledger.DataScript -> DataScriptHash
plcDataScriptHash = DataScriptHash . plcHash

plcValidatorDigest :: Digest SHA256 -> ValidatorHash
plcValidatorDigest = ValidatorHash . plcDigest

plcRedeemerHash :: Ledger.Redeemer -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcHash

plcTxHash :: Ledger.TxId' -> TxHash
plcTxHash = TxHash . plcDigest . Ledger.getTxId

-- | PLC-compatible hash of a hashable value
plcHash :: BA.ByteArrayAccess a => a -> BSL.ByteString
plcHash = plcDigest . hash

-- | Convert a `Digest SHA256` to a PLC `Hash`
plcDigest :: Digest SHA256 -> BSL.ByteString
plcDigest = serialise

-- | Blockchain height
--   TODO: Use [[Ledger.Height]] when Integer is supported
data Height = Height
  { getHeight :: Int
  } deriving (Eq, Ord, Show, Generic, FromJSON, ToJSON, ToSchema)

makeLift ''PendingTxOutType

makeLift ''PendingTxOut

makeLift ''PendingTxOutRef

makeLift ''PendingTxIn

makeLift ''PendingTx

makeLift ''OracleValue

makeLift ''Signed

makeLift ''ValidatorHash

makeLift ''DataScriptHash

makeLift ''RedeemerHash

makeLift ''TxHash

makeLift ''Height
