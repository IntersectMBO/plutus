{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
-- | A model of the types involved in transactions. These types are intented to
--   be used in PLC scripts.
module Wallet.UTXO.Runtime (-- * Transactions and related types
                PubKey(..)
              , Value
              , Height
              , PendingTxOutRef(..)
              , Hash
              , plcHash
              , plcDigest
              , Signature(..)
              -- * Pending transactions
              , PendingTx(..)
              , PendingTxOut(..)
              , PendingTxIn(..)
              , PendingTxOutType(..)
              -- * Oracles
              , Signed(..)
              , OracleValue(..)
              ) where

import           Codec.Serialise      (serialise)
import           Crypto.Hash          (Digest, SHA256, hash)
import qualified Data.ByteArray       as BA
import qualified Data.ByteString.Lazy as BSL
import           GHC.Generics         (Generic)
import           Language.Plutus.Lift (LiftPlc (..), TypeablePlc (..))
import           Wallet.UTXO.Types    (PubKey (..), Signature (..))

data PendingTxOutType =
    PubKeyTxOut PubKey -- ^ Pub key address
    | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])
    deriving Generic

instance TypeablePlc PendingTxOutType
instance LiftPlc PendingTxOutType

-- | Output of a pending transaction.
data PendingTxOut = PendingTxOut {
    pendingTxOutValue  :: Value,
    pendingTxOutHashes :: Maybe (Hash, Hash), -- ^ Hashes of validator script and data script
    pendingTxOutData   :: PendingTxOutType
    } deriving Generic

instance TypeablePlc PendingTxOut
instance LiftPlc PendingTxOut

data PendingTxOutRef = PendingTxOutRef {
    pendingTxOutRefId  :: Hash, -- ^ Transaction whose outputs are consumed
    pendingTxOutRefIdx :: Int, -- ^ Index into the referenced transaction's list of outputs
    pendingTxOutSigs   :: [Signature]
    } deriving Generic

instance TypeablePlc PendingTxOutRef
instance LiftPlc PendingTxOutRef

-- | Input of a pending transaction.
data PendingTxIn = PendingTxIn {
    pendingTxInRef       :: PendingTxOutRef,
    pendingTxInRefHashes :: Maybe (Hash, Hash), -- ^ Hashes of validator and redeemer scripts
    pendingTxInValue     :: Value -- ^ Value consumed by this txn input
    } deriving Generic

instance TypeablePlc PendingTxIn
instance LiftPlc PendingTxIn

-- | A pending transaction as seen by validator scripts.
data PendingTx = PendingTx {
    pendingTxInputs      :: [PendingTxIn], -- ^ Transaction inputs
    pendingTxOutputs     :: [PendingTxOut],
    pendingTxFee         :: Value,
    pendingTxForge       :: Value,
    pendingTxBlockHeight :: Height,
    pendingTxSignatures  :: [Signature]
    } deriving Generic

instance TypeablePlc PendingTx
instance LiftPlc PendingTx

-- `OracleValue a` is the value observed at a time signed by
-- an oracle.
newtype OracleValue a = OracleValue (Signed (Height, a))
    deriving Generic

instance TypeablePlc a => TypeablePlc (OracleValue a)
instance (TypeablePlc a, LiftPlc a) => LiftPlc (OracleValue a)

newtype Signed a = Signed (PubKey, a)
    deriving Generic

instance TypeablePlc a => TypeablePlc (Signed a)
instance (TypeablePlc a, LiftPlc a) => LiftPlc (Signed a)

-- | Ada value
--
-- TODO: Use [[Wallet.UTXO.Types.Value]] when Integer is supported
type Value = Int

type Hash = BSL.ByteString

-- | PLC-compatible hash of a hashable value
plcHash :: BA.ByteArrayAccess a => a -> Hash
plcHash = plcDigest . hash

-- | Convert a `Digest SHA256` to a PLC `Hash`
plcDigest :: Digest SHA256 -> Hash
plcDigest = serialise

-- | Blockchain height
--   TODO: Use [[Wallet.UTXO.Height]] when Integer is supported
type Height = Int
