-- | A model of the types involved in transactions. These types are intented to
--   be used in PLC scripts.
module Language.Plutus.Runtime.Types (-- * Transactions and related types
                PubKey(..)
              , Value
              , Height
              , PendingTxOutRef(..)
              , TxId
              , Hash
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

import           Wallet.API  (PubKey (..))
import           Wallet.UTXO (Signature (..), TxId)

data PendingTxOutType =
    PubKeyTxOut PubKey -- ^ Pub key address
    | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])

-- | Output of a pending transaction.
data PendingTxOut d = PendingTxOut {
    pendingTxOutValue   :: Value,
    pendingTxDataScript :: Maybe d, -- ^ Note: It would be better if the `DataTxOut` constructor of `PendingTxOutType` contained the `d` value (because the data script is always `Nothing` for a pub key output). However, this causes the core-to-plc converter to fail with a type error on a pattern match on `PubKeyTxOut`.
    pendingTxOutData    :: PendingTxOutType
    }

data PendingTxOutRef = PendingTxOutRef {
    pendingTxOutRefId  :: Hash,
    pendingTxOutRefIdx :: Int,
    pendingTxOutSigs   :: [Signature]
    }

-- | Input of a pending transaction.
data PendingTxIn r = PendingTxIn {
    pendingTxInRef         :: PendingTxOutRef,
    pendingTxInRefRedeemer :: r -- ^ The redeemer of the pending transaction input (see note [Script types in pending transactions])
    }

-- | A pending transaction as seen by validator scripts.
data PendingTx r d = PendingTx {
    pendingTxCurrentInput :: (PendingTxIn r, Value), -- ^ The input we are validating
    pendingTxOtherInputs  :: [(PendingTxIn r, Value)], -- ^ Other transaction inputs (they will be validated separately but we can look at their redeemer data and coin value)
    pendingTxOutputs      :: [PendingTxOut d],
    pendingTxForge        :: Value,
    pendingTxFee          :: Value,
    pendingTxBlockHeight  :: Height,
    pendingTxSignatures   :: [Signature]
    }

-- `OracleValue a` is the value observed at a time signed by
-- an oracle.
newtype OracleValue a = OracleValue (Signed (Height, a))

newtype Signed a = Signed (PubKey, a)

-- | Ada value
--
-- TODO: Use [[Wallet.UTXO.Types.Value]] when Integer is supported
type Value = Int

type Hash = Int

-- | Blockchain height
--   TODO: Use [[Wallet.UTXO.Height]] when Integer is supported
type Height = Int
