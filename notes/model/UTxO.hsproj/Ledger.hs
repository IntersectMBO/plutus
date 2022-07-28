{-# LANGUAGE PackageImports  #-}
{-# LANGUAGE RecordWildCards #-}

module Ledger (

  -- ** Ledger & transaction types
  Ledger, Tx(..), TxIn(..), TxOut(..), TxOutRef(..), txIn,

  -- ** Ledger & transaction state for scripts
  hashTx, preHashTx, validValuesTx, state
) where

import "cryptonite" Crypto.Hash
import Data.ByteArray qualified as BA
import Data.ByteString.Char8 qualified as BS
import Data.Set (Set)
import Data.Set qualified as Set

import Types
import Witness


-- Ledger and transaction types
-- ----------------------------

-- |An UTxO ledger
--
type Ledger = [Tx]        -- last transaction first

-- |A single transaction
--
data Tx
  = Tx
    { inputsTX  :: [TxIn]
    , outputsTX :: [TxOut]
    , mintTX    :: Value
    , feeTX     :: Value
    }
    deriving stock (Show)

data TxStripped
  = TxStripped
    { inputsTXS  :: Set TxOutRef
    , outputsTXS :: [TxOut]
    , mintTXS    :: Value
    , feeTXS     :: Value
    }
    deriving stock (Show)

stripTx :: Tx -> TxStripped
stripTx Tx{..}
  = TxStripped{..}
  where
    inputsTXS   = Set.fromList . map refTI $ inputsTX
    outputsTXS  = outputsTX
    mintTXS    = mintTX
    feeTXS      = feeTX

-- |Hash (double) the given transaction *without* witnesses.
--
hashTx :: Tx -> Digest SHA256
hashTx = hash . preHashTx

-- |Hash (once) the given transaction *without* witnesses.
--
preHashTx :: Tx -> Digest SHA256
preHashTx tx = hash (stripTx tx)

-- |Check that all values in a transaction are no.
--
validValuesTx :: Tx -> Bool
validValuesTx Tx{..}
  = all ((>= 0) . valueTO) outputsTX && mintTX >= 0 && feeTX >= 0

data TxOutRef
  = TxOutRef
    { idTOR    :: TxId
    , indexTOR :: Int
    }
    deriving stock (Show, Eq, Ord)

-- |A single transaction input
--
data TxIn
  = TxIn
    { refTI     :: TxOutRef
    , witnessTI :: Witness
    }
    deriving stock (Show)

-- |Convenience constructor for inputs.
--
txIn :: TxId -> Int -> Witness -> TxIn
txIn txId idx wit = TxIn (TxOutRef txId idx) wit

---- Equality of transaction inputs is only predicated on the output that the input
---- refers to, *not* on the witness. This is crucial so that two 'TxIn values
---- spending the same input are considered the same.
----
--instance Eq TxIn where
--  txIn1 == txIn2 = idTI txIn1 == idTI txIn2 && indexTI txIn1 == indexTI txIn2
--
---- As for equality
----
--instance Ord TxIn where
--  txIn1 <= txIn2
--    = idTI txIn1 < idTI txIn2 || (idTI txIn1 == idTI txIn2 && indexTI txIn1 < indexTI txIn2)

-- |A single transaction output, paying a value to a script address
--
data TxOut
  = TxOut
    { addressTO :: Address
    , valueTO   :: Value
    }
    deriving stock (Eq, Show)

instance BA.ByteArrayAccess Tx where
  length        = BA.length . BS.pack . show            -- FIXME: we should serialise properly
  withByteArray = BA.withByteArray . BS.pack  . show    -- FIXME: we should serialise properly

instance BA.ByteArrayAccess TxStripped where
  length        = BA.length . BS.pack . show            -- FIXME: we should serialise properly
  withByteArray = BA.withByteArray . BS.pack  . show    -- FIXME: we should serialise properly

instance BA.ByteArrayAccess TxIn where
  length        = BA.length . BS.pack . show            -- FIXME: we should serialise properly
  withByteArray = BA.withByteArray . BS.pack  . show    -- FIXME: we should serialise properly

instance BA.ByteArrayAccess TxOut where
  length        = BA.length . BS.pack . show            -- FIXME: we should serialise properly
  withByteArray = BA.withByteArray . BS.pack  . show    -- FIXME: we should serialise properly


-- Ledger & transaction state for scripts
-- --------------------------------------

-- |Given a transaction and a ledger that the transaction is to be validated against, extract
-- the state information needed by validation scripts.
--
state :: Tx -> Ledger -> State
state tx ledger = State (length ledger) (hashTx tx) (preHashTx tx)

