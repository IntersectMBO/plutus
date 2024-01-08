-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusLedgerApi.V1.Tx
    (
    -- * Transactions
      TxId (..)
    , ScriptTag (..)
    , RedeemerPtr (..)
    , Redeemers
    -- * Transaction outputs
    , TxOut(..)
    , TxOutRef(..)
    , isPubKeyOut
    , isPayToScriptOut
    , outAddress
    , outValue
    , txOutPubKey
    ,txOutDatum
    ,pubKeyHashTxOut
    ) where

import Control.DeepSeq (NFData)
import Control.Lens
import Data.Map (Map)
import Data.Maybe (isJust)
import Data.String (IsString)
import GHC.Generics (Generic)
import Prettyprinter

import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.Ord qualified as PlutusTx

import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Bytes
import PlutusLedgerApi.V1.Crypto
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V1.Value
{- | A transaction ID, i.e. the hash of a transaction. Hashed with BLAKE2b-256. 32 byte.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://github.com/input-output-hk/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf).
-}
newtype TxId = TxId { getTxId :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord)
    deriving
        (IsString        -- ^ from hex encoding
        , Show           -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes

-- | A tag indicating the type of script that we are pointing to.
--
-- See also 'PlutusLedgerApi.V1.ScriptPurpose'
data ScriptTag = Spend | Mint | Cert | Reward
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | A redeemer pointer is a pair of a script type tag ('ScriptTag') `t` and an index `i`,
-- picking out the i-th script of type `t` in the transaction.
data RedeemerPtr = RedeemerPtr ScriptTag Integer
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Redeemers is a `Map` of redeemer pointer ('RedeemerPtr') and its 'Redeemer'.
type Redeemers = Map RedeemerPtr Redeemer

-- | A reference to a transaction output. This is a
-- pair of a transaction ID (`TxId`), and an index indicating which of the outputs
-- of that transaction we are referring to.
data TxOutRef = TxOutRef {
    txOutRefId  :: TxId, -- ^ The transaction ID.
    txOutRefIdx :: Integer -- ^ Index into the referenced transaction's outputs
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

instance Pretty TxOutRef where
    pretty TxOutRef{txOutRefId, txOutRefIdx} = pretty txOutRefId <> "!" <> pretty txOutRefIdx

instance PlutusTx.Eq TxOutRef where
    {-# INLINABLE (==) #-}
    l == r =
        txOutRefId l PlutusTx.== txOutRefId r
        PlutusTx.&& txOutRefIdx l PlutusTx.== txOutRefIdx r

-- | A transaction output, consisting of a target address ('Address'), a value ('Value'),
-- and optionally a datum hash ('DatumHash').
data TxOut = TxOut {
    txOutAddress   :: Address,
    txOutValue     :: Value,
    txOutDatumHash :: Maybe DatumHash
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Pretty TxOut where
    pretty TxOut{txOutAddress, txOutValue} =
                hang 2 $ vsep ["-" <+> pretty txOutValue <+> "addressed to", pretty txOutAddress]

instance PlutusTx.Eq TxOut where
    {-# INLINABLE (==) #-}
    l == r =
        txOutAddress l PlutusTx.== txOutAddress r
        PlutusTx.&& txOutValue l PlutusTx.== txOutValue r
        PlutusTx.&& txOutDatumHash l PlutusTx.== txOutDatumHash r

-- | The datum attached to a 'TxOut', if there is one.
txOutDatum :: TxOut -> Maybe DatumHash
txOutDatum TxOut{txOutDatumHash} = txOutDatumHash

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey TxOut{txOutAddress} = toPubKeyHash txOutAddress

-- | The validator hash attached to a 'TxOut', if there is one.
txOutScriptHash :: TxOut -> Maybe ScriptHash
txOutScriptHash TxOut{txOutAddress} = toScriptHash txOutAddress

-- | The address of a transaction output.
outAddress :: Lens' TxOut Address
outAddress = lens txOutAddress s where
    s tx a = tx { txOutAddress = a }

-- | The value of a transaction output.
-- | TODO: Compute address again
outValue :: Lens' TxOut Value
outValue = lens txOutValue s where
    s tx v = tx { txOutValue = v }

-- | Whether the output is a pay-to-pubkey output.
isPubKeyOut :: TxOut -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Whether the output is a pay-to-script output.
isPayToScriptOut :: TxOut -> Bool
isPayToScriptOut = isJust . txOutScriptHash

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v Nothing

PlutusTx.makeLift ''TxId
PlutusTx.makeIsDataIndexed ''TxId [('TxId,0)]

PlutusTx.makeIsDataIndexed ''TxOut [('TxOut,0)]
PlutusTx.makeLift ''TxOut

PlutusTx.makeIsDataIndexed ''TxOutRef [('TxOutRef,0)]
PlutusTx.makeLift ''TxOutRef
