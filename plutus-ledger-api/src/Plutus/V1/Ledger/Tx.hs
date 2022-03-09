{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plutus.V1.Ledger.Tx(
    -- * Transactions
    TxId (..),
    ScriptTag (..),
    RedeemerPtr (..),
    Redeemers,
    -- * Transaction outputs
    TxOut(..),
    TxOutRef(..),
    isPubKeyOut,
    isPayToScriptOut,
    outAddress,
    outValue,
    txOutPubKey,
    txOutDatum,
    pubKeyHashTxOut,
    -- * Transaction inputs
    TxInType(..),
    TxIn(..),
    inRef,
    inType,
    inScripts,
    pubKeyTxIn,
    scriptTxIn,
    pubKeyTxIns,
    scriptTxIns,
    ) where

import Control.DeepSeq (NFData)
import Control.Lens
import Data.Map (Map)
import Data.Maybe (isJust)
import Data.Set qualified as Set
import Data.String (IsString)
import GHC.Generics (Generic)
import Prettyprinter

import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.Ord qualified as PlutusTx

import Plutus.V1.Ledger.Address
import Plutus.V1.Ledger.Bytes
import Plutus.V1.Ledger.Crypto
import Plutus.V1.Ledger.Scripts
import Plutus.V1.Ledger.Value

-- | A transaction ID, using a SHA256 hash as the transaction id.
newtype TxId = TxId { getTxId :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord)
    deriving (Show, Pretty, IsString) via LedgerBytes

-- | A tag indicating the type of script that we are pointing to.
data ScriptTag = Spend | Mint | Cert | Reward
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | A redeemer pointer is a pair of a script type tag t and an index i, picking out the ith
-- script of type t in the transaction.
data RedeemerPtr = RedeemerPtr ScriptTag Integer
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

type Redeemers = Map RedeemerPtr Redeemer

-- | A reference to a transaction output. This is a
-- pair of a transaction reference, and an index indicating which of the outputs
-- of that transaction we are referring to.
data TxOutRef = TxOutRef {
    txOutRefId  :: TxId,
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

-- | The type of a transaction input.
data TxInType =
      -- TODO: these should all be hashes, with the validators and data segregated to the side
      ConsumeScriptAddress !Validator !Redeemer !Datum -- ^ A transaction input that consumes a script address with the given validator, redeemer, and datum.
    | ConsumePublicKeyAddress -- ^ A transaction input that consumes a public key address.
    | ConsumeSimpleScriptAddress -- ^ Consume a simple script
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | A transaction input, consisting of a transaction output reference and an input type.
data TxIn = TxIn {
    txInRef  :: !TxOutRef,
    txInType :: Maybe TxInType
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

instance Pretty TxIn where
    pretty TxIn{txInRef,txInType} =
                let rest =
                        case txInType of
                            Just (ConsumeScriptAddress _ redeemer _) ->
                                pretty redeemer
                            _ -> mempty
                in hang 2 $ vsep ["-" <+> pretty txInRef, rest]

-- | The 'TxOutRef' spent by a transaction input.
inRef :: Lens' TxIn TxOutRef
inRef = lens txInRef s where
    s txi r = txi { txInRef = r }

-- | The type of a transaction input.
inType :: Lens' TxIn (Maybe TxInType)
inType = lens txInType s where
    s txi t = txi { txInType = t }

-- | Validator, redeemer, and data scripts of a transaction input that spends a
--   "pay to script" output.
inScripts :: TxIn -> Maybe (Validator, Redeemer, Datum)
inScripts TxIn{ txInType = t } = case t of
    Just (ConsumeScriptAddress v r d) -> Just (v, r, d)
    _                                 -> Nothing

-- | A transaction input that spends a "pay to public key" output, given the witness.
pubKeyTxIn :: TxOutRef -> TxIn
pubKeyTxIn r = TxIn r (Just ConsumePublicKeyAddress)

-- | A transaction input that spends a "pay to script" output, given witnesses.
scriptTxIn :: TxOutRef -> Validator -> Redeemer -> Datum -> TxIn
scriptTxIn ref v r d = TxIn ref . Just $ ConsumeScriptAddress v r d

-- | Filter to get only the pubkey inputs.
pubKeyTxIns :: Fold (Set.Set TxIn) TxIn
pubKeyTxIns = folding (Set.filter (\TxIn{ txInType = t } -> t == Just ConsumePublicKeyAddress))

-- | Filter to get only the script inputs.
scriptTxIns :: Fold (Set.Set TxIn) TxIn
scriptTxIns = (\x -> folding x) . Set.filter $ \case
    TxIn{ txInType = Just ConsumeScriptAddress{} } -> True
    _                                              -> False

-- | A transaction output, consisting of a target address, a value, and optionally a datum hash.
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
txOutValidatorHash :: TxOut -> Maybe ValidatorHash
txOutValidatorHash TxOut{txOutAddress} = toValidatorHash txOutAddress

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
isPayToScriptOut = isJust . txOutValidatorHash

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v Nothing

PlutusTx.makeLift ''TxId
PlutusTx.makeIsDataIndexed ''TxId [('TxId,0)]

PlutusTx.makeIsDataIndexed ''TxOut [('TxOut,0)]
PlutusTx.makeLift ''TxOut

PlutusTx.makeIsDataIndexed ''TxOutRef [('TxOutRef,0)]
PlutusTx.makeLift ''TxOutRef
