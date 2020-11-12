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
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Tx(
    -- * Transactions
    Tx(..),
    inputs,
    outputs,
    txOutRefs,
    unspentOutputsTx,
    spentOutputs,
    updateUtxo,
    validValuesTx,
    forgeScripts,
    signatures,
    datumWitnesses,
    lookupSignature,
    lookupDatum,
    addSignature,
    forge,
    -- ** Hashing transactions
    txId,
    -- ** Stripped transactions
    TxStripped(..),
    strip,
    -- * Transaction outputs
    TxOutType(..),
    TxOut(..),
    TxOutTx(..),
    TxOutRef(..),
    isPubKeyOut,
    isPayToScriptOut,
    outAddress,
    outValue,
    outType,
    txOutPubKey,
    txOutDatum,
    pubKeyTxOut,
    pubKeyHashTxOut,
    scriptTxOut,
    scriptTxOut',
    txOutTxDatum,
    -- * Transaction inputs
    TxInType(..),
    TxIn(..),
    inRef,
    inType,
    inScripts,
    validRange,
    pubKeyTxIn,
    scriptTxIn,
    -- * Addresses
    Address
    ) where

import qualified Codec.CBOR.Write          as Write
import           Codec.Serialise.Class     (Serialise, encode)
import           Control.Lens
import           Crypto.Hash               (Digest, SHA256, hash)
import           Data.Aeson                (FromJSON, FromJSONKey (..), ToJSON, ToJSONKey (..))
import qualified Data.ByteArray            as BA
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe                (isJust)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc
import           Data.Typeable
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)

import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Bool    as PlutusTx
import qualified Language.PlutusTx.Eq      as PlutusTx
import           Language.PlutusTx.Lattice

import           Ledger.Address
import           Ledger.Crypto
import           Ledger.Orphans            ()
import           Ledger.Scripts
import           Ledger.Slot
import           Ledger.TxId
import           Ledger.Value
import qualified Ledger.Value              as V

{- Note [Serialisation and hashing]

We use cryptonite for generating hashes, which requires us to serialise values
to a strict ByteString (to implement `Data.ByteArray.ByteArrayAccess`).

Binary serialisation could be achieved via

1. The `binary` package
2. The `cbor` package

(1) is used in the cardano-sl repository, and (2) is used in the
`plutus-core` project in this repository.

In this module we use (2) because of the precedent. This means however that we
may generate different hashes for the same transactions compared to cardano-sl.
This might become a problem if/when we want to support "imports" of some real
blockchain state into the emulator.

However, it should be easy to change the serialisation mechanism later on,
especially because we only need one direction (to binary).

-}

-- | A transaction, including witnesses for its inputs.
data Tx = Tx {
    txInputs       :: Set.Set TxIn,
    -- ^ The inputs to this transaction.
    txOutputs      :: [TxOut],
    -- ^ The outputs of this transaction, ordered so they can be referenced by index.
    txForge        :: !Value,
    -- ^ The 'Value' forged by this transaction.
    txFee          :: !Value,
    -- ^ The fee for this transaction.
    txValidRange   :: !SlotRange,
    -- ^ The 'SlotRange' during which this transaction may be validated.
    txForgeScripts :: Set.Set MonetaryPolicy,
    -- ^ The scripts that must be run to check forging conditions.
    txSignatures   :: Map PubKey Signature,
    -- ^ Signatures of this transaction.
    txData         :: Map DatumHash Datum
    -- ^ Datum objects recorded on this transaction.
    } deriving stock (Show, Eq, Generic, Typeable)
      deriving anyclass (ToJSON, FromJSON, Serialise, IotsType)

instance Pretty Tx where
    pretty t@Tx{txInputs, txOutputs, txForge, txFee, txValidRange, txSignatures, txForgeScripts, txData} =
        let lines' =
                [ hang 2 (vsep ("inputs:" : fmap pretty (Set.toList txInputs)))
                , hang 2 (vsep ("outputs:" : fmap pretty txOutputs))
                , "forge:" <+> pretty txForge
                , "fee:" <+> pretty txFee
                , hang 2 (vsep ("mps:": fmap pretty (Set.toList txForgeScripts)))
                , hang 2 (vsep ("signatures:": fmap (pretty . fst) (Map.toList txSignatures)))
                , "validity range:" <+> viaShow txValidRange
                , hang 2 (vsep ("data:": fmap (pretty . snd) (Map.toList txData) ))
                ]
            txid = txId t
        in nest 2 $ vsep ["Tx" <+> pretty txid <> colon, braces (vsep lines')]

instance Semigroup Tx where
    tx1 <> tx2 = Tx {
        txInputs = txInputs tx1 <> txInputs tx2,
        txOutputs = txOutputs tx1 <> txOutputs tx2,
        txForge = txForge tx1 <> txForge tx2,
        txFee = txFee tx1 <> txFee tx2,
        txValidRange = txValidRange tx1 /\ txValidRange tx2,
        txForgeScripts = txForgeScripts tx1 <> txForgeScripts tx2,
        txSignatures = txSignatures tx1 <> txSignatures tx2,
        txData = txData tx1 <> txData tx2
        }

instance Monoid Tx where
    mempty = Tx mempty mempty mempty mempty top mempty mempty mempty

instance BA.ByteArrayAccess Tx where
    length        = BA.length . Write.toStrictByteString . encode
    withByteArray = BA.withByteArray . Write.toStrictByteString . encode

-- | The inputs of a transaction.
inputs :: Lens' Tx (Set.Set TxIn)
inputs = lens g s where
    g = txInputs
    s tx i = tx { txInputs = i }

-- | The outputs of a transaction.
outputs :: Lens' Tx [TxOut]
outputs = lens g s where
    g = txOutputs
    s tx o = tx { txOutputs = o }

-- | The validity range of a transaction.
validRange :: Lens' Tx SlotRange
validRange = lens g s where
    g = txValidRange
    s tx o = tx { txValidRange = o }

signatures :: Lens' Tx (Map PubKey Signature)
signatures = lens g s where
    g = txSignatures
    s tx sig = tx { txSignatures = sig }

forge :: Lens' Tx Value
forge = lens g s where
    g = txForge
    s tx v = tx { txForge = v }

forgeScripts :: Lens' Tx (Set.Set MonetaryPolicy)
forgeScripts = lens g s where
    g = txForgeScripts
    s tx fs = tx { txForgeScripts = fs }

datumWitnesses :: Lens' Tx (Map DatumHash Datum)
datumWitnesses = lens g s where
    g = txData
    s tx dat = tx { txData = dat }

lookupSignature :: PubKey -> Tx -> Maybe Signature
lookupSignature s Tx{txSignatures} = Map.lookup s txSignatures

lookupDatum :: Tx -> DatumHash -> Maybe Datum
lookupDatum Tx{txData} h = Map.lookup h txData

-- | Check that all values in a transaction are non-negative.
validValuesTx :: Tx -> Bool
validValuesTx Tx{..}
  = all (nonNegative . txOutValue) txOutputs  && nonNegative txFee
    where
      nonNegative i = V.geq i mempty

-- | A transaction without witnesses for its inputs.
data TxStripped = TxStripped {
    txStrippedInputs  :: Set.Set TxOutRef,
    -- ^ The inputs to this transaction, as transaction output references only.
    txStrippedOutputs :: [TxOut],
    -- ^ The outputs of this transation.
    txStrippedForge   :: !Value,
    -- ^ The 'Value' forged by this transaction.
    txStrippedFee     :: !Value
    -- ^ The fee for this transaction.
    } deriving (Show, Eq, Generic, Serialise)

strip :: Tx -> TxStripped
strip Tx{..} = TxStripped i txOutputs txForge txFee where
    i = Set.map txInRef txInputs

-- | Compute the id of a transaction.
txId :: Tx -> TxId
-- Double hash of a transaction, excluding its witnesses.
txId tx = TxId $ BA.convert h' where
    h :: Digest SHA256
    h = hash $ Write.toStrictByteString $ encode $ strip tx
    h' :: Digest SHA256
    h' = hash h

-- | A reference to a transaction output. This is a
-- pair of a transaction reference, and an index indicating which of the outputs
-- of that transaction we are referring to.
data TxOutRef = TxOutRef {
    txOutRefId  :: TxId,
    txOutRefIdx :: Integer -- ^ Index into the referenced transaction's outputs
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, IotsType, ToJSON, FromJSON, ToJSONKey, FromJSONKey)

instance Pretty TxOutRef where
    pretty TxOutRef{txOutRefId, txOutRefIdx} = pretty txOutRefId <> "!" <> pretty txOutRefIdx

instance PlutusTx.Eq TxOutRef where
    {-# INLINABLE (==) #-}
    l == r =
        txOutRefId l PlutusTx.== txOutRefId r
        PlutusTx.&& txOutRefIdx l PlutusTx.== txOutRefIdx r

-- | A list of a transaction's outputs paired with a 'TxOutRef's referring to them.
txOutRefs :: Tx -> [(TxOut, TxOutRef)]
txOutRefs t = mkOut <$> zip [0..] (txOutputs t) where
    mkOut (i, o) = (o, TxOutRef (txId t) i)

-- | The type of a transaction input.
data TxInType =
      -- TODO: these should all be hashes, with the validators and data segregated to the side
      ConsumeScriptAddress !Validator !Redeemer !Datum -- ^ A transaction input that consumes a script address with the given validator, redeemer, and datum.
    | ConsumePublicKeyAddress -- ^ A transaction input that consumes a public key address.
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, IotsType)

-- | A transaction input, consisting of a transaction output reference and an input type.
data TxIn = TxIn {
    txInRef  :: !TxOutRef,
    txInType :: !TxInType
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, IotsType, ToJSON, FromJSON)

instance Pretty TxIn where
    pretty TxIn{txInRef,txInType} =
                let rest =
                        case txInType of
                            ConsumeScriptAddress _ redeemer _ ->
                                pretty redeemer
                            ConsumePublicKeyAddress -> mempty
                in hang 2 $ vsep ["-" <+> pretty txInRef, rest]

-- | The 'TxOutRef' spent by a transaction input.
inRef :: Lens' TxIn TxOutRef
inRef = lens txInRef s where
    s txi r = txi { txInRef = r }

-- | The type of a transaction input.
inType :: Lens' TxIn TxInType
inType = lens txInType s where
    s txi t = txi { txInType = t }

-- | Validator, redeemer, and data scripts of a transaction input that spends a
--   "pay to script" output.
inScripts :: TxIn -> Maybe (Validator, Redeemer, Datum)
inScripts TxIn{ txInType = t } = case t of
    ConsumeScriptAddress v r d -> Just (v, r, d)
    ConsumePublicKeyAddress    -> Nothing

-- | A transaction input that spends a "pay to public key" output, given the witness.
pubKeyTxIn :: TxOutRef -> TxIn
pubKeyTxIn r = TxIn r ConsumePublicKeyAddress

-- | A transaction input that spends a "pay to script" output, given witnesses.
scriptTxIn :: TxOutRef -> Validator -> Redeemer -> Datum -> TxIn
scriptTxIn ref v r d = TxIn ref $ ConsumeScriptAddress v r d

-- | The type of a transaction output.
data TxOutType =
    PayToScript !DatumHash -- ^ A pay-to-script output with the given datum hash.
    | PayToPubKey -- ^ A pay-to-pubkey output.
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, ToJSONKey, IotsType)

instance PlutusTx.Eq TxOutType where
    PayToScript l == PayToScript r = l PlutusTx.== r
    PayToPubKey == PayToPubKey     = True
    _ == _                         = False

instance Pretty TxOutType where
    pretty = \case
        PayToScript ds -> "PayToScript:" <+> pretty ds
        PayToPubKey    -> "PayToPubKey"

-- | A transaction output, consisting of a target address, a value, and an output type.
data TxOut = TxOut {
    txOutAddress :: !Address,
    txOutValue   :: !Value,
    txOutType    :: !TxOutType
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, IotsType)

instance Pretty TxOut where
    pretty TxOut{txOutAddress, txOutValue} =
                hang 2 $ vsep ["-" <+> pretty txOutValue <+> "addressed to", pretty txOutAddress]

instance PlutusTx.Eq TxOut where
    l == r =
        txOutAddress l PlutusTx.== txOutAddress r
        PlutusTx.&& txOutValue l PlutusTx.== txOutValue r
        PlutusTx.&& txOutType l PlutusTx.== txOutType r

-- | The datum attached to a 'TxOutOf', if there is one.
txOutDatum :: TxOut -> Maybe DatumHash
txOutDatum TxOut{txOutType = t} = case  t of
    PayToScript s -> Just s
    PayToPubKey   -> Nothing

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey TxOut{txOutAddress = a} = case a of
    PubKeyAddress pkh -> Just pkh
    _                 -> Nothing

-- | The address of a transaction output.
outAddress :: Lens' TxOut Address
outAddress = lens txOutAddress s where
    s tx a = tx { txOutAddress = a }

-- | The value of a transaction output.
-- | TODO: Compute address again
outValue :: Lens' TxOut Value
outValue = lens txOutValue s where
    s tx v = tx { txOutValue = v }

-- | The output type of a transaction output.
-- | TODO: Compute address again
outType :: Lens' TxOut TxOutType
outType = lens txOutType s where
    s tx d = tx { txOutType = d }

-- | Whether the output is a pay-to-pubkey output.
isPubKeyOut :: TxOut -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Whether the output is a pay-to-script output.
isPayToScriptOut :: TxOut -> Bool
isPayToScriptOut = isJust . txOutDatum

-- | A 'TxOut' along with the 'Tx' it comes from, which may have additional information e.g.
-- the full data script that goes with the 'TxOut'.
data TxOutTx = TxOutTx { txOutTxTx :: Tx, txOutTxOut :: TxOut }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, IotsType)

txOutTxDatum :: TxOutTx -> Maybe Datum
txOutTxDatum (TxOutTx tx out) = txOutDatum out >>= lookupDatum tx

-- | Create a transaction output locked by a validator script hash
--   with the given data script attached.
scriptTxOut' :: Value -> Address -> Datum -> TxOut
scriptTxOut' v a ds = TxOut a v tp where
    tp = PayToScript (datumHash ds)

-- | Create a transaction output locked by a validator script and with the given data script attached.
scriptTxOut :: Value -> Validator -> Datum -> TxOut
scriptTxOut v vs = scriptTxOut' v (scriptAddress vs)

-- | Create a transaction output locked by a public key.
pubKeyTxOut :: Value -> PubKey -> TxOut
pubKeyTxOut v pk = TxOut (pubKeyAddress pk) v PayToPubKey

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (PubKeyAddress pkh) v PayToPubKey

-- | The unspent outputs of a transaction.
unspentOutputsTx :: Tx -> Map TxOutRef TxOut
unspentOutputsTx t = Map.fromList $ fmap f $ zip [0..] $ txOutputs t where
    f (idx, o) = (TxOutRef (txId t) idx, o)

-- | The transaction output references consumed by a transaction.
spentOutputs :: Tx -> Set.Set TxOutRef
spentOutputs = Set.map txInRef . txInputs

-- | Update a map of unspent transaction outputs and signatures based on the inputs
--   and outputs of a transaction.
updateUtxo :: Tx -> Map TxOutRef TxOut -> Map TxOutRef TxOut
updateUtxo t unspent = (unspent `Map.difference` lift' (spentOutputs t)) `Map.union` outs where
    lift' = Map.fromSet (const ())
    outs = unspentOutputsTx t

-- | Sign the transaction with a 'PrivateKey' and add the signature to the
--   transaction's list of signatures.
addSignature :: PrivateKey -> Tx -> Tx
addSignature privK tx = tx & signatures . at pubK ?~ sig where
    sig = signTx (txId tx) privK
    pubK = toPublicKey privK

PlutusTx.makeIsData ''TxOut
PlutusTx.makeLift ''TxOut

PlutusTx.makeIsDataIndexed ''TxOutType [('PayToScript, 0), ('PayToPubKey , 1)]
PlutusTx.makeLift ''TxOutType

PlutusTx.makeIsData ''TxOutRef
PlutusTx.makeLift ''TxOutRef
