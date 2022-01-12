{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plutus.V1.Ledger.Tx(
    -- * Transactions
    Tx(..),
    inputs,
    collateralInputs,
    outputs,
    spentOutputs,
    updateUtxoCollateral,
    validValuesTx,
    mintScripts,
    signatures,
    datumWitnesses,
    redeemers,
    lookupSignature,
    lookupDatum,
    lookupRedeemer,
    mint,
    fee,
    ScriptTag (..),
    RedeemerPtr (..),
    Redeemers,
    -- ** Stripped transactions
    TxStripped(..),
    strip,
    -- * Transaction outputs
    TxOut(..),
    TxOutTx(..),
    TxOutRef(..),
    isPubKeyOut,
    isPayToScriptOut,
    outAddress,
    outValue,
    txOutPubKey,
    txOutDatum,
    pubKeyHashTxOut,
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
    pubKeyTxIns,
    scriptTxIns,
    -- * Addresses
    Address
    ) where

import Codec.CBOR.Write qualified as Write
import Codec.Serialise.Class (Serialise, encode)
import Control.DeepSeq (NFData)
import Control.Lens
import Data.Aeson (FromJSON, FromJSONKey (..), ToJSON, ToJSONKey (..))
import Data.ByteArray qualified as BA
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (isJust)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Prettyprinter

import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.Lattice

import Plutus.V1.Ledger.Address
import Plutus.V1.Ledger.Crypto
import Plutus.V1.Ledger.Orphans ()
import Plutus.V1.Ledger.Scripts
import Plutus.V1.Ledger.Slot
import Plutus.V1.Ledger.TxId
import Plutus.V1.Ledger.Value
import Plutus.V1.Ledger.Value qualified as V

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
    txInputs      :: Set.Set TxIn,
    -- ^ The inputs to this transaction.
    txCollateral  :: Set.Set TxIn,
    -- ^ The collateral inputs to cover the fees in case validation of the transaction fails.
    txOutputs     :: [TxOut],
    -- ^ The outputs of this transaction, ordered so they can be referenced by index.
    txMint        :: !Value,
    -- ^ The 'Value' minted by this transaction.
    txFee         :: !Value,
    -- ^ The fee for this transaction.
    txValidRange  :: !SlotRange,
    -- ^ The 'SlotRange' during which this transaction may be validated.
    txMintScripts :: Set.Set MintingPolicy,
    -- ^ The scripts that must be run to check minting conditions.
    txSignatures  :: Map PubKey Signature,
    -- ^ Signatures of this transaction.
    txRedeemers   :: Redeemers,
    -- ^ Redeemers of the minting scripts.
    txData        :: Map DatumHash Datum
    -- ^ Datum objects recorded on this transaction.
    } deriving stock (Show, Eq, Generic)
      deriving anyclass (ToJSON, FromJSON, Serialise, NFData)

instance Semigroup Tx where
    tx1 <> tx2 = Tx {
        txInputs = txInputs tx1 <> txInputs tx2,
        txCollateral = txCollateral tx1 <> txCollateral tx2,
        txOutputs = txOutputs tx1 <> txOutputs tx2,
        txMint = txMint tx1 <> txMint tx2,
        txFee = txFee tx1 <> txFee tx2,
        txValidRange = txValidRange tx1 /\ txValidRange tx2,
        txMintScripts = txMintScripts tx1 <> txMintScripts tx2,
        txSignatures = txSignatures tx1 <> txSignatures tx2,
        txRedeemers = txRedeemers tx1 <> txRedeemers tx2,
        txData = txData tx1 <> txData tx2
        }

instance Monoid Tx where
    mempty = Tx mempty mempty mempty mempty mempty top mempty mempty mempty mempty

instance BA.ByteArrayAccess Tx where
    length        = BA.length . Write.toStrictByteString . encode
    withByteArray = BA.withByteArray . Write.toStrictByteString . encode

-- | The inputs of a transaction.
inputs :: Lens' Tx (Set.Set TxIn)
inputs = lens g s where
    g = txInputs
    s tx i = tx { txInputs = i }

-- | The collateral inputs of a transaction for paying fees when validating the transaction fails.
collateralInputs :: Lens' Tx (Set.Set TxIn)
collateralInputs = lens g s where
    g = txCollateral
    s tx i = tx { txCollateral = i }

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

fee :: Lens' Tx Value
fee = lens g s where
    g = txFee
    s tx v = tx { txFee = v }

mint :: Lens' Tx Value
mint = lens g s where
    g = txMint
    s tx v = tx { txMint = v }

mintScripts :: Lens' Tx (Set.Set MintingPolicy)
mintScripts = lens g s where
    g = txMintScripts
    s tx fs = tx { txMintScripts = fs }

redeemers :: Lens' Tx Redeemers
redeemers = lens g s where
    g = txRedeemers
    s tx reds = tx { txRedeemers = reds }

datumWitnesses :: Lens' Tx (Map DatumHash Datum)
datumWitnesses = lens g s where
    g = txData
    s tx dat = tx { txData = dat }

lookupSignature :: PubKey -> Tx -> Maybe Signature
lookupSignature s Tx{txSignatures} = Map.lookup s txSignatures

lookupDatum :: Tx -> DatumHash -> Maybe Datum
lookupDatum Tx{txData} h = Map.lookup h txData

lookupRedeemer :: Tx -> RedeemerPtr -> Maybe Redeemer
lookupRedeemer tx p = Map.lookup p (txRedeemers tx)

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
    txStrippedMint    :: !Value,
    -- ^ The 'Value' minted by this transaction.
    txStrippedFee     :: !Value
    -- ^ The fee for this transaction.
    } deriving (Show, Eq, Generic, Serialise)

strip :: Tx -> TxStripped
strip Tx{..} = TxStripped i txOutputs txMint txFee where
    i = Set.map txInRef txInputs

-- | A tag indicating the type of script that we are pointing to.
-- NOTE: Cert/Reward are not supported right now.
data ScriptTag = Spend | Mint | Cert | Reward
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, NFData)

-- | A redeemer pointer is a pair of a script type tag t and an index i, picking out the ith
-- script of type t in the transaction.
data RedeemerPtr = RedeemerPtr ScriptTag Integer
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, ToJSONKey, FromJSONKey, NFData)

type Redeemers = Map RedeemerPtr Redeemer

-- | A reference to a transaction output. This is a
-- pair of a transaction reference, and an index indicating which of the outputs
-- of that transaction we are referring to.
data TxOutRef = TxOutRef {
    txOutRefId  :: TxId,
    txOutRefIdx :: Integer -- ^ Index into the referenced transaction's outputs
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, ToJSONKey, FromJSONKey, NFData)

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
    deriving anyclass (Serialise, ToJSON, FromJSON, NFData)

-- | A transaction input, consisting of a transaction output reference and an input type.
data TxIn = TxIn {
    txInRef  :: !TxOutRef,
    txInType :: Maybe TxInType
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON, NFData)

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
    deriving anyclass (Serialise, ToJSON, FromJSON, NFData)

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
isPayToScriptOut = isJust . txOutDatum

-- | A 'TxOut' along with the 'Tx' it comes from, which may have additional information e.g.
-- the full data script that goes with the 'TxOut'.
data TxOutTx = TxOutTx { txOutTxTx :: Tx, txOutTxOut :: TxOut }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (Serialise, ToJSON, FromJSON)

txOutTxDatum :: TxOutTx -> Maybe Datum
txOutTxDatum (TxOutTx tx out) = txOutDatum out >>= lookupDatum tx

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v Nothing

-- | The transaction output references consumed by a transaction.
spentOutputs :: Tx -> Set.Set TxOutRef
spentOutputs = Set.map txInRef . txInputs

-- | Update a map of unspent transaction outputs and signatures
--   for a failed transaction using its collateral inputs.
updateUtxoCollateral :: Tx -> Map TxOutRef TxOut -> Map TxOutRef TxOut
updateUtxoCollateral tx unspent = unspent `Map.withoutKeys` (Set.map txInRef . txCollateral $ tx)

PlutusTx.makeIsDataIndexed ''TxOut [('TxOut,0)]
PlutusTx.makeLift ''TxOut

PlutusTx.makeIsDataIndexed ''TxOutRef [('TxOutRef,0)]
PlutusTx.makeLift ''TxOutRef
