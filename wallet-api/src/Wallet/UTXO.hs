{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Wallet.UTXO(
    -- * Basic types
    Value(..),
    Height(..),
    height,
    TxId(..),
    TxId',
    PubKey(..),
    Signature(..),
    signedBy,
    -- ** Addresses
    Address(..),
    Address',
    pubKeyAddress,
    scriptAddress,
    -- ** Scripts
    Validator(..),
    Redeemer(..),
    DataScript(..),
    -- * Transactions
    Tx(..),
    TxStripped(..),
    strip,
    preHash,
    hashTx,
    dataTxo,
    TxIn(..),
    TxInType(..),
    TxIn',
    TxOut(..),
    TxOutType(..),
    TxOut',
    TxOutRef(..),
    TxOutRef',
    simpleInput,
    simpleOutput,
    pubKeyTxIn,
    scriptTxIn,
    pubKeyTxOut,
    scriptTxOut,
    -- * Blockchain & UTxO model
    Block,
    Blockchain,
    BlockchainState(..),
    state,
    transaction,
    out,
    value,
    unspentOutputsTx,
    spentOutputs,
    unspentOutputs,
    validTx,
    txOutPubKey,
    pubKeyTxo,
    -- * Scripts
    validate,
    emptyValidator,
    unitRedeemer,
    unitData,
    -- * Lenses
    inputs,
    outputs,
    outAddress,
    outValue,
    outType,
    inRef,
    inType,
    inScripts,
    inSignature,
    -- * Encodings
    encodePubKey,
    encodeSignature,
    encodeValue,
    encodeValidator,
    encodeDataScript,
    encodeRedeemer,
    encodeHeight,
    encodeTxId,
    encodeAddress,
    encodeTx,
    encodeTxOutRef,
    encodeTxIn,
    encodeTxInType,
    encodeTxOut,
    encodeTxOutType
    ) where

import           Codec.CBOR.Encoding                      (Encoding)
import qualified Codec.CBOR.Encoding                      as Enc
import qualified Codec.CBOR.Write                         as Write
import           Control.Monad                            (join)
import           Control.Monad.Except
import           Crypto.Hash                              (Digest, SHA256, hash)
import qualified Data.ByteArray                           as BA
import qualified Data.ByteString.Char8                    as BS
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Foldable                            (foldMap)
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import           Data.Maybe                               (fromMaybe, isJust, listToMaybe)
import           Data.Monoid                              (Sum (..))
import           Data.Semigroup                           (Semigroup (..))
import qualified Data.Set                                 as Set
import           Lens.Micro

import           Language.Plutus.CoreToPLC.Plugin         (PlcCode, getAst, getSerializedCode)
import           Language.Plutus.TH                       (plutus)
import           Language.PlutusCore                      (applyProgram, typecheckPipeline)
import           Language.PlutusCore.Evaluation.CkMachine (runCk)
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Quote

{- Note [Serialisation and hashing]

We use cryptonite for generating hashes, which requires us to serialise values
to a strict ByteString (to implement `Data.ByteArray.ByteArrayAccess`).

Binary serialisation could be achieved via

1. The `binary` package
2. The `cbor` package

(1) is used in the cardano-sl repository, and (2) is used in the
`language-plutus-core` project in this repository.

In this module we use (2) because of the precedent. This means however that we
may generate different hashes for the same transactions compared to cardano-sl.
This might become a problem if/when we want to support "imports" of some real
blockchain state into the emulator.

However, it should be easy to change the serialisation mechanism later on,
especially because we only need one direction (to binary).

-}

-- | Public key
newtype PubKey = PubKey { getPubKey :: Int }
    deriving (Eq, Ord, Show)

encodePubKey :: PubKey -> Encoding
encodePubKey = Enc.encodeInt . getPubKey

newtype Signature = Signature { getSignature :: Int }
    deriving (Eq, Ord, Show)

encodeSignature :: Signature -> Encoding
encodeSignature = Enc.encodeInt . getSignature

-- | True if the signature matches the public key
signedBy :: Signature -> PubKey -> Bool
signedBy (Signature k) (PubKey s) = k == s

-- | Cryptocurrency value
--
newtype Value = Value { getValue :: Integer }
    deriving (Eq, Ord, Show, Num, Integral, Real, Enum)

encodeValue :: Value -> Encoding
encodeValue = Enc.encodeInteger . getValue

-- | Transaction ID (double SHA256 hash of the transaction)
newtype TxId h = TxId { getTxId :: h }
    deriving (Eq, Ord, Show)

type TxId' = TxId (Digest SHA256)

encodeTxId :: TxId' -> Encoding
encodeTxId = Enc.encodeBytes . BA.convert . getTxId

-- | A payment address is a double SHA256 of a
--   UTxO output's validator script (and presumably its data script).
--   This corresponds to a Bitcoing pay-to-witness-script-hash
newtype Address h = Address { getAddress :: h }
    deriving (Eq, Ord, Show)

type Address' = Address (Digest SHA256)

encodeAddress :: Address' -> Encoding
encodeAddress = Enc.encodeBytes . BA.convert . getAddress

-- | A validator is a PLC script.
newtype Validator = Validator { getValidator :: PlcCode }

instance Show Validator where
    show = const "Validator { <script> }"

instance Eq Validator where
    (Validator l) == (Validator r) = -- TODO: Deriving via
        getSerializedCode l == getSerializedCode r

instance Ord Validator where
    compare (Validator l) (Validator r) = -- TODO: Deriving via
        getSerializedCode l `compare` getSerializedCode r

instance BA.ByteArrayAccess Validator where
    length =
        BA.length . Write.toStrictByteString . encodeValidator
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encodeValidator

encPlc :: PlcCode -> Encoding
encPlc = Enc.encodeBytes . BSL.toStrict  . getSerializedCode

encodeValidator :: Validator -> Encoding
encodeValidator = encPlc . getValidator

-- | Data script (supplied by producer of the transaction output)
newtype DataScript = DataScript { getDataScript :: PlcCode  }

instance Show DataScript where
    show = const "DataScript { <script> }"

instance Eq DataScript where
    (DataScript l) == (DataScript r) = -- TODO: Deriving via
        getSerializedCode l == getSerializedCode r

instance Ord DataScript where
    compare (DataScript l) (DataScript r) = -- TODO: Deriving via
        getSerializedCode l `compare` getSerializedCode r

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encodeDataScript
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encodeDataScript

encodeDataScript :: DataScript -> Encoding
encodeDataScript = encPlc . getDataScript

-- | Redeemer (supplied by consumer of the transaction output)
newtype Redeemer = Redeemer { getRedeemer :: PlcCode }

instance Show Redeemer where
    show = const "Redeemer { <script> }"

instance Eq Redeemer where
    (Redeemer l) == (Redeemer r) = -- TODO: Deriving via
        getSerializedCode l == getSerializedCode r

instance Ord Redeemer where
    compare (Redeemer l) (Redeemer r) = -- TODO: Deriving via
        getSerializedCode l `compare` getSerializedCode r

encodeRedeemer :: Redeemer -> Encoding
encodeRedeemer = encPlc . getRedeemer

-- | Block height
newtype Height = Height { getHeight :: Integer }
    deriving (Eq, Ord, Show, Enum, Num, Real, Integral)

encodeHeight :: Height -> Encoding
encodeHeight = Enc.encodeInteger . getHeight

-- | The height of a blockchain
height :: Blockchain -> Height
height = Height . fromIntegral . length . join

-- | Transaction including witnesses for its inputs
data Tx = Tx {
    txInputs  :: Set.Set TxIn',
    txOutputs :: [TxOut'],
    txForge   :: !Value,
    txFee     :: !Value
    } deriving (Show, Eq, Ord)

-- | The inputs of a transaction
inputs :: Lens' Tx (Set.Set TxIn')
inputs = lens g s where
    g = txInputs
    s tx i = tx { txInputs = i }

outputs :: Lens' Tx [TxOut']
outputs = lens g s where
    g = txOutputs
    s tx o = tx { txOutputs = o }

encodeTx :: Tx -> Encoding
encodeTx Tx{..} =
    foldMap encodeTxIn txInputs
    <> foldMap encodeTxOut txOutputs
    <> encodeValue txForge
    <> encodeValue txFee

instance BA.ByteArrayAccess Tx where
    length        = BA.length . Write.toStrictByteString . encodeTx
    withByteArray = BA.withByteArray . Write.toStrictByteString . encodeTx

-- | Check that all values in a transaction are no.
--
validValuesTx :: Tx -> Bool
validValuesTx Tx{..}
  = all ((>= 0) . txOutValue) txOutputs && txForge >= 0 && txFee >= 0

-- | Transaction without witnesses for its inputs
data TxStripped = TxStripped {
    txStrippedInputs  :: Set.Set TxOutRef',
    txStrippedOutputs :: [TxOut'],
    txStrippedForge   :: !Value,
    txStrippedFee     :: !Value
    } deriving (Show, Eq, Ord)

instance BA.ByteArrayAccess TxStripped where
    length = BA.length . BS.pack . show
    withByteArray = BA.withByteArray . BS.pack . show

strip :: Tx -> TxStripped
strip Tx{..} = TxStripped i txOutputs txForge txFee where
    i = Set.map txInRef txInputs

-- | Hash a stripped transaction once
preHash :: TxStripped -> Digest SHA256
preHash = hash

-- | Double hash of a transaction, excluding its witnesses
hashTx :: Tx -> TxId'
hashTx = TxId . hash . preHash . strip

-- | Reference to a transaction output
data TxOutRef h = TxOutRef {
    txOutRefId  :: !(TxId h),
    txOutRefIdx :: !Int -- ^ Index into the referenced transaction's outputs
    } deriving (Show, Eq, Ord)

type TxOutRef' = TxOutRef (Digest SHA256)

encodeTxOutRef :: TxOutRef' -> Encoding
encodeTxOutRef TxOutRef{..} =
    encodeTxId txOutRefId
    <> Enc.encodeInt txOutRefIdx

-- | Type of transaction input.
data TxInType =
      ConsumeScriptAddress !Validator !Redeemer
    | ConsumePublicKeyAddress !Signature
    deriving (Show, Eq, Ord)

encodeTxInType :: TxInType -> Encoding
encodeTxInType = \case
    ConsumeScriptAddress v r  -> encodeValidator v <> encodeRedeemer r
    ConsumePublicKeyAddress s -> encodeSignature s

-- | Transaction input
data TxIn h = TxIn {
    txInRef  :: !(TxOutRef h),
    txInType :: !TxInType
    } deriving (Show, Eq, Ord)

type TxIn' = TxIn (Digest SHA256)

-- | The `TxOutRef` spent by a transaction input
inRef :: Lens (TxIn h) (TxIn g) (TxOutRef h) (TxOutRef g)
inRef = lens txInRef s where
    s txi r = txi { txInRef = r }

-- | The type of a transaction input
inType :: Lens' (TxIn h) TxInType
inType = lens txInType s where
    s txi t = txi { txInType = t }

-- | Validator and redeemer scripts of a transaction input that spends a
--   "pay to script" output
--
inScripts :: TxIn h -> Maybe (Validator, Redeemer)
inScripts TxIn{ txInType = t } = case t of
    ConsumeScriptAddress v r  -> Just (v, r)
    ConsumePublicKeyAddress _ -> Nothing

-- | Signature of a transaction input that spends a "pay to public key" output
--
inSignature :: TxIn h -> Maybe Signature
inSignature TxIn{ txInType = t } = case t of
    ConsumeScriptAddress _ _ -> Nothing
    ConsumePublicKeyAddress s   -> Just s

pubKeyTxIn :: TxOutRef h -> Signature -> TxIn h
pubKeyTxIn r = TxIn r . ConsumePublicKeyAddress

scriptTxIn :: TxOutRef h -> Validator -> Redeemer -> TxIn h
scriptTxIn r v = TxIn r . ConsumeScriptAddress v

encodeTxIn :: TxIn' -> Encoding
encodeTxIn TxIn{..} =
    encodeTxOutRef txInRef
    <> encodeTxInType txInType

instance BA.ByteArrayAccess TxIn' where
    length        = BA.length . Write.toStrictByteString . encodeTxIn
    withByteArray = BA.withByteArray . Write.toStrictByteString . encodeTxIn

-- | Type of transaction output.
data TxOutType =
    PayToScript !DataScript
    | PayToPubKey !PubKey
    deriving (Show, Eq, Ord)

encodeTxOutType :: TxOutType -> Encoding
encodeTxOutType = \case
    PayToScript sc -> encodeDataScript sc
    PayToPubKey pk -> encodePubKey pk

-- Transaction output
data TxOut h = TxOut {
    txOutAddress :: !(Address h),
    txOutValue   :: !Value,
    txOutType    :: !TxOutType
    }
    deriving (Show, Eq, Ord)

type TxOut' = TxOut (Digest SHA256)

-- | The data script that a [[TxOut]] refers to
txOutData :: TxOut h -> Maybe DataScript
txOutData TxOut{txOutType = t} = case  t of
    PayToScript s -> Just s
    PayToPubKey _ -> Nothing

-- | The public key that a [[TxOut]] refers to
txOutPubKey :: TxOut h -> Maybe PubKey
txOutPubKey TxOut{txOutType = t} = case  t of
    PayToPubKey k -> Just k
    _ -> Nothing

-- | The address of a transaction output
outAddress :: Lens (TxOut h) (TxOut g) (Address h) (Address g)
outAddress = lens txOutAddress s where
    s tx a = tx { txOutAddress = a }

-- | The value of a transaction output
-- | TODO: Compute address again
outValue :: Lens' (TxOut h) Value
outValue = lens txOutValue s where
    s tx v = tx { txOutValue = v }

-- | The type of a transaction output
-- | TODO: Compute address again
outType :: Lens' (TxOut h) TxOutType
outType = lens txOutType s where
    s tx d = tx { txOutType = d }

-- | The address of a transaction output locked by public key
pubKeyAddress :: Value -> PubKey -> Address (Digest SHA256)
pubKeyAddress v pk = Address $ hash h where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    e = encodeValue v <> encodePubKey pk

-- | The address of a transaction output locked by a validator script
scriptAddress :: Value -> Validator -> DataScript -> Address (Digest SHA256)
scriptAddress v vl ds = Address $ hash h where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    e = encodeValue v <> encodeValidator vl <> encodeDataScript ds

-- | Create a transaction output locked by a validator script
scriptTxOut :: Value -> Validator -> DataScript -> TxOut'
scriptTxOut v vl ds = TxOut a v tp where
    a = scriptAddress v vl ds
    tp = PayToScript ds

-- | Create a transaction output locked by a public key
pubKeyTxOut :: Value -> PubKey -> TxOut'
pubKeyTxOut v pk = TxOut a v tp where
    a = pubKeyAddress v pk
    tp = PayToPubKey pk

encodeTxOut :: TxOut' -> Encoding
encodeTxOut TxOut{..} =
    encodeAddress txOutAddress
    <> encodeValue txOutValue
    <> encodeTxOutType txOutType

instance BA.ByteArrayAccess TxOut' where
    length        = BA.length . Write.toStrictByteString . encodeTxOut
    withByteArray = BA.withByteArray . Write.toStrictByteString . encodeTxOut

type Block = [Tx]
type Blockchain = [Block]

-- | Lookup a transaction by its hash
transaction :: Blockchain -> TxOutRef' -> Maybe Tx
transaction bc o = listToMaybe $ filter p  $ join bc where
    p = (txOutRefId o ==) . hashTx

-- | Determine the unspent output that an input refers to
out :: Blockchain -> TxOutRef' -> Maybe TxOut'
out bc o = do
    t <- transaction bc o
    let i = txOutRefIdx o
    if length (txOutputs t) <= i
        then Nothing
        else Just $ txOutputs t !! i

-- | Determine the unspent value that an input refers to
value :: Blockchain -> TxOutRef' -> Maybe Value
value bc o = txOutValue <$> out bc o

-- | Determine the data script that an input refers to
dataTxo :: Blockchain -> TxOutRef' -> Maybe DataScript
dataTxo bc o = txOutData =<< out bc o

-- | Determine the public key that locks the txo
pubKeyTxo :: Blockchain -> TxOutRef' -> Maybe PubKey
pubKeyTxo bc o = out bc o >>= txOutPubKey

-- | The unspent outputs of a transaction
unspentOutputsTx :: Tx -> Map TxOutRef' TxOut'
unspentOutputsTx t = Map.fromList $ fmap f $ zip [0..] $ txOutputs t where
    f (idx, o) = (TxOutRef (hashTx t) idx, o)

-- | The outputs consumed by a transaction
spentOutputs :: Tx -> Set.Set TxOutRef'
spentOutputs = Set.map txInRef . txInputs

-- | Unspent outputs of a ledger.
unspentOutputs :: Blockchain -> Map TxOutRef' TxOut'
unspentOutputs = foldr ins Map.empty . join where
    ins t unspent = (unspent `Map.difference` lift (spentOutputs t)) `Map.union` unspentOutputsTx t
    lift = Map.fromSet (const ())

-- | Ledger and transaction state available to both the validator and redeemer
--   scripts
--
data BlockchainState = BlockchainState {
    blockchainStateHeight :: Height,
    blockchainStateTxHash :: TxId'
    }

-- | Get blockchain state for a transaction
state :: Tx -> Blockchain -> BlockchainState
state tx bc = BlockchainState (height bc) (hashTx tx)

-- | Determine whether a transaction is valid in a given ledger
--
-- * The inputs refer to unspent outputs, which they unlock (input validity).
--
-- * The transaction preserves value (value preservation).
--
-- * All values in the transaction are non-negative.
--
validTx :: Tx -> Blockchain -> Bool
validTx t bc = inputsAreValid && valueIsPreserved && validValuesTx t where
    inputsAreValid = all (`validatesIn` unspentOutputs bc) (txInputs t)
    valueIsPreserved = inVal == outVal
    inVal =
        txForge t + getSum (foldMap (Sum . fromMaybe 0 . value bc . txInRef) (txInputs t))
    outVal =
        txFee t + sum (map txOutValue (txOutputs t))
    txIn `validatesIn` allOutputs =
        maybe False (validate (state t bc) txIn)
        $ txInRef txIn `Map.lookup` allOutputs

-- | Check whether a transaction output can be spent by the given
--   transaction input. This involves
--
--   * Checking that pay-to-script (P2S) output is spent by a P2S input, and a 
--     pay-to-public key (P2PK) output is spend by a P2PK input
--   * If it is a P2S input:
--     * Verifying the hash of the validator script
--     * Evaluating the validator script with the redeemer and data script
--   * If it is a P2PK input:
--     * Verifying that the signature matches the public key
--
validate :: BlockchainState -> TxIn' -> TxOut' -> Bool
validate bs TxIn{ txInType = ti } TxOut{..} = 
    case (ti, txOutType) of
        (ConsumeScriptAddress v r, PayToScript d)
            | txOutAddress /= scriptAddress txOutValue v d -> False
            | otherwise                                    -> runScript bs v r d
        (ConsumePublicKeyAddress sig, PayToPubKey pk) -> sig `signedBy` pk
        _ -> False

-- | Evaluate a validator script with the given inputs
runScript :: BlockchainState -> Validator -> Redeemer -> DataScript -> Bool
runScript _ (Validator (getAst -> validator)) (Redeemer (getAst -> redeemer)) (DataScript (getAst -> dataScript)) =
    let
        applied = (validator `applyProgram` redeemer) `applyProgram` dataScript
        -- TODO: do something with the error
        inferred = either (const Nothing) Just $ runExcept $ runQuoteT $ void $ typecheckPipeline 1000 applied
    in isJust $ do
        void inferred
        evaluationResultToMaybe $ runCk applied

-- | () as a data script
unitData :: DataScript
unitData = DataScript $(plutus [| () |])

-- | \() () -> () as a validator
emptyValidator :: Validator
emptyValidator = Validator $(plutus [| \() () -> () |])

-- | () as a redeemer
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $(plutus [| () |])

-- | Transaction output locked by the empty validator and unit data scripts.
simpleOutput :: Value -> TxOut'
simpleOutput vl = scriptTxOut vl emptyValidator unitData

-- | Transaction input that spends an output using the empty validator and
--   unit redeemer scripts.
simpleInput :: TxOutRef a -> TxIn a
simpleInput ref = scriptTxIn ref emptyValidator unitRedeemer

