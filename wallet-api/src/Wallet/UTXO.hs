{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Wallet.UTXO(
    -- * Basic types
    Value(..),
    TxId(..),
    Address(..),
    Height(..),
    height,
    -- * Script types
    Validator(..),
    hashValidator,
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
    TxOut(..),
    TxOutRef(..),
    simpleInput,
    simpleOutput,
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
    -- * Scripts
    validate,
    emptyValidator,
    unitRedeemer,
    unitData,
    -- * Encodings
    encodeValue,
    encodeValidator,
    encodeDataScript,
    hashDataScript,
    encodeRedeemer,
    hashRedeemer,
    encodeHeight,
    encodeTxId,
    encodeAddress,
    encodeTx,
    encodeTxOutRef,
    encodeTxIn,
    encodeTxOut
    ) where

import           Codec.CBOR.Encoding              (Encoding)
import qualified Codec.CBOR.Encoding              as Enc
import qualified Codec.CBOR.Write                 as Write
import           Control.Monad                    (join)
import           Control.Monad.Except
import           Crypto.Hash                      (Digest, SHA256, hash)
import qualified Data.ByteArray                   as BA
import qualified Data.ByteString.Char8            as BS
import qualified Data.ByteString.Lazy             as BSL
import           Data.Foldable                    (foldMap)
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Maybe                       (fromMaybe, listToMaybe, isJust)
import           Data.Monoid                      (Sum(..))
import           Data.Semigroup                   (Semigroup (..))
import           Data.Set                         (Set)
import qualified Data.Set as Set

import           Language.Plutus.CoreToPLC.Plugin (PlcCode, getSerializedCode, getAst)
import           Language.Plutus.TH               (plutusT)
import           Language.PlutusCore              (applyProgram, typecheckPipeline)
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Evaluation.CkMachine  (runCk)
import           Language.PlutusCore.Evaluation.Result

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

-- | Cryptocurrency value
--
newtype Value = Value { getValue :: Integer }
    deriving (Eq, Ord, Show, Num, Integral, Real, Enum)

encodeValue :: Value -> Encoding
encodeValue = Enc.encodeInteger . getValue

-- | Transaction ID (double SHA256 hash of the transaction)
newtype TxId = TxId { getTxId :: Digest SHA256 }
    deriving (Eq, Ord, Show)

encodeTxId :: TxId -> Encoding
encodeTxId = Enc.encodeBytes . BA.convert . getTxId

-- | A payment address is a double SHA256 of a
--   UTxO output's validator script (and presumably its data script).
--   This corresponds to a Bitcoing pay-to-witness-script-hash
newtype Address = Address { getAddress :: Digest SHA256 }
    deriving (Eq, Ord, Show)

encodeAddress :: Address -> Encoding
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

-- | Hash a validator script to get an address
hashValidator :: Validator -> Address
hashValidator = Address . hash

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

-- | Hash a data script to get an address
hashDataScript :: DataScript -> Address
hashDataScript = Address . hash

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

-- | Hash a redeemer script to get an address
hashRedeemer :: Redeemer -> Address
hashRedeemer = Address . hash . Write.toStrictByteString . encodeRedeemer

-- | Block height
newtype Height = Height { getHeight :: Integer }
    deriving (Eq, Ord, Show)

encodeHeight :: Height -> Encoding
encodeHeight = Enc.encodeInteger . getHeight

-- | The height of a blockchain
height :: Blockchain -> Height
height = Height . fromIntegral . length . join

-- | Transaction including witnesses for its inputs
data Tx = Tx {
    txInputs  :: Set TxIn,
    txOutputs :: [TxOut],
    txForge   :: !Value,
    txFee     :: !Value
    } deriving (Show, Eq, Ord)

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
    txStrippedInputs  :: Set TxOutRef,
    txStrippedOutputs :: [TxOut],
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
hashTx :: Tx -> TxId
hashTx = TxId . hash . preHash . strip

-- | Reference to a transaction output
data TxOutRef = TxOutRef {
    txOutRefId  :: !TxId,
    txOutRefIdx :: !Int -- ^ Index into the referenced transaction's outputs
    } deriving (Show, Eq, Ord)

encodeTxOutRef :: TxOutRef -> Encoding
encodeTxOutRef TxOutRef{..} =
    encodeTxId txOutRefId
    <> Enc.encodeInt txOutRefIdx

-- | Transaction input
data TxIn = TxIn {
    txInRef       :: !TxOutRef,
    txInValidator :: !Validator,
    txInRedeemer  :: !Redeemer
    } deriving (Show, Eq, Ord)

encodeTxIn :: TxIn -> Encoding
encodeTxIn TxIn{..} =
    encodeTxOutRef txInRef
    <> encodeValidator txInValidator
    <> encodeRedeemer txInRedeemer

instance BA.ByteArrayAccess TxIn where
    length        = BA.length . Write.toStrictByteString . encodeTxIn
    withByteArray = BA.withByteArray . Write.toStrictByteString . encodeTxIn

-- Transaction output
data TxOut = TxOut {
    txOutAddress :: !Address,
    txOutValue   :: !Value,
    txOutData    :: !DataScript
    } deriving (Show, Eq, Ord)

encodeTxOut :: TxOut -> Encoding
encodeTxOut TxOut{..} =
    encodeAddress txOutAddress
    <> encodeValue txOutValue
    <> encodeDataScript txOutData

instance BA.ByteArrayAccess TxOut where
    length        = BA.length . Write.toStrictByteString . encodeTxOut
    withByteArray = BA.withByteArray . Write.toStrictByteString . encodeTxOut

type Block = [Tx]
type Blockchain = [Block]

-- | Lookup a transaction by its hash
transaction :: Blockchain -> TxOutRef -> Maybe Tx
transaction bc o = listToMaybe $ filter p  $ join bc where
    p = (txOutRefId o ==) . hashTx

-- | Determine the unspent output that an input refers to
out :: Blockchain -> TxOutRef -> Maybe TxOut
out bc o = do
    t <- transaction bc o
    let i = txOutRefIdx o
    if length (txOutputs t) <= i
        then Nothing
        else Just $ txOutputs t !! i

-- | Determine the unspent value that an input refers to
value :: Blockchain -> TxOutRef -> Maybe Value
value bc o = txOutValue <$> out bc o

-- | Determine the data script that an input refers to
dataTxo :: Blockchain -> TxOutRef -> Maybe DataScript
dataTxo bc o = txOutData <$> out bc o

-- | The unspent outputs of a transaction
unspentOutputsTx :: Tx -> Map TxOutRef TxOut
unspentOutputsTx t = Map.fromList $ fmap f $ zip [0..] $ txOutputs t where
    f (idx, o) = (TxOutRef (hashTx t) idx, o)

-- | The outputs consumed by a transaction
spentOutputs :: Tx -> Set TxOutRef
spentOutputs = Set.map txInRef . txInputs

-- | Unspent outputs of a ledger.
unspentOutputs :: Blockchain -> Map TxOutRef TxOut
unspentOutputs = foldr ins Map.empty . join where
    ins t unspent = (unspent `Map.difference` lift (spentOutputs t)) `Map.union` unspentOutputsTx t
    lift = Map.fromSet (const ())

-- | Ledger and transaction state available to both the validator and redeemer
--   scripts
--
data BlockchainState = BlockchainState {
    blockchainStateHeight :: Height,
    blockchainStateTxHash :: TxId
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
--   * Verifying the hash of the validator script
--   * Evaluating the validator script with the redeemer and data script
--
validate :: BlockchainState -> TxIn -> TxOut -> Bool
validate bs (TxIn _ v r) (TxOut h _ d)
    | h /= hashValidator v = False
    | otherwise            = runScript bs v r d

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
unitData = DataScript $$(plutusT [|| () ||])

-- | \() () -> () as a validator
emptyValidator :: Validator
emptyValidator = Validator $$(plutusT [|| \() () -> () ||])

-- | () as a redeemer
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $$(plutusT [|| () ||])

-- | Transaction output locked by the empty validator and unit data scripts.
simpleOutput :: Value -> TxOut
simpleOutput vl = TxOut (hashValidator emptyValidator) vl unitData

-- | Transaction input that spends an output using the empty validator and
--   unit redeemer scripts.
simpleInput :: TxOutRef -> TxIn
simpleInput ref = TxIn ref emptyValidator unitRedeemer
