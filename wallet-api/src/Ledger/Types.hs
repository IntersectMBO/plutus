{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ledger.Types(
    -- * Basic types
    Value,
    Ada,
    Slot(..),
    SlotRange,
    lastSlot,
    TxIdOf(..),
    TxId,
    PubKey(..),
    Signature(..),
    signedBy,
    -- ** Addresses
    AddressOf(..),
    Address,
    pubKeyAddress,
    scriptAddress,
    -- ** Scripts
    Script,
    fromCompiledCode,
    compileScript,
    lifted,
    applyScript,
    evaluateScript,
    ValidatorScript(..),
    RedeemerScript(..),
    DataScript(..),
    -- * Transactions
    Tx(..),
    TxStripped(..),
    strip,
    preHash,
    hashTx,
    dataTxo,
    TxInOf(..),
    TxInType(..),
    TxIn,
    TxOutOf(..),
    TxOutType(..),
    TxOut,
    TxOutRefOf(..),
    TxOutRef,
    pubKeyTxIn,
    scriptTxIn,
    pubKeyTxOut,
    scriptTxOut,
    isPubKeyOut,
    isPayToScriptOut,
    txOutRefs,
    -- * Blockchain & UTxO model
    Block,
    Blockchain,
    ValidationData(..),
    transaction,
    out,
    value,
    unspentOutputsTx,
    spentOutputs,
    unspentOutputs,
    updateUtxo,
    txOutPubKey,
    pubKeyTxo,
    validValuesTx,
    -- * Scripts
    unitRedeemer,
    unitData,
    runScript,
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
    validRange
    ) where

import qualified Codec.CBOR.Write                         as Write
import           Codec.Serialise                          (deserialise, deserialiseOrFail, serialise)
import           Codec.Serialise.Class                    (Serialise, decode, encode)
import           Control.Lens                             hiding (lifted)
import           Control.Monad                            (join)
import           Control.Newtype.Generics     (Newtype)
import           Crypto.Hash                              (Digest, SHA256, digestFromByteString, hash)
import           Data.Aeson                               (FromJSON (parseJSON), ToJSON (toJSON), withText)
import qualified Data.Aeson                               as JSON
import           Data.Bifunctor                           (first)
import qualified Data.ByteArray                           as BA
import qualified Data.ByteString                          as BSS
import qualified Data.ByteString.Base64                   as Base64
import qualified Data.ByteString.Char8                    as BS8
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import           Data.Maybe                               (isJust, listToMaybe)
import           Data.Proxy                               (Proxy(Proxy))
import qualified Data.Set                                 as Set
import qualified Data.Text.Encoding                       as TE
import           GHC.Generics                             (Generic)
import           Data.Swagger.Internal.Schema             (ToSchema(declareNamedSchema), plain, paramSchemaToSchema)
import qualified Language.Haskell.TH                      as TH
import qualified Language.PlutusCore                      as PLC
import           Language.PlutusTx.Evaluation             (evaluateCekTrace)
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusTx.Lift                   (makeLift, unsafeLiftProgram)
import           Language.PlutusTx.Lift.Class             (Lift)
import           Language.PlutusTx.TH                     (CompiledCode, compile, getSerializedPlc)

import           Ledger.Interval                          (Slot(..), SlotRange)
import           Ledger.Ada                               (Ada)
import           Ledger.Value                             (Value)
import qualified Ledger.Value.TH                          as V

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
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON, Newtype)
    deriving newtype (Serialise)

makeLift ''PubKey

newtype Signature = Signature { getSignature :: Int }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

makeLift ''Signature

-- | True if the signature matches the public key
signedBy :: Signature -> PubKey -> Bool
signedBy (Signature k) (PubKey s) = k == s

-- | Transaction ID (double SHA256 hash of the transaction)
newtype TxIdOf h = TxIdOf { getTxId :: h }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)

makeLift ''TxIdOf

type TxId = TxIdOf (Digest SHA256)

deriving newtype instance Serialise TxId
deriving anyclass instance ToJSON a => ToJSON (TxIdOf a)
deriving anyclass instance FromJSON a => FromJSON (TxIdOf a)
deriving anyclass instance ToSchema a => ToSchema (TxIdOf a)

instance Serialise (Digest SHA256) where
  encode = encode . BA.unpack
  decode = do
    d <- decode
    let md = digestFromByteString . BSS.pack $ d
    case md of
      Nothing -> fail "couldn't decode to Digest SHA256"
      Just v  -> pure v

instance ToJSON (Digest SHA256) where
  toJSON = JSON.String . TE.decodeUtf8 . Base64.encode . Write.toStrictByteString . encode

instance ToSchema (Digest SHA256) where
  declareNamedSchema _ = plain . paramSchemaToSchema $ (Proxy :: Proxy String)

instance FromJSON (Digest SHA256) where
  parseJSON = withText "SHA256" $ \s -> do
    let ev = do
          eun64 <- Base64.decode . TE.encodeUtf8 $ s
          first show $ deserialiseOrFail $ BSL.fromStrict eun64
    case ev of
      Left e  -> fail e
      Right v -> pure v

-- | A payment address is a double SHA256 of a
--   UTxO output's validator script (and presumably its data script).
--   This corresponds to a Bitcoing pay-to-witness-script-hash
newtype AddressOf h = AddressOf { getAddress :: h }
    deriving (Eq, Ord, Show, Generic)

type Address = AddressOf (Digest SHA256)

deriving newtype instance Serialise Address
deriving anyclass instance ToJSON Address
deriving anyclass instance FromJSON Address

-- | Script
newtype Script = Script { getSerialized :: BSL.ByteString }
  deriving newtype (Serialise, Eq, Ord)

  -- TODO: possibly this belongs with CompiledCode
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = Script . getSerializedPlc

-- | Compile a quoted Haskell expression to a 'Script'
compileScript :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp Script)
compileScript a = [|| Script $ getSerializedPlc $ $$(compile a) ||]

getPlc :: Script -> PLC.Program PLC.TyName PLC.Name ()
getPlc = deserialise . getSerialized

applyScript :: Script -> Script -> Script
-- TODO: this is a bit inefficient
applyScript (getPlc -> s1) (getPlc -> s2) = Script $ serialise $ s1 `PLC.applyProgram` s2

evaluateScript :: Script -> ([String], Bool)
evaluateScript (getPlc -> s) = (isJust . evaluationResultToMaybe) <$> evaluateCekTrace s

instance ToJSON Script where
  toJSON = JSON.String . TE.decodeUtf8 . Base64.encode . BSL.toStrict . serialise

instance FromJSON Script where
  parseJSON = withText "Script" $ \s -> do
    let ev = do
          eun64 <- Base64.decode . TE.encodeUtf8 $ s
          first show $ deserialiseOrFail $ BSL.fromStrict eun64
    case ev of
      Left e  -> fail e
      Right v -> pure v

lifted :: Lift a => a -> Script
lifted = Script . serialise . unsafeLiftProgram

-- | A validator is a PLC script.
newtype ValidatorScript = ValidatorScript { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show ValidatorScript where
    show = const "ValidatorScript { <script> }"

instance Eq ValidatorScript where
    (ValidatorScript l) == (ValidatorScript r) = -- TODO: Deriving via
        l == r

instance Ord ValidatorScript where
    compare (ValidatorScript l) (ValidatorScript r) = -- TODO: Deriving via
        l `compare` r

instance BA.ByteArrayAccess ValidatorScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | Data script (supplied by producer of the transaction output)
newtype DataScript = DataScript { getDataScript :: Script  }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show DataScript where
    show = const "DataScript { <script> }"

instance Eq DataScript where
    (DataScript l) == (DataScript r) = -- TODO: Deriving via
        l == r

instance Ord DataScript where
    compare (DataScript l) (DataScript r) = -- TODO: Deriving via
        l `compare` r

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | Redeemer (supplied by consumer of the transaction output)
newtype RedeemerScript = RedeemerScript { getRedeemer :: Script }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show RedeemerScript where
    show = const "RedeemerScript { <script> }"

instance Eq RedeemerScript where
    (RedeemerScript l) == (RedeemerScript r) = -- TODO: Deriving via
        l == r

instance Ord RedeemerScript where
    compare (RedeemerScript l) (RedeemerScript r) = -- TODO: Deriving via
        l `compare` r

instance BA.ByteArrayAccess RedeemerScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | The number of the last slot of a blockchain. Assumes that empty slots are
--   represented as empty blocks (as opposed to no blocks). This is true in the
--   emulator but not necessarily on the real chain,
lastSlot :: Blockchain -> Slot
lastSlot = Slot . length

-- | Transaction including witnesses for its inputs
data Tx = Tx {
    txInputs     :: Set.Set TxIn,
    txOutputs    :: [TxOut],
    txForge      :: !Value,
    txFee        :: !Ada,
    txValidRange :: !SlotRange
    -- ^ The 'SlotRange' during which this transaction may be validated
    } deriving (Show, Eq, Ord, Generic, Serialise, ToJSON, FromJSON)

-- | The inputs of a transaction
inputs :: Lens' Tx (Set.Set TxIn)
inputs = lens g s where
    g = txInputs
    s tx i = tx { txInputs = i }

outputs :: Lens' Tx [TxOut]
outputs = lens g s where
    g = txOutputs
    s tx o = tx { txOutputs = o }

validRange :: Lens' Tx SlotRange
validRange = lens g s where
    g = txValidRange
    s tx o = tx { txValidRange = o }

instance BA.ByteArrayAccess Tx where
    length        = BA.length . Write.toStrictByteString . encode
    withByteArray = BA.withByteArray . Write.toStrictByteString . encode

-- | Check that all values in a transaction are non-negative
--
validValuesTx :: Tx -> Bool
validValuesTx Tx{..}
  = all (nonNegative . txOutValue) txOutputs && nonNegative txForge  && txFee >= 0 where
    nonNegative i = $$(V.geq) i $$(V.zero)

-- | Transaction without witnesses for its inputs
data TxStripped = TxStripped {
    txStrippedInputs  :: Set.Set TxOutRef,
    txStrippedOutputs :: [TxOut],
    txStrippedForge   :: !Value,
    txStrippedFee     :: !Ada
    } deriving (Show, Eq, Ord)

instance BA.ByteArrayAccess TxStripped where
    length = BA.length . BS8.pack . show
    withByteArray = BA.withByteArray . BS8.pack . show

strip :: Tx -> TxStripped
strip Tx{..} = TxStripped i txOutputs txForge txFee where
    i = Set.map txInRef txInputs

-- | Hash a stripped transaction once
preHash :: TxStripped -> Digest SHA256
preHash = hash

-- | Double hash of a transaction, excluding its witnesses
hashTx :: Tx -> TxId
hashTx = TxIdOf . hash . preHash . strip

-- | Reference to a transaction output
data TxOutRefOf h = TxOutRefOf {
    txOutRefId  :: TxIdOf h,
    txOutRefIdx :: Int -- ^ Index into the referenced transaction's outputs
    } deriving (Show, Eq, Ord, Generic)

type TxOutRef = TxOutRefOf (Digest SHA256)

deriving instance Serialise TxOutRef
deriving instance ToJSON TxOutRef
deriving instance FromJSON TxOutRef
deriving instance ToSchema TxOutRef

-- | A list of a transaction's outputs paired with their [[TxOutRef]]s
txOutRefs :: Tx -> [(TxOut, TxOutRef)]
txOutRefs t = mkOut <$> zip [0..] (txOutputs t) where
    mkOut (i, o) = (o, TxOutRefOf txId i)
    txId = hashTx t

-- | Type of transaction input.
data TxInType =
      ConsumeScriptAddress !ValidatorScript !RedeemerScript
    | ConsumePublicKeyAddress !Signature
    deriving (Show, Eq, Ord, Generic, Serialise, ToJSON, FromJSON)

-- | Transaction input
data TxInOf h = TxInOf {
    txInRef  :: !(TxOutRefOf h),
    txInType :: !TxInType
    } deriving (Show, Eq, Ord, Generic)

type TxIn = TxInOf (Digest SHA256)

deriving instance Serialise TxIn
deriving instance ToJSON TxIn
deriving instance FromJSON TxIn

-- | The 'TxOutRefOf' spent by a transaction input
inRef :: Lens (TxInOf h) (TxInOf g) (TxOutRefOf h) (TxOutRefOf g)
inRef = lens txInRef s where
    s txi r = txi { txInRef = r }

-- | The type of a transaction input
inType :: Lens' (TxInOf h) TxInType
inType = lens txInType s where
    s txi t = txi { txInType = t }

-- | Validator and redeemer scripts of a transaction input that spends a
--   "pay to script" output
--
inScripts :: TxInOf h -> Maybe (ValidatorScript, RedeemerScript)
inScripts TxInOf{ txInType = t } = case t of
    ConsumeScriptAddress v r  -> Just (v, r)
    ConsumePublicKeyAddress _ -> Nothing

-- | Signature of a transaction input that spends a "pay to public key" output
--
inSignature :: TxInOf h -> Maybe Signature
inSignature TxInOf{ txInType = t } = case t of
    ConsumeScriptAddress _ _  -> Nothing
    ConsumePublicKeyAddress s -> Just s

pubKeyTxIn :: TxOutRefOf h -> Signature -> TxInOf h
pubKeyTxIn r = TxInOf r . ConsumePublicKeyAddress

scriptTxIn :: TxOutRefOf h -> ValidatorScript -> RedeemerScript -> TxInOf h
scriptTxIn r v = TxInOf r . ConsumeScriptAddress v

instance BA.ByteArrayAccess TxIn where
    length        = BA.length . Write.toStrictByteString . encode
    withByteArray = BA.withByteArray . Write.toStrictByteString . encode

-- | Type of transaction output.
data TxOutType =
    PayToScript !DataScript -- ^ A pay-to-script output with the data script
    | PayToPubKey !PubKey -- ^ A pay-to-pubkey output
    deriving (Show, Eq, Ord, Generic, Serialise, ToJSON, FromJSON)

-- Transaction output
data TxOutOf h = TxOutOf {
    txOutAddress :: !(AddressOf h),
    txOutValue   :: !Value,
    txOutType    :: !TxOutType
    }
    deriving (Show, Eq, Ord, Generic)

type TxOut = TxOutOf (Digest SHA256)

deriving instance Serialise TxOut
deriving instance ToJSON TxOut
deriving instance FromJSON TxOut

-- | The data script that a [[TxOutOf]] refers to
txOutData :: TxOutOf h -> Maybe DataScript
txOutData TxOutOf{txOutType = t} = case  t of
    PayToScript s -> Just s
    PayToPubKey _ -> Nothing

-- | The public key that a [[TxOut]] refers to
txOutPubKey :: TxOutOf h -> Maybe PubKey
txOutPubKey TxOutOf{txOutType = t} = case  t of
    PayToPubKey k -> Just k
    _             -> Nothing

-- | The address of a transaction output
outAddress :: Lens (TxOutOf h) (TxOutOf g) (AddressOf h) (AddressOf g)
outAddress = lens txOutAddress s where
    s tx a = tx { txOutAddress = a }

-- | The value of a transaction output
-- | TODO: Compute address again
outValue :: Lens' (TxOutOf h) Value
outValue = lens txOutValue s where
    s tx v = tx { txOutValue = v }

-- | The type of a transaction output
-- | TODO: Compute address again
outType :: Lens' (TxOutOf h) TxOutType
outType = lens txOutType s where
    s tx d = tx { txOutType = d }

-- | Returns true if the output is a pay-to-pubkey output
isPubKeyOut :: TxOutOf h -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Returns true if the output is a pay-to-script output
isPayToScriptOut :: TxOutOf h -> Bool
isPayToScriptOut = isJust . txOutData

-- | The address of a transaction output locked by public key
pubKeyAddress :: PubKey -> AddressOf (Digest SHA256)
pubKeyAddress pk = AddressOf $ hash h where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    e = encode pk

-- | The address of a transaction output locked by a validator script
scriptAddress :: ValidatorScript -> AddressOf (Digest SHA256)
scriptAddress vl = AddressOf $ hash h where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    e = encode vl

-- | Create a transaction output locked by a validator script
scriptTxOut :: Value -> ValidatorScript -> DataScript -> TxOut
scriptTxOut v vl ds = TxOutOf a v tp where
    a = scriptAddress vl
    tp = PayToScript ds

-- | Create a transaction output locked by a public key
pubKeyTxOut :: Value -> PubKey -> TxOut
pubKeyTxOut v pk = TxOutOf a v tp where
    a = pubKeyAddress pk
    tp = PayToPubKey pk

instance BA.ByteArrayAccess TxOut where
    length        = BA.length . Write.toStrictByteString . encode
    withByteArray = BA.withByteArray . Write.toStrictByteString . encode

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
dataTxo bc o = txOutData =<< out bc o

-- | Determine the public key that locks the txo
pubKeyTxo :: Blockchain -> TxOutRef -> Maybe PubKey
pubKeyTxo bc o = out bc o >>= txOutPubKey

-- | The unspent outputs of a transaction
unspentOutputsTx :: Tx -> Map TxOutRef TxOut
unspentOutputsTx t = Map.fromList $ fmap f $ zip [0..] $ txOutputs t where
    f (idx, o) = (TxOutRefOf (hashTx t) idx, o)

-- | The outputs consumed by a transaction
spentOutputs :: Tx -> Set.Set TxOutRef
spentOutputs = Set.map txInRef . txInputs

-- | Unspent outputs of a ledger.
unspentOutputs :: Blockchain -> Map TxOutRef TxOut
unspentOutputs = foldr updateUtxo Map.empty . join

-- | Update a map of unspent transaction outputs and sigantures with the inputs
--   and outputs of a transaction.
updateUtxo :: Tx -> Map TxOutRef TxOut -> Map TxOutRef TxOut
updateUtxo t unspent = (unspent `Map.difference` lift' (spentOutputs t)) `Map.union` outs where
    lift' = Map.fromSet (const ())
    outs = unspentOutputsTx t

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in PLC.
--
--   In the future we will generate this at transaction validation time, but
--   for now we have to construct it at compilation time (in the test suite)
--   and pass it to the validator.
newtype ValidationData = ValidationData Script
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Show ValidationData where
    show = const "ValidationData { <script> }"

-- | Evaluate a validator script with the given inputs
runScript :: ValidationData -> ValidatorScript -> RedeemerScript -> DataScript -> ([String], Bool)
runScript (ValidationData valData) (ValidatorScript validator) (RedeemerScript redeemer) (DataScript dataScript) =
    let
        applied = ((validator `applyScript` redeemer) `applyScript` dataScript) `applyScript` valData
        -- TODO: do something with the error
    in evaluateScript applied
        -- TODO: Enable type checking of the program
        -- void typecheck

-- | () as a data script
unitData :: DataScript
unitData = DataScript $ fromCompiledCode $$(compile [|| () ||])

-- | () as a redeemer
unitRedeemer :: RedeemerScript
unitRedeemer = RedeemerScript $ fromCompiledCode $$(compile [|| () ||])
