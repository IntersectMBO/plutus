{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Validation
    (
    -- * Pending transactions and related types
      PendingTx(..)
    , PendingTxOut(..)
    , PendingTxOutRef(..)
    , PendingTxIn(..)
    , PendingTxOutType(..)
    -- ** Hashes (see note [Hashes in validator scripts])
    , DataScriptHash(..)
    , RedeemerHash(..)
    , ValidatorHash(..)
    , TxHash(..)
    , plcDataScriptHash
    , plcValidatorDigest
    , plcRedeemerHash
    , plcTxHash
    , plcDigest
    , plcCurrencySymbol
    , validatorScriptHash
    -- * Oracles
    , OracleValue(..)
    -- * Validator functions
    -- ** Signatures
    , txSignedBy
    -- ** Transactions
    , pubKeyOutput
    , scriptOutputsAt
    , pubKeyOutputsAt
    , valueLockedBy
    , valuePaidTo
    , adaLockedBy
    , signsTransaction
    , spendsOutput
    , valueSpent
    , ownCurrencySymbol
    , ownHashes
    , ownHash
    -- * Hashes
    , plcSHA2_256
    , plcSHA3_256
    , fromSymbol
    ) where

import           Codec.Serialise              (Serialise)
import           Crypto.Hash                  (Digest, SHA256)
import           Data.Aeson                   (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.ByteArray               as BA
import qualified Data.ByteString.Lazy         as BSL
import qualified Data.ByteString.Lazy.Hash    as Hash
import           Data.Hashable                (Hashable)
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Swagger.Internal.Schema (ToSchema (declareNamedSchema), paramSchemaToSchema, plain)
import           Data.String                  (IsString)
import           GHC.Generics                 (Generic)
import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude
import qualified Prelude                      as Haskell

import           Ledger.Ada                   (Ada)
import qualified Ledger.Ada                   as Ada
import           Ledger.Crypto                (PubKey (..), Signature (..))
import           Ledger.Scripts
import           Ledger.Slot                  (Slot, SlotRange)
import           Ledger.Tx                    (Address, getAddress, scriptAddress)
import qualified Ledger.TxId                  as Tx
import           Ledger.Value                 (CurrencySymbol (..), Value)
import qualified Ledger.Value                 as Value
import           LedgerBytes                  (LedgerBytes (..))

{- Note [Script types in pending transactions]
To validate a transaction, we have to evaluate the validation script of each of
the transaction's inputs. The validation script sees the data of the
transaction output it validates, and the redeemer of the transaction input of
the transaction that consumes it.
In addition, the validation script also needs information on the transaction as
a whole (not just the output-input pair it is concerned with). This information
is provided by the `PendingTx` type. A `PendingTx` contains the hashes of
redeemer and data scripts of all of its inputs and outputs.
-}

-- | The type of a transaction output in a pending transaction.
data PendingTxOutType
    = PubKeyTxOut PubKey -- ^ Pub key address
    | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])
    deriving (Generic)

-- | An output of a pending transaction.
data PendingTxOut = PendingTxOut
    { pendingTxOutValue  :: Value
    , pendingTxOutHashes :: Maybe (ValidatorHash, DataScriptHash) -- ^ Hashes of validator script and data script.
    , pendingTxOutData   :: PendingTxOutType
    } deriving (Generic)

-- | A reference to a transaction output in a pending transaction.
data PendingTxOutRef = PendingTxOutRef
    { pendingTxOutRefId  :: TxHash -- ^ Transaction whose output are consumed.
    , pendingTxOutRefIdx :: Integer -- ^ Index into the referenced transaction's list of outputs.
    } deriving (Generic)

-- | An input of a pending transaction.
data PendingTxIn = PendingTxIn
    { pendingTxInRef     :: PendingTxOutRef
    , pendingTxInWitness :: Maybe (ValidatorHash, RedeemerHash)
    -- ^ Tx input witness, hashes for Script input, or signature for a PubKey
    , pendingTxInValue   :: Value -- ^ Value consumed by this txn input
    } deriving (Generic)

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data PendingTx = PendingTx
    { pendingTxInputs     :: [PendingTxIn] -- ^ Transaction inputs
    , pendingTxOutputs    :: [PendingTxOut] -- ^ Transaction outputs
    , pendingTxFee        :: Ada -- ^ The fee paid by this transaction.
    , pendingTxForge      :: Value -- ^ The 'Value' forged by this transaction.
    , pendingTxIn         :: PendingTxIn -- ^ The 'PendingTxIn' being validated against currently.
    , pendingTxValidRange :: SlotRange -- ^ The valid range for the transaction.
    , pendingTxSignatures :: [(PubKey, Signature)]
    -- ^ Signatures provided with the transaction
    , pendingTxHash       :: TxHash
    -- ^ Hash of the pending transaction (excluding witnesses)
    } deriving (Generic)

{- Note [Oracles]
I'm not sure how oracles are going to work eventually, so I'm going to use this
definition for now:
* Oracles are identified by their public key
* An oracle can produce "observations", which are values annotated with time
  (slot number). These observations are signed by the oracle. This means we are
  assume a _trusted_ oracle (as opposed to services such as
  http://www.oraclize.it/ who provide untrusted oracles). Trusting the oracle
  makes sense when dealing with financial data: Current prices etc. are usually
  provided by companies such as Bloomberg or Yahoo Finance, who are
  necessarily trusted by the consumers of their data. It seems reasonable to
  assume that similar providers will exist for Plutus, who simply sign the
  data with a known key in the way we implemented it here.
* To use an oracle value inside a validator script, it has to be provided as the
  redeemer script of the transaction that consumes the output locked by the
  validator script.
Examples of this can be found in the
Language.Plutus.Coordination.Contracts.Swap.swapValidator and
Language.Plutus.Coordination.Contracts.Future.validatorScript scripts.
-}

-- | @OracleValue a@ is a value observed at a time signed by
-- an oracle. See note [Oracles].
data OracleValue a = OracleValue {
        ovSignature :: PubKey,
        ovSlot      :: Slot,
        ovValue     :: a
    }
    deriving (Generic)

{- Note [Hashes in validator scripts]

We need to deal with hashes of four different things in a validator script:

1. Transactions
2. Validator scripts
3. Data scripts
4. Redeemer scripts

The mockchain code in 'Ledger.Tx' only deals with the hashes of(1)
and (2), and uses the 'Ledger.Tx.TxId' and `Digest SHA256` types for
them.

In PLC validator scripts the situation is different: First, they need to work
with hashes of (1-4). Second, the `Digest SHA256` type is not available in PLC
- we have to represent all hashes as `ByteStrings`.

To ensure that we only compare hashes of the correct type inside a validator
script, we define a newtype for each of them, as well as functions for creating
them from the correct types in Haskell, and for comparing them (in
`Language.Plutus.Runtime.TH`).

-}
-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable)

instance ToSchema ValidatorHash where
    declareNamedSchema _ = plain . paramSchemaToSchema $ (Proxy :: Proxy String)

-- | Script runtime representation of a @Digest SHA256@.
newtype DataScriptHash =
    DataScriptHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable)

-- | Script runtime representation of a @Digest SHA256@.
newtype TxHash =
    TxHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable)

{-# INLINABLE plcDataScriptHash #-}
plcDataScriptHash :: DataScript -> DataScriptHash
plcDataScriptHash = DataScriptHash . plcSHA2_256 . BSL.pack . BA.unpack

{-# INLINABLE plcValidatorDigest #-}
-- | Compute the hash of a validator script.
plcValidatorDigest :: Digest SHA256 -> ValidatorHash
plcValidatorDigest = ValidatorHash . BSL.pack . BA.unpack

{-# INLINABLE plcRedeemerHash #-}
plcRedeemerHash :: RedeemerScript -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcSHA2_256 . BSL.pack . BA.unpack

{-# INLINABLE plcTxHash #-}
-- | Compute the hash of a redeemer script.
plcTxHash :: Tx.TxId -> TxHash
plcTxHash = TxHash . plcDigest . Tx.getTxId

{-# INLINABLE plcSHA2_256 #-}
-- | PLC-compatible SHA-256 hash of a hashable value
plcSHA2_256 :: Builtins.ByteString -> Builtins.ByteString
plcSHA2_256 = Hash.sha2

{-# INLINABLE plcSHA3_256 #-}
-- | PLC-compatible SHA3-256 hash of a hashable value
plcSHA3_256 :: Builtins.ByteString -> Builtins.ByteString
plcSHA3_256 = Hash.sha3

{-# INLINABLE plcDigest #-}
-- | Convert a `Digest SHA256` to a PLC `Hash`
plcDigest :: Digest SHA256 -> ByteString
plcDigest = BSL.pack . BA.unpack

{-# INLINABLE plcCurrencySymbol #-}
-- | The 'CurrencySymbol' of an 'Address'
plcCurrencySymbol :: Address -> CurrencySymbol
plcCurrencySymbol = Value.currencySymbol . plcDigest . getAddress

{-# INLINABLE txSignedBy #-}
-- | Check if a transaction was signed by the given public key.
txSignedBy :: PendingTx -> PubKey -> Bool
txSignedBy PendingTx{pendingTxSignatures=sigs, pendingTxHash=hash} k =
    let
        signedBy' :: Signature -> Bool
        signedBy' (Signature sig) =
            let
                PubKey (LedgerBytes pk) = k
                TxHash msg           = hash
            in verifySignature pk msg sig

        go :: [(PubKey, Signature)] -> Bool
        go l = case l of
                    (pk, sig):r ->
                        if k == pk
                        then  signedBy' sig
                              || traceH "matching pub key with invalid signature" (go r)
                        else go r
                    []  -> False
    in
        go sigs

{-# INLINABLE pubKeyOutput #-}
-- | Get the public key that locks the transaction output, if any.
pubKeyOutput :: PendingTxOut -> Maybe PubKey
pubKeyOutput o = case pendingTxOutData o of
    PubKeyTxOut pk -> Just pk
    _              -> Nothing

{-# INLINABLE ownHashes #-}
-- | Get the hashes of validator script and redeemer script that are
--   currently being validated
ownHashes :: PendingTx -> (ValidatorHash, RedeemerHash)
ownHashes (PendingTx _ _ _ _ i _ _ _) = case i of
    PendingTxIn _ (Just h) _ -> h
    _                        -> error ()

{-# INLINABLE ownHash #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash :: PendingTx -> ValidatorHash
ownHash p = fst (ownHashes p)

{-# INLINABLE fromSymbol #-}
-- | Convert a 'CurrencySymbol' to a 'ValidatorHash'
fromSymbol :: CurrencySymbol -> ValidatorHash
fromSymbol (CurrencySymbol s) = ValidatorHash s

{-# INLINABLE scriptOutputsAt #-}
-- | Get the list of 'PendingTxOut' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt :: ValidatorHash -> PendingTx -> [(DataScriptHash, Value)]
scriptOutputsAt h p =
    let flt ptxo =
            case pendingTxOutHashes ptxo of
                Just (h', ds) -> if h == h'
                                 then Just (ds, pendingTxOutValue ptxo)
                                 else Nothing
                Nothing -> Nothing
    in mapMaybe flt (pendingTxOutputs p)

{-# INLINABLE valueLockedBy #-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: PendingTx -> ValidatorHash -> Value
valueLockedBy ptx h =
    let outputs = map snd (scriptOutputsAt h ptx)
    in mconcat outputs

{-# INLINABLE pubKeyOutputsAt #-}
-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKey -> PendingTx -> [Value]
pubKeyOutputsAt pk p =
    let flt ptxo =
            case pendingTxOutData ptxo of
                PubKeyTxOut pk' ->
                    if pk' == pk
                    then Just (pendingTxOutValue ptxo)
                    else Nothing
                _ -> Nothing
    in mapMaybe flt (pendingTxOutputs p)

{-# INLINABLE valuePaidTo #-}
-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: PendingTx -> PubKey -> Value
valuePaidTo ptx pk = mconcat (pubKeyOutputsAt pk ptx)

{-# INLINABLE adaLockedBy #-}
-- | Get the total amount of 'Ada' locked by the given validator in this transaction.
adaLockedBy :: PendingTx -> ValidatorHash -> Ada
adaLockedBy ptx h = Ada.fromValue (valueLockedBy ptx h)

{-# INLINABLE signsTransaction #-}
-- | Check if the provided signature is the result of signing the pending
--   transaction (without witnesses) with the given public key.
signsTransaction :: Signature -> PubKey -> PendingTx -> Bool
signsTransaction (Signature sig) (PubKey (LedgerBytes pk)) p =
    verifySignature pk (let TxHash h = pendingTxHash p in h) sig

{-# INLINABLE valueSpent #-}
-- | Get the total value of inputs spent by this transaction.
valueSpent :: PendingTx -> Value
valueSpent p =
    let inputs' = map pendingTxInValue (pendingTxInputs p)
    in mconcat inputs'

{-# INLINABLE ownCurrencySymbol #-}
-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: PendingTx -> CurrencySymbol
ownCurrencySymbol p =
    let ValidatorHash h = fst (ownHashes p)
    in  Value.currencySymbol h

{-# INLINABLE spendsOutput #-}
-- | Check if the pending transaction spends a specific transaction output
--   (identified by the hash of a transaction and an index into that
--   transactions' outputs)
spendsOutput :: PendingTx -> TxHash -> Integer -> Bool
spendsOutput p h i =
    let spendsOutRef inp =
            let outRef = pendingTxInRef inp
            in h == pendingTxOutRefId outRef
                && i == pendingTxOutRefIdx outRef

    in any spendsOutRef (pendingTxInputs p)

{-# INLINABLE validatorScriptHash #-}
-- | The hash of a 'ValidatorScript'.
validatorScriptHash :: ValidatorScript -> ValidatorHash
validatorScriptHash =
    plcValidatorDigest
    . getAddress
    . scriptAddress

makeLift ''PendingTxOutType

makeLift ''PendingTxOut

makeLift ''PendingTxOutRef

makeLift ''PendingTxIn

makeLift ''PendingTx

makeLift ''OracleValue

makeLift ''ValidatorHash

makeLift ''DataScriptHash

makeLift ''RedeemerHash

makeLift ''TxHash
