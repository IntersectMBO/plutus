{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC   -O0 #-}
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
    -- * Oracles
    , OracleValue(..)
    -- * Validator functions
    -- ** Signatures
    , txSignedBy
    -- ** Transactions
    , pubKeyOutput
    , scriptOutput
    , eqPubKey
    , eqDataScript
    , eqRedeemer
    , eqValidator
    , eqTx
    , adaLockedBy
    , ownHash
    , signsTransaction
    , txHash
    -- * Hashes
    , plcSHA2_256
    , plcSHA3_256
    ) where

import           Codec.Serialise              (Serialise)
import           Crypto.Hash                  (Digest, SHA256)
import           Data.Aeson                   (FromJSON, ToJSON (toJSON))
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Extras            as JSON
import qualified Data.ByteArray               as BA
import qualified Data.ByteString.Lazy.Hash    as Hash
import qualified Data.ByteString.Lazy         as BSL
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Swagger.Internal.Schema (ToSchema (declareNamedSchema), paramSchemaToSchema, plain)
import           GHC.Generics                 (Generic)
import           Language.Haskell.TH          (Q, TExp)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Builtins   as Builtins
import qualified Language.PlutusTx.Prelude    as P

import           Ledger.Ada                   (Ada)
import qualified Ledger.Ada.TH                as Ada
import           Ledger.Crypto                (PubKey (..), Signature (..))
import           Ledger.Scripts
import           Ledger.Slot                  (Slot, SlotRange)
import qualified Ledger.TxId                  as Tx
import           Ledger.Value                 (Value)
import           KeyBytes                     (KeyBytes(..))

-- Ignore newtype warnings related to `Oracle` and `Signed` because it causes
-- problems with the plugin
--
-- TODO: Remove annotation once `newtype Oracle = (...)` works
{-# ANN module "HLint: ignore Use newtype instead of data" #-}

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
    , pendingTxOutRefIdx :: Int -- ^ Index into the referenced transaction's list of outputs.
    } deriving (Generic)

-- | An input of a pending transaction.
data PendingTxIn = PendingTxIn
    { pendingTxInRef       :: PendingTxOutRef
    , pendingTxInWitness   :: Maybe (ValidatorHash, RedeemerHash)
    -- ^ Tx input witness, hashes for Script input, or signature for a PubKey
    , pendingTxInValue     :: Value -- ^ Value consumed by this txn input
    } deriving (Generic)

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data PendingTx = PendingTx
    { pendingTxInputs      :: [PendingTxIn] -- ^ Transaction inputs
    , pendingTxOutputs     :: [PendingTxOut] -- ^ Transaction outputs
    , pendingTxFee         :: Ada -- ^ The fee paid by this transaction.
    , pendingTxForge       :: Value -- ^ The 'Value' forged by this transaction.
    , pendingTxIn          :: PendingTxIn -- ^ The 'PendingTxIn' being validated against currently.
    , pendingTxValidRange  :: SlotRange -- ^ The valid range for the transaction.    
    , pendingTxSignatures  :: [(PubKey, Signature)]
    -- ^ Signatures provided with the transaction
    , pendingTxHash        :: TxHash
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
    ValidatorHash (Builtins.SizedByteString 32)
    deriving stock (Eq, Generic)
    deriving newtype (Serialise)

instance Show ValidatorHash where
    show = show . JSON.encodeSerialise

instance ToSchema ValidatorHash where
    declareNamedSchema _ = plain . paramSchemaToSchema $ (Proxy :: Proxy String)

instance ToJSON ValidatorHash where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON ValidatorHash where
    parseJSON = JSON.decodeSerialise

-- | Script runtime representation of a @Digest SHA256@.
newtype DataScriptHash =
    DataScriptHash (Builtins.SizedByteString 32)
    deriving (Eq, Generic)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash (Builtins.SizedByteString 32)
    deriving (Eq, Generic)

-- | Script runtime representation of a @Digest SHA256@.
newtype TxHash =
    TxHash (Builtins.SizedByteString 32)
    deriving (Eq, Generic)

plcDataScriptHash :: DataScript -> DataScriptHash
plcDataScriptHash = DataScriptHash . plcSHA2_256 . Builtins.SizedByteString . BSL.pack . BA.unpack

-- | Compute the hash of a validator script.
plcValidatorDigest :: Digest SHA256 -> ValidatorHash
plcValidatorDigest = ValidatorHash . Builtins.SizedByteString . BSL.pack . BA.unpack

plcRedeemerHash :: RedeemerScript -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcSHA2_256 . Builtins.SizedByteString . BSL.pack . BA.unpack

-- | Compute the hash of a redeemer script.
plcTxHash :: Tx.TxId -> TxHash
plcTxHash = TxHash . plcDigest . Tx.getTxId

-- | PLC-compatible SHA-256 hash of a hashable value
plcSHA2_256 :: Builtins.ByteString -> Builtins.ByteString
plcSHA2_256 = Builtins.SizedByteString . Hash.sha2 . Builtins.unSizedByteString

-- | PLC-compatible SHA3-256 hash of a hashable value
plcSHA3_256 :: Builtins.ByteString -> Builtins.ByteString
plcSHA3_256 = Builtins.SizedByteString . Hash.sha3 . Builtins.unSizedByteString

-- | Convert a `Digest SHA256` to a PLC `Hash`
plcDigest :: Digest SHA256 -> P.SizedByteString 32
plcDigest = P.SizedByteString . BSL.pack . BA.unpack

-- | Check if two public keys are equal.
eqPubKey :: Q (TExp (PubKey -> PubKey -> Bool))
eqPubKey = [|| 
    \(PubKey (KeyBytes l)) (PubKey (KeyBytes r)) -> $$(P.equalsByteString) l r
    ||]
    
-- | Check if a transaction was signed by the given public key.
txSignedBy :: Q (TExp (PendingTx -> PubKey -> Bool))
txSignedBy = [||
    \(p :: PendingTx) k ->
        let
            PendingTx _ _ _ _ _ _ sigs hsh = p

            signedBy' :: Signature -> Bool
            signedBy' (Signature sig) =
                let
                    PubKey (KeyBytes pk) = k
                    TxHash msg           = hsh
                in $$(P.verifySignature) pk msg sig

            go :: [(PubKey, Signature)] -> Bool
            go l = case l of
                        (pk, sig):r ->
                            if $$(eqPubKey) k pk
                            then if signedBy' sig
                                 then True
                                 else $$(P.traceH) "matching pub key with invalid signature" (go r)
                            else go r
                        []  -> False
        in
            go sigs
    ||]

-- | Get the 'TxHash' of a 'PendingTx'.
txHash :: Q (TExp (PendingTx -> TxHash))
txHash = [|| \(PendingTx _ _ _ _ _ _ _ h) -> h||]

-- | Get the public key that locks the transaction output, if any.
pubKeyOutput :: Q (TExp (PendingTxOut -> Maybe PubKey))
pubKeyOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ _ (PubKeyTxOut pk) -> Just pk
    _                                 -> Nothing ||]

-- | Get the validator and data script hashes from a pay-to-script transaction
--   output, if there are any.
scriptOutput :: Q (TExp (PendingTxOut -> Maybe (ValidatorHash, DataScriptHash)))
scriptOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ d DataTxOut -> d
    _                          -> Nothing ||]

-- | Check if two data script hashes are equal.
eqDataScript :: Q (TExp (DataScriptHash -> DataScriptHash -> Bool))
eqDataScript = [|| \(DataScriptHash l) (DataScriptHash r) -> Builtins.equalsByteString l r ||]

-- | Check if two validator script hashes are equal.
eqValidator :: Q (TExp (ValidatorHash -> ValidatorHash -> Bool))
eqValidator = [|| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r ||]

-- | Check if two redeemer script hashes are equal.
eqRedeemer :: Q (TExp (RedeemerHash -> RedeemerHash -> Bool))
eqRedeemer = [|| \(RedeemerHash l) (RedeemerHash r) -> Builtins.equalsByteString l r ||]

-- | Check if two transaction hashes are equal.
eqTx :: Q (TExp (TxHash -> TxHash -> Bool))
eqTx = [|| \(TxHash l) (TxHash r) -> Builtins.equalsByteString l r ||]

-- | Get the hash of the validator script that is currently being validated.
ownHash :: Q (TExp (PendingTx -> ValidatorHash))
ownHash = [|| \(PendingTx _ _ _ _ i _ _ _) -> let PendingTxIn _ (Just (h, _)) _ = i in h ||]

-- | Get the total amount of 'Ada' locked by the given validator in this transaction.
adaLockedBy :: Q (TExp (PendingTx -> ValidatorHash -> Ada))
adaLockedBy = [|| \(PendingTx _ outs _ _ _ _ _ _) h ->
    let

        go :: [PendingTxOut] -> Ada
        go c = case c of
            [] -> $$(Ada.zero)
            (PendingTxOut vl hashes _):xs ->
                case hashes of
                    Nothing -> go xs
                    Just  (h', _) -> if $$(eqValidator) h h'
                                     then $$(Ada.plus) ($$(Ada.fromValue) vl) (go xs)
                                     else go xs

    in go outs
      ||]

-- | Check if the provided signature is the result of signing the pending
--   transaction (without witnesses) with the given public key.
signsTransaction :: Q (TExp (Signature -> PubKey -> PendingTx -> Bool))
signsTransaction = [|| 
    \(Signature sig) (PubKey (KeyBytes pk)) (p :: PendingTx) -> 
        $$(P.verifySignature) pk (let TxHash h = $$(txHash) p in h) sig
    ||]

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
