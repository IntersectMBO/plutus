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
    , txInSignedBy
    -- ** Transactions
    , pubKeyOutput
    , scriptOutput
    , eqPubKey
    , eqDataScript
    , eqRedeemer
    , eqValidator
    , eqTx
    -- * Hashes
    , plcSHA2_256
    , plcSHA3_256
    ) where

import           Codec.Serialise              (Serialise, deserialiseOrFail, serialise)
import           Crypto.Hash                  (Digest, SHA256)
import           Data.Aeson                   (FromJSON, ToJSON (toJSON), withText)
import qualified Data.Aeson                   as JSON
import           Data.Bifunctor               (first)
import qualified Data.ByteString.Lazy.Hash    as Hash
import qualified Data.ByteString.Base64       as Base64
import qualified Data.ByteString.Lazy         as BSL
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Swagger.Internal.Schema (ToSchema (declareNamedSchema), paramSchemaToSchema, plain)
import qualified Data.Text.Encoding           as TE
import           GHC.Generics                 (Generic)
import           Language.Haskell.TH          (Q, TExp)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Builtins as Builtins
import           Ledger.Types                 (PubKey (..), Signature (..), Value (..), Slot(..))
import qualified Ledger.Types                 as Ledger

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

data PendingTxOutType
    = PubKeyTxOut PubKey -- ^ Pub key address
    | DataTxOut -- ^ The data script of the pending transaction output (see note [Script types in pending transactions])
    deriving (Generic)

-- | Output of a pending transaction.
data PendingTxOut = PendingTxOut
    { pendingTxOutValue  :: Value
    , pendingTxOutHashes :: Maybe (ValidatorHash, DataScriptHash) -- ^ Hashes of validator script and data script
    , pendingTxOutData   :: PendingTxOutType
    } deriving (Generic)

data PendingTxOutRef = PendingTxOutRef
    { pendingTxOutRefId  :: TxHash -- ^ Transaction whose outputs are consumed
    , pendingTxOutRefIdx :: Int -- ^ Index into the referenced transaction's list of outputs
    } deriving (Generic)

-- | Input of a pending transaction.
data PendingTxIn = PendingTxIn
    { pendingTxInRef       :: PendingTxOutRef
    , pendingTxInWitness   :: Either (ValidatorHash, RedeemerHash) Signature
    -- ^ Tx input witness, hashes for Script input, or signature for a PubKey
    , pendingTxInValue     :: Value -- ^ Value consumed by this txn input
    } deriving (Generic)

-- | A pending transaction as seen by validator scripts.
data PendingTx = PendingTx
    { pendingTxInputs      :: [PendingTxIn] -- ^ Transaction inputs
    , pendingTxOutputs     :: [PendingTxOut]
    , pendingTxFee         :: Value
    , pendingTxForge       :: Value
    , pendingTxSlot        :: Slot
    , pendingTxIn          :: PendingTxIn
    -- ^ PendingTxIn being validated
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

-- `OracleValue a` is the value observed at a time signed by
-- an oracle. See note [Oracles]
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

The mockchain code in [[Ledger.Types]] only deals with the hashes of(1)
and (2), and uses the [[Ledger.TxId]] and `Digest SHA256` types for
them.

In PLC validator scripts the situation is different: First, they need to work
with hashes of (1-4). Second, the `Digest SHA256` type is not available in PLC
- we have to represent all hashes as `ByteStrings`.

To ensure that we only compare hashes of the correct type inside a validator
script, we define a newtype for each of them, as well as functions for creating
them from the correct types in Haskell, and for comparing them (in
`Language.Plutus.Runtime.TH`).

-}
-- | PLC runtime representation of a `Digest SHA256`
newtype ValidatorHash =
    ValidatorHash BSL.ByteString
    deriving stock (Eq, Generic)
    deriving newtype (Serialise)

instance ToSchema ValidatorHash where
    declareNamedSchema _ = plain . paramSchemaToSchema $ (Proxy :: Proxy String)

instance ToJSON ValidatorHash where
    toJSON = JSON.String . TE.decodeUtf8 . Base64.encode . BSL.toStrict . serialise

instance FromJSON ValidatorHash where
    parseJSON = withText "ValidatorScript" $ \s -> do
        let ev = do
                eun64 <- Base64.decode . TE.encodeUtf8 $ s
                first show $ deserialiseOrFail $ BSL.fromStrict eun64
        case ev of
            Left e  -> fail e
            Right v -> pure v

newtype DataScriptHash =
    DataScriptHash BSL.ByteString
    deriving (Eq, Generic)

newtype RedeemerHash =
    RedeemerHash BSL.ByteString
    deriving (Eq, Generic)

newtype TxHash =
    TxHash BSL.ByteString
    deriving (Eq, Generic)

plcDataScriptHash :: Ledger.DataScript -> DataScriptHash
plcDataScriptHash = DataScriptHash . plcSHA2_256 . serialise

plcValidatorDigest :: Digest SHA256 -> ValidatorHash
plcValidatorDigest = ValidatorHash . plcDigest

plcRedeemerHash :: Ledger.RedeemerScript -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcSHA2_256 . serialise

plcTxHash :: Ledger.TxId -> TxHash
plcTxHash = TxHash . plcDigest . Ledger.getTxId

-- | PLC-compatible SHA-256 hash of a hashable value
plcSHA2_256 :: BSL.ByteString -> BSL.ByteString
plcSHA2_256 = Hash.sha2

-- | PLC-compatible SHA3-256 hash of a hashable value
plcSHA3_256 :: BSL.ByteString -> BSL.ByteString
plcSHA3_256 = Hash.sha3

-- | Convert a `Digest SHA256` to a PLC `Hash`
plcDigest :: Digest SHA256 -> BSL.ByteString
plcDigest = serialise

-- | Check if a transaction was signed by a public key
txSignedBy :: Q (TExp (PendingTx -> PubKey -> Bool))
txSignedBy = [||
    \(p :: PendingTx) (PubKey k) ->
        let
            PendingTx txins _ _ _ _ _ = p

            signedBy' :: Signature -> Bool
            signedBy' (Signature s) = s == k

            go :: [PendingTxIn] -> Bool
            go l = case l of
                        PendingTxIn _ (Right sig) _ : r -> if signedBy' sig then True else go r
                        _ : r -> go r
                        []  -> False
        in
            go txins
    ||]

-- | Check if the input of a pending transaction was signed by a public key
txInSignedBy :: Q (TExp (PendingTxIn -> PubKey -> Bool))
txInSignedBy = [||
    \(i :: PendingTxIn) (PubKey k) -> case i of
        PendingTxIn _ (Right (Signature sig)) _ -> sig == k
        _ -> False
    ||]

-- | Returns the public key that locks the transaction output
pubKeyOutput :: Q (TExp (PendingTxOut -> Maybe PubKey))
pubKeyOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ _ (PubKeyTxOut pk) -> Just pk
    _                                 -> Nothing ||]

-- | Returns the data script that is part of the pay-to-script transaction
--   output
scriptOutput :: Q (TExp (PendingTxOut -> Maybe (ValidatorHash, DataScriptHash)))
scriptOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ d DataTxOut -> d
    _                          -> Nothing ||]

-- | Equality of public keys
eqPubKey :: Q (TExp (PubKey -> PubKey -> Bool))
eqPubKey = [|| \(PubKey l) (PubKey r) -> l == r ||]

-- | Equality of data scripts
eqDataScript :: Q (TExp (DataScriptHash -> DataScriptHash -> Bool))
eqDataScript = [|| \(DataScriptHash l) (DataScriptHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of validator scripts
eqValidator :: Q (TExp (ValidatorHash -> ValidatorHash -> Bool))
eqValidator = [|| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of redeemer scripts
eqRedeemer :: Q (TExp (RedeemerHash -> RedeemerHash -> Bool))
eqRedeemer = [|| \(RedeemerHash l) (RedeemerHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of transactions
eqTx :: Q (TExp (TxHash -> TxHash -> Bool))
eqTx = [|| \(TxHash l) (TxHash r) -> Builtins.equalsByteString l r ||]



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
