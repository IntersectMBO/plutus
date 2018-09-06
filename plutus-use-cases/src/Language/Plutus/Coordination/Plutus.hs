-- | This is a mock of (parts of) the Plutus API
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE LambdaCase     #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin #-}
-- | A model of the types involved in transactions, and of the wallet API.
module Language.Plutus.Coordination.Plutus (-- * Transactions and related types
                Address
              , PubKey(..)
              , KeyPair
              , pubKey
              , Value
              , Tx(..)
              , TxIn(..)
              , TxOut(..)
              , mkAddress
              , TxOutRef(..)
              , standardTxFee
              , txOutValue
              , txOutDataScript
              , txOutValidatorScriptHash
              -- * API operations
              , TxM
              , Hash
              , hash
              , Redeemer
              , Validator
              , DataScript
              , PlutusTx(..)
              , unitPLC
              , BlockHeight
              , PendingTx(..)
              , submitTransaction
              , assert
              , lookupMyKeyPair
              , lookupMyPubKey
              , createPayment
              , txInSign
              , Range(..)
              , EventTrigger(..)
              , Signed(..)
              , OracleValue(..)
              ) where

import           Control.Applicative              (Alternative (..))
import           Control.Monad.State              (State)
import           Control.Monad.Trans.Maybe        (MaybeT (..))
import           Language.Plutus.CoreToPLC.Plugin (PlcCode, plc)

newtype Signed a = Signed (PubKey, a)

{- Note [Oracles]

I'm not sure how oracles are going to work eventually, so I'm going to use this
definition for now:

* Oracles are identified by their public key
* An oracle can produce "observations", which are values annotated with time
  (block height). These observations are signed by the oracle.
* To use an oracle value inside a validator script, it has to be provided as the
  data script of the transaction that consumes the output locked by the
  validator script.

An example of this can be found in the
Language.Plutus.Coordination.Contracts.Swap.swapValidator script.

-}

-- `OracleValue a` is the value observed at a time signed by
-- an oracle.
newtype OracleValue a = OracleValue (Signed (BlockHeight, a))

-- | Cardano address
--
newtype Address = Address Int
    deriving (Eq, Ord, Show, Read)

-- | Ada value
--
type Value = Int

newtype Hash = Hash Int
    deriving (Eq, Ord, Show, Read)

hash :: a -> Hash
hash _ = Hash 10

-- | Public key
--
data PubKey = PubKey

-- | Public key pair (no lift instance, because we never ought to put it into a
--   transaction)
--
data KeyPair

data TxState

-- | Transaction monad for coordination layer computations; provides access to
-- the blockchain
--
type TxM a = MaybeT (State TxState) a

-- | Submit the given transaction to the blockchain
submitTransaction :: Tx -> TxM [TxOutRef]
submitTransaction = const empty

-- | Verify that a condition is true.
assert :: Bool -> TxM ()
assert = const empty

-- | Get the users's public key. Part of the wallet interface
lookupMyPubKey :: TxM PubKey
lookupMyPubKey = pubKey <$> lookupMyKeyPair

-- | Extract the public key from a key pair.
pubKey :: KeyPair -> PubKey
pubKey = const PubKey

-- | Part of the wallet interface
lookupMyKeyPair :: TxM KeyPair
lookupMyKeyPair = empty

-- | Create an input that spends the given value (part of the wallet interface)
--
createPayment :: Value -> TxM TxIn
createPayment = const empty

-- | A UTxO transaction specification
--
--   In this model the number of inputs and outputs of a transaction is
--   limited to a maximum of 2. This will change when we can translate recursive
--   types in the core-to-plc plugin.
data Tx = Tx
          { txInputs  :: Either TxIn (TxIn, TxIn) -- TODO: Change to [TxIn]
          , txOutputs :: Either (TxOut Int) (TxOut Int, TxOut Int) -- TODO: Change to [TxOut Int]
          }

-- | UTxO input
--
data TxIn = TxIn
            { txInOutRef     :: !TxOutRef -- ^ Output consumed by this transaction
            , txInValidator  :: !Hash -- ^ Validator script of the transaction output (TODO: This should be the actual script, not the hash; Change to Validator when recursive types are supported - same for redeemer and data scripts.)
            , txInRedeemer   :: !Hash -- ^ Redeemer
            , txInDataScript :: !Hash -- ^ Data script (TODO: Not sure if we should have 1 data script per transaction or 1 data script per transaction input)
            }

-- | Construct an input that can spend the given output (assuming it was payed
--   to an address in our wallet.) Part of the wallet interface
--
txInSign :: TxOutRef -> Validator -> Redeemer -> DataScript -> KeyPair -> TxIn
txInSign to v r d _ = TxIn to (hash v) (hash r) (hash d)

-- | Reference to an unspent output
--   See https://github.com/input-output-hk/plutus-prototype/tree/master/docs/extended-utxo#extension-to-transaction-outputs
--
data TxOutRef =
  TxOutRef
  {
     txOutRefValue          :: !Value -- We assume this is added by the library. TODO: In cardano-sl this is a "ValueDistribution" (map of keys to values)
   , txOutRefValidatorHash  :: !Hash -- Hash of validator script. The validator script has to be submitted by the consumer of the outputs referenced by this TxOutRef.
   , txOutRefDataScriptHash :: !Hash -- Hash of data script used by the creator of the transaction.
  }

type BlockHeight = Int

-- | Information about a pending transaction used by validator scripts.
--   See https://github.com/input-output-hk/plutus-prototype/tree/master/docs/extended-utxo#blockchain-state-available-to-validator-scripts
data PendingTx = PendingTx {
      pendingTxBlockHeight :: !BlockHeight -- ^ Block height exl. current transaction
    , pendingTxHash        :: !Hash -- ^ Hash of the transaction that is being validated
    , pendingTxTransaction :: !Tx
    }

-- | UTxO output
--
data TxOut a = TxOutPubKey  !Value !PubKey
           | TxOutScript  !Value !Hash !a

-- | An address in cardano is a hash of the information in `TxOut`
mkAddress :: TxOut a -> Address
mkAddress = const (Address 5)

txOutValue :: TxOut a -> Value
txOutValue = \case
    TxOutPubKey v _ -> v
    TxOutScript v _ _ -> v

txOutDataScript :: TxOut a -> Maybe a
txOutDataScript = \case
    TxOutScript _ _ r -> Just r
    _ -> Nothing

txOutValidatorScriptHash :: TxOut a -> Maybe Hash
txOutValidatorScriptHash = \case
    TxOutScript _ h _ -> Just h
    _ -> Nothing

-- | PlutusTx code
--
newtype PlutusTx = PlutusTx { getPlutusTx :: PlcCode }

-- | A PLC script containing the `()` value, to be used as a placeholder for
--   data and redeemer scripts where we don't need them.
unitPLC :: PlutusTx
unitPLC = PlutusTx $ plc ()

-- | Some sort of transaction fee (we need to determine that more dynamically)
--
standardTxFee :: Value
standardTxFee = 1

data Range a =
    Interval a a -- inclusive-exclusive
    | GEQ a
    | LT a

-- | Event triggers the Plutus client can register with the wallet.
data EventTrigger =
    BlockHeightRange !(Range BlockHeight) -- ^ True when the block height is within the range
    | FundsAtAddress [Address] !(Range Value) -- ^ True when the (unspent) funds at a list of addresses are within the range
    | And EventTrigger EventTrigger -- ^ True when both triggers are true
    | Or EventTrigger EventTrigger -- ^ True when at least one trigger is true
    | PAlways -- ^ Always true
    | PNever -- ^ Never true

-- | Validator scripts expect two scripts and information about the current
--   txn. In the future this will be written in Plutus (with the help of TH)
--   and its return type will be `a` instead of `Maybe a`.
--   See https://github.com/input-output-hk/plutus-prototype/tree/master/docs/extended-utxo#extension-to-validator-scripts
--
type Validator = PlutusTx

type Redeemer = PlutusTx

type DataScript = PlutusTx

{- Note [Transaction Templates]

Transaction templates are currently missing from this mock API and will be
added in the future.

Transaction templates differ from transactions in at least two ways:

1) They do not include a transaction fee (that is, the sum of their input
   values equals the sum of their output values)
2) Part of their input value is not attributed to an address

To turn a template into a transaction, the wallet
1) Adjusts either the input values or the output value to ensure that the
   difference between inputs and outputs matches the transaction fee.
2) Expands the inputs to account for the missing funds (via coin selection).

These two steps depend on each other because the transaction fee is a
function of the size of the transaction including its
inputs.

-}
