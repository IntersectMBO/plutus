{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Validation
    (
    -- * Pending transactions and related types
      PendingTx'(..)
    , PendingTx
    , PendingTxMPS
    , TxOut(..)
    , TxOutRef(..)
    , TxOutType(..)
    , toLedgerTxIn
    , PendingTxIn'(..)
    , PendingTxIn
    , PendingTxInScript
    , findData
    , findDataHash
    , findTxInByTxOutRef
    , findContinuingOutputs
    , getContinuingOutputs
    -- ** Hashes (see note [Hashes in validator scripts])
    , scriptCurrencySymbol
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
    , fromSymbol
    ) where

import           GHC.Generics              (Generic)
import           Language.PlutusTx
import           Language.PlutusTx.Lift    (makeLift)
import           Language.PlutusTx.Prelude
import qualified Prelude                   as Haskell

import           Ledger.Ada                (Ada)
import qualified Ledger.Ada                as Ada
import           Ledger.Address            (Address (..), scriptHashAddress)
import           Ledger.Crypto             (PubKey (..), PubKeyHash (..), Signature (..))
import           Ledger.Scripts
import           Ledger.Slot               (SlotRange)
import           Ledger.Tx                 (TxOut (..), TxOutRef (..), TxOutType (..))
import           Ledger.TxId
import           Ledger.Value              (CurrencySymbol (..), Value)
import qualified Ledger.Value              as Value
import           LedgerBytes               (LedgerBytes (..))

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

-- | An input of a pending transaction, parameterised by its witness.
data PendingTxIn' w = PendingTxIn
    { pendingTxInRef     :: TxOutRef
    , pendingTxInWitness :: w
    -- ^ Tx input witness, hashes for Script input, or signature for a PubKey
    , pendingTxInValue   :: Value -- ^ Value consumed by this txn input
    } deriving (Generic, Haskell.Functor)

instance Functor PendingTxIn' where
    fmap f p = p{pendingTxInWitness = f (pendingTxInWitness p) }

type PendingTxIn = PendingTxIn' (Maybe (ValidatorHash, RedeemerHash, DataValueHash))
type PendingTxInScript = PendingTxIn' (ValidatorHash, RedeemerHash, DataValueHash)

toLedgerTxIn :: PendingTxInScript -> PendingTxIn
toLedgerTxIn = fmap Just

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data PendingTx' i = PendingTx
    { pendingTxInputs       :: [PendingTxIn] -- ^ Transaction inputs
    , pendingTxOutputs      :: [TxOut] -- ^ Transaction outputs
    , pendingTxFee          :: Value -- ^ The fee paid by this transaction.
    , pendingTxForge        :: Value -- ^ The 'Value' forged by this transaction.
    , pendingTxItem         :: i -- ^ The item being validated against currently.
    , pendingTxValidRange   :: SlotRange -- ^ The valid range for the transaction.
    , pendingTxForgeScripts :: [MonetaryPolicyHash]
    , pendingTxSignatories  :: [PubKeyHash]
    -- ^ Signatures provided with the transaction
    , pendingTxData         :: [(DataValueHash, DataValue)]
    , pendingTxId           :: TxId
    -- ^ Hash of the pending transaction (excluding witnesses)
    } deriving (Generic, Haskell.Functor)

instance Functor PendingTx' where
    fmap f p = p { pendingTxItem = f (pendingTxItem p) }

type PendingTx = PendingTx' PendingTxInScript

type PendingTxMPS = PendingTx' MonetaryPolicyHash

{-# INLINABLE findData #-}
-- | Find the data corresponding to a data hash, if there is one
findData :: DataValueHash -> PendingTx' a -> Maybe DataValue
findData dsh PendingTx{pendingTxData=datas} = snd <$> find f datas
    where
        f (dsh', _) = dsh' == dsh

{-# INLINABLE findDataHash #-}
-- | Find the hash of a data value, if it is part of the pending transaction's
--   hashes
findDataHash :: DataValue -> PendingTx -> Maybe DataValueHash
findDataHash ds PendingTx{pendingTxData=datas} = fst <$> find f datas
    where
        f (_, ds') = ds' == ds

{-# INLINABLE findTxInByTxOutRef #-}
findTxInByTxOutRef :: TxOutRef -> PendingTx -> Maybe PendingTxIn
findTxInByTxOutRef outRef PendingTx{pendingTxInputs} =
    listToMaybe
    $ filter (\PendingTxIn{pendingTxInRef} -> pendingTxInRef == outRef) pendingTxInputs


{-# INLINABLE findContinuingOutputs #-}
-- | Finds all the outputs that pay to the same script address that we are currently spending from, if any.
findContinuingOutputs :: PendingTx -> [Integer]
findContinuingOutputs PendingTx{pendingTxItem=PendingTxIn{pendingTxInWitness=(inpHsh, _, _)}, pendingTxOutputs=outs} = findIndices f outs
    where
        f TxOut{txOutType=PayToScript{}, txOutAddress} = txOutAddress == scriptHashAddress inpHsh
        f _                                            = False

{-# INLINABLE getContinuingOutputs #-}
getContinuingOutputs :: PendingTx -> [TxOut]
getContinuingOutputs PendingTx{pendingTxItem=PendingTxIn{pendingTxInWitness=(inpHsh, _, _)}, pendingTxOutputs=outs} = filter f outs
    where
        f TxOut{txOutType=PayToScript{}, txOutAddress} = txOutAddress == scriptHashAddress inpHsh
        f _                                            = False

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

{-# INLINABLE scriptCurrencySymbol #-}
-- | The 'CurrencySymbol' of a 'MonetaryPolicy'
scriptCurrencySymbol :: MonetaryPolicy -> CurrencySymbol
scriptCurrencySymbol scrpt = let (MonetaryPolicyHash hsh) = monetaryPolicyHash scrpt in Value.currencySymbol hsh

{-# INLINABLE txSignedBy #-}
-- | Check if a transaction was signed by the given public key.
txSignedBy :: PendingTx' a -> PubKeyHash -> Bool
txSignedBy PendingTx{pendingTxSignatories=sigs} k = case find ((==) k) sigs of
    Just _  -> True
    Nothing -> False

{-# INLINABLE pubKeyOutput #-}
-- | Get the public key hash that locks the transaction output, if any.
pubKeyOutput :: TxOut -> Maybe PubKeyHash
pubKeyOutput TxOut{txOutAddress} = case txOutAddress of
    PubKeyAddress pk -> Just pk
    _                -> Nothing

{-# INLINABLE ownHashes #-}
-- | Get the hashes of validator script and redeemer script that are
--   currently being validated
ownHashes :: PendingTx -> (ValidatorHash, RedeemerHash, DataValueHash)
ownHashes PendingTx{pendingTxItem=PendingTxIn{pendingTxInWitness=h}} = h

{-# INLINABLE ownHash #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash :: PendingTx -> ValidatorHash
ownHash p = let (vh, _, _) = ownHashes p in vh

{-# INLINABLE fromSymbol #-}
-- | Convert a 'CurrencySymbol' to a 'ValidatorHash'
fromSymbol :: CurrencySymbol -> ValidatorHash
fromSymbol (CurrencySymbol s) = ValidatorHash s

{-# INLINABLE scriptOutputsAt #-}
-- | Get the list of 'PendingTxOut' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt :: ValidatorHash -> PendingTx' a -> [(DataValueHash, Value)]
scriptOutputsAt h p =
    let flt TxOut{txOutType, txOutAddress, txOutValue} =
            case txOutType of
                PayToScript ds | scriptHashAddress h == txOutAddress -> Just (ds, txOutValue)
                _                                                    -> Nothing
    in mapMaybe flt (pendingTxOutputs p)

{-# INLINABLE valueLockedBy #-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: PendingTx' a -> ValidatorHash -> Value
valueLockedBy ptx h =
    let outputs = map snd (scriptOutputsAt h ptx)
    in mconcat outputs

{-# INLINABLE pubKeyOutputsAt #-}
-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKeyHash -> PendingTx' a -> [Value]
pubKeyOutputsAt pk p =
    let flt TxOut{txOutAddress, txOutValue} =
            case txOutAddress of
                PubKeyAddress pk' | pk' == pk -> Just txOutValue
                _                             -> Nothing
    in mapMaybe flt (pendingTxOutputs p)

{-# INLINABLE valuePaidTo #-}
-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: PendingTx' a-> PubKeyHash -> Value
valuePaidTo ptx pkh = mconcat (pubKeyOutputsAt pkh ptx)

{-# INLINABLE adaLockedBy #-}
-- | Get the total amount of 'Ada' locked by the given validator in this transaction.
adaLockedBy :: PendingTx' a -> ValidatorHash -> Ada
adaLockedBy ptx h = Ada.fromValue (valueLockedBy ptx h)

{-# INLINABLE signsTransaction #-}
-- | Check if the provided signature is the result of signing the pending
--   transaction (without witnesses) with the given public key.
signsTransaction :: Signature -> PubKey -> PendingTx' a -> Bool
signsTransaction (Signature sig) (PubKey (LedgerBytes pk)) p =
    verifySignature pk (let TxId h = pendingTxId p in h) sig

{-# INLINABLE valueSpent #-}
-- | Get the total value of inputs spent by this transaction.
valueSpent :: PendingTx' a -> Value
valueSpent p =
    let inputs' = map pendingTxInValue (pendingTxInputs p)
    in mconcat inputs'

{-# INLINABLE ownCurrencySymbol #-}
-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: PendingTxMPS -> CurrencySymbol
ownCurrencySymbol p =
    let MonetaryPolicyHash h = pendingTxItem p
    in  Value.currencySymbol h

{-# INLINABLE spendsOutput #-}
-- | Check if the pending transaction spends a specific transaction output
--   (identified by the hash of a transaction and an index into that
--   transactions' outputs)
spendsOutput :: PendingTx' a -> TxId -> Integer -> Bool
spendsOutput p h i =
    let spendsOutRef inp =
            let outRef = pendingTxInRef inp
            in h == txOutRefId outRef
                && i == txOutRefIdx outRef

    in any spendsOutRef (pendingTxInputs p)

makeLift ''PendingTxIn'
makeIsData ''PendingTxIn'

makeLift ''PendingTx'
makeIsData ''PendingTx'
