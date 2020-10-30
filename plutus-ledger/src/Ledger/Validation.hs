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
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Validation
    (
    -- * Pending transactions and related types
      TxInfo(..)
    , ValidatorCtx (..)
    , PolicyCtx (..)
    , TxOut(..)
    , TxOutRef(..)
    , TxOutType(..)
    , TxInInfo(..)
    , TxOutInfo
    , findOwnInput
    , findDatum
    , findDatumHash
    , findTxInByTxOutRef
    , findContinuingOutputs
    , getContinuingOutputs
    -- ** Hashes (see note [Hashes in validator scripts])
    , scriptCurrencySymbol
    , pubKeyHash
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

import           GHC.Generics               (Generic)
import           Language.PlutusTx
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Prelude

import           Ledger.Ada                 (Ada)
import qualified Ledger.Ada                 as Ada
import           Ledger.Address             (Address (..), scriptHashAddress)
import           Ledger.Crypto              (PubKey (..), PubKeyHash (..), Signature (..), pubKeyHash)
import           Ledger.Scripts
import           Ledger.Slot                (SlotRange)
import           Ledger.Tx                  (TxOut (..), TxOutRef (..), TxOutType (..))
import           Ledger.TxId
import           Ledger.Value               (CurrencySymbol (..), Value)
import qualified Ledger.Value               as Value
import           LedgerBytes                (LedgerBytes (..))

{- Note [Script types in pending transactions]
To validate a transaction, we have to evaluate the validation script of each of
the transaction's inputs. The validation script sees the data of the
transaction output it validates, and the redeemer of the transaction input of
the transaction that consumes it.
In addition, the validation script also needs information on the transaction as
a whole (not just the output-input pair it is concerned with). This information
is provided by the `TxInfo` type. A `TxInfo` contains the hashes of
redeemer and data scripts of all of its inputs and outputs.
-}

-- | An input of a pending transaction.
data TxInInfo = TxInInfo
    { txInInfoOutRef  :: TxOutRef
    , txInInfoWitness :: Maybe (ValidatorHash, RedeemerHash, DatumHash)
    -- ^ Tx input witness, hashes for Script input
    , txInInfoValue   :: Value -- ^ Value consumed by this txn input
    } deriving (Generic)

type TxOutInfo = TxOut

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data TxInfo = TxInfo
    { txInfoInputs       :: [TxInInfo] -- ^ Transaction inputs
    , txInfoOutputs      :: [TxOutInfo] -- ^ Transaction outputs
    , txInfoFee          :: Value -- ^ The fee paid by this transaction.
    , txInfoForge        :: Value -- ^ The 'Value' forged by this transaction.
    , txInfoValidRange   :: SlotRange -- ^ The valid range for the transaction.
    , txInfoForgeScripts :: [MonetaryPolicyHash]
    , txInfoSignatories  :: [PubKeyHash]
    -- ^ Signatures provided with the transaction
    , txInfoData         :: [(DatumHash, Datum)]
    , txInfoId           :: TxId
    -- ^ Hash of the pending transaction (excluding witnesses)
    } deriving (Generic)

data ValidatorCtx = ValidatorCtx { valCtxTxInfo :: TxInfo, valCtxInput :: Integer }

data PolicyCtx = PolicyCtx { policyCtxTxInfo :: TxInfo, policyCtxPolicy :: MonetaryPolicyHash }

{-# INLINABLE findOwnInput #-}
-- | Find the input currently being validated.
findOwnInput :: ValidatorCtx -> TxInInfo
findOwnInput ValidatorCtx{valCtxTxInfo=TxInfo{txInfoInputs}, valCtxInput} = txInfoInputs !! valCtxInput

{-# INLINABLE findDatum #-}
-- | Find the data corresponding to a data hash, if there is one
findDatum :: DatumHash -> TxInfo -> Maybe Datum
findDatum dsh TxInfo{txInfoData} = snd <$> find f txInfoData
    where
        f (dsh', _) = dsh' == dsh

{-# INLINABLE findDatumHash #-}
-- | Find the hash of a datum, if it is part of the pending transaction's
--   hashes
findDatumHash :: Datum -> TxInfo -> Maybe DatumHash
findDatumHash ds TxInfo{txInfoData} = fst <$> find f txInfoData
    where
        f (_, ds') = ds' == ds

{-# INLINABLE findTxInByTxOutRef #-}
findTxInByTxOutRef :: TxOutRef -> TxInfo -> Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo{txInfoInputs} =
    listToMaybe
    $ filter (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == outRef) txInfoInputs


{-# INLINABLE findContinuingOutputs #-}
-- | Finds all the outputs that pay to the same script address that we are currently spending from, if any.
findContinuingOutputs :: ValidatorCtx -> [Integer]
findContinuingOutputs ctx@ValidatorCtx{valCtxTxInfo=TxInfo{txInfoOutputs}} | TxInInfo{txInInfoWitness=Just (inpHsh, _, _)} <- findOwnInput ctx = findIndices (f inpHsh) txInfoOutputs
    where
        f inpHsh TxOut{txOutType=PayToScript{}, txOutAddress} = txOutAddress == scriptHashAddress inpHsh
        f _ _                                                 = False
findContinuingOutputs _ = Builtins.error()

{-# INLINABLE getContinuingOutputs #-}
getContinuingOutputs :: ValidatorCtx -> [TxOutInfo]
getContinuingOutputs ctx@ValidatorCtx{valCtxTxInfo=TxInfo{txInfoOutputs}} | TxInInfo{txInInfoWitness=Just (inpHsh, _, _)} <- findOwnInput ctx = filter (f inpHsh) txInfoOutputs
    where
        f inpHsh TxOut{txOutType=PayToScript{}, txOutAddress} = txOutAddress == scriptHashAddress inpHsh
        f _ _                                                 = False
getContinuingOutputs _ = Builtins.error()

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
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy TxInfo{txInfoSignatories} k = case find ((==) k) txInfoSignatories of
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
ownHashes :: ValidatorCtx -> (ValidatorHash, RedeemerHash, DatumHash)
ownHashes (findOwnInput -> TxInInfo{txInInfoWitness=Just witness}) = witness
ownHashes _                                                        = Builtins.error ()

{-# INLINABLE ownHash #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash :: ValidatorCtx -> ValidatorHash
ownHash p = let (vh, _, _) = ownHashes p in vh

{-# INLINABLE fromSymbol #-}
-- | Convert a 'CurrencySymbol' to a 'ValidatorHash'
fromSymbol :: CurrencySymbol -> ValidatorHash
fromSymbol (CurrencySymbol s) = ValidatorHash s

{-# INLINABLE scriptOutputsAt #-}
-- | Get the list of 'TxOutInfo' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt :: ValidatorHash -> TxInfo -> [(DatumHash, Value)]
scriptOutputsAt h p =
    let flt TxOut{txOutType, txOutAddress, txOutValue} =
            case txOutType of
                PayToScript ds | scriptHashAddress h == txOutAddress -> Just (ds, txOutValue)
                _                                                    -> Nothing
    in mapMaybe flt (txInfoOutputs p)

{-# INLINABLE valueLockedBy #-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: TxInfo -> ValidatorHash -> Value
valueLockedBy ptx h =
    let outputs = map snd (scriptOutputsAt h ptx)
    in mconcat outputs

{-# INLINABLE pubKeyOutputsAt #-}
-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKeyHash -> TxInfo -> [Value]
pubKeyOutputsAt pk p =
    let flt TxOut{txOutAddress, txOutValue} =
            case txOutAddress of
                PubKeyAddress pk' | pk' == pk -> Just txOutValue
                _                             -> Nothing
    in mapMaybe flt (txInfoOutputs p)

{-# INLINABLE valuePaidTo #-}
-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> PubKeyHash -> Value
valuePaidTo ptx pkh = mconcat (pubKeyOutputsAt pkh ptx)

{-# INLINABLE adaLockedBy #-}
-- | Get the total amount of 'Ada' locked by the given validator in this transaction.
adaLockedBy :: TxInfo -> ValidatorHash -> Ada
adaLockedBy ptx h = Ada.fromValue (valueLockedBy ptx h)

{-# INLINABLE signsTransaction #-}
-- | Check if the provided signature is the result of signing the pending
--   transaction (without witnesses) with the given public key.
signsTransaction :: Signature -> PubKey -> TxInfo -> Bool
signsTransaction (Signature sig) (PubKey (LedgerBytes pk)) (TxInfo{txInfoId=TxId h}) =
    verifySignature pk h sig

{-# INLINABLE valueSpent #-}
-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> Value
valueSpent p =
    let inputs' = map txInInfoValue (txInfoInputs p)
    in mconcat inputs'

{-# INLINABLE ownCurrencySymbol #-}
-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: PolicyCtx -> CurrencySymbol
ownCurrencySymbol p =
    let MonetaryPolicyHash h = policyCtxPolicy p
    in  Value.currencySymbol h

{-# INLINABLE spendsOutput #-}
-- | Check if the pending transaction spends a specific transaction output
--   (identified by the hash of a transaction and an index into that
--   transactions' outputs)
spendsOutput :: TxInfo -> TxId -> Integer -> Bool
spendsOutput p h i =
    let spendsOutRef inp =
            let outRef = txInInfoOutRef inp
            in h == txOutRefId outRef
                && i == txOutRefIdx outRef

    in any spendsOutRef (txInfoInputs p)

makeLift ''TxInInfo
makeIsData ''TxInInfo

makeLift ''TxInfo
makeIsData ''TxInfo

makeLift ''ValidatorCtx
makeIsData ''ValidatorCtx

makeLift ''PolicyCtx
makeIsData ''PolicyCtx
