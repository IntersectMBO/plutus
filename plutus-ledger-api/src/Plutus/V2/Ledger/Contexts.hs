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
module Plutus.V2.Ledger.Contexts
    (
    -- * Pending transactions and related types
      TxInfo(..)
    , ScriptContext(..)
    , ScriptPurpose(..)
    , TxOut(..)
    , TxOutRef(..)
    , TxInInfo(..)
    , findOwnInput
    , findDatum
    , findDatumHash
    , findTxInByTxOutRef
    , findContinuingOutputs
    , getContinuingOutputs
    -- ** Hashes (see note [Hashes in validator scripts])
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
    , valueProduced
    , ownCurrencySymbol
    , ownHashes
    , ownHash
    , fromSymbol
    ) where

import           Data.Text.Prettyprint.Doc   (Pretty (..), nest, vsep, (<+>))
import           GHC.Generics                (Generic)
import           PlutusTx
import           PlutusTx.AssocMap           hiding (filter, mapMaybe)
import           PlutusTx.Prelude            hiding (toList)

import           Plutus.V1.Ledger.Ada        (Ada)
import qualified Plutus.V1.Ledger.Ada        as Ada
import           Plutus.V1.Ledger.Address    (Address (..))
import           Plutus.V1.Ledger.Bytes      (LedgerBytes (..))
import           Plutus.V1.Ledger.Credential (Credential (..), StakingCredential)
import           Plutus.V1.Ledger.Crypto     (PubKey (..), PubKeyHash (..), Signature (..))
import           Plutus.V1.Ledger.DCert      (DCert (..))
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Time       (POSIXTimeRange)
import           Plutus.V1.Ledger.TxId
import           Plutus.V1.Ledger.Value      (CurrencySymbol, Value)
import qualified Prelude                     as Haskell

import           Plutus.V1.Ledger.Contexts   (ScriptPurpose (..), TxInInfo (..), TxOut (..), TxOutRef (..), fromSymbol,
                                              pubKeyOutput)

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data TxInfo = TxInfo
    { txInfoInputs      :: [TxInInfo] -- ^ Transaction inputs
    , txInfoOutputs     :: [TxOut] -- ^ Transaction outputs
    , txInfoFee         :: Value -- ^ The fee paid by this transaction.
    , txInfoMint        :: Value -- ^ The 'Value' minted by this transaction.
    , txInfoDCert       :: [DCert] -- ^ Digests of certificates included in this transaction
    , txInfoWdrl        :: Map StakingCredential Integer -- ^ Withdrawals
    , txInfoValidRange  :: POSIXTimeRange -- ^ The valid range for the transaction.
    , txInfoSignatories :: [PubKeyHash] -- ^ Signatures provided with the transaction, attested that they all signed the tx
    , txInfoRedeemers   :: Map ScriptPurpose Redeemer
    , txInfoData        :: Map DatumHash Datum
    , txInfoId          :: TxId
    -- ^ Hash of the pending transaction (excluding witnesses)
    } deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Eq TxInfo where
    {-# INLINABLE (==) #-}
    TxInfo i o f m c w r s rs d tid == TxInfo i' o' f' m' c' w' r' s' rs' d' tid' =
        i == i' && o == o' && f == f' && m == m' && c == c' && w == w' && r == r' && s == s' && rs == rs' && d == d' && tid == tid'

instance Pretty TxInfo where
    pretty TxInfo{txInfoInputs, txInfoOutputs, txInfoFee, txInfoMint, txInfoDCert, txInfoWdrl, txInfoValidRange, txInfoSignatories, txInfoRedeemers, txInfoData, txInfoId} =
        vsep
            [ "TxId:" <+> pretty txInfoId
            , "Inputs:" <+> pretty txInfoInputs
            , "Outputs:" <+> pretty txInfoOutputs
            , "Fee:" <+> pretty txInfoFee
            , "Value minted:" <+> pretty txInfoMint
            , "DCerts:" <+> pretty txInfoDCert
            , "Wdrl:" <+> pretty txInfoWdrl
            , "Valid range:" <+> pretty txInfoValidRange
            , "Signatories:" <+> pretty txInfoSignatories
            , "Redeemers:" <+> pretty txInfoRedeemers
            , "Datums:" <+> pretty txInfoData
            ]

data ScriptContext = ScriptContext{scriptContextTxInfo :: TxInfo, scriptContextPurpose :: ScriptPurpose }
    deriving stock (Generic, Haskell.Eq, Haskell.Show)

instance Eq ScriptContext where
    {-# INLINABLE (==) #-}
    ScriptContext info purpose == ScriptContext info' purpose' = info == info' && purpose == purpose'

instance Pretty ScriptContext where
    pretty ScriptContext{scriptContextTxInfo, scriptContextPurpose} =
        vsep
            [ "Purpose:" <+> pretty scriptContextPurpose
            , nest 2 $ vsep ["TxInfo:", pretty scriptContextTxInfo]
            ]

{-# INLINABLE findOwnInput #-}
-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs}, scriptContextPurpose=Spending txOutRef} =
    find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
findOwnInput _ = Nothing

{-# INLINABLE findDatum #-}
-- | Find the data corresponding to a data hash, if there is one
findDatum :: DatumHash -> TxInfo -> Maybe Datum
findDatum dsh TxInfo{txInfoData} = lookup dsh txInfoData

{-# INLINABLE findDatumHash #-}
-- | Find the hash of a datum, if it is part of the pending transaction's
--   hashes
findDatumHash :: Datum -> TxInfo -> Maybe DatumHash
findDatumHash ds TxInfo{txInfoData} = fst <$> find f (toList txInfoData)
    where
        f (_, ds') = ds' == ds

{-# INLINABLE findTxInByTxOutRef #-}
findTxInByTxOutRef :: TxOutRef -> TxInfo -> Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo{txInfoInputs} =
    find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == outRef) txInfoInputs

{-# INLINABLE findContinuingOutputs #-}
-- | Finds all the outputs that pay to the same script address that we are currently spending from, if any.
findContinuingOutputs :: ScriptContext -> [Integer]
findContinuingOutputs ctx | Just TxInInfo{txInInfoResolved=TxOut{txOutAddress}} <- findOwnInput ctx = findIndices (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
    where
        f addr TxOut{txOutAddress=otherAddress} = addr == otherAddress
findContinuingOutputs _ = traceError "Le" -- "Can't find any continuing outputs"

{-# INLINABLE getContinuingOutputs #-}
getContinuingOutputs :: ScriptContext -> [TxOut]
getContinuingOutputs ctx | Just TxInInfo{txInInfoResolved=TxOut{txOutAddress}} <- findOwnInput ctx = filter (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
    where
        f addr TxOut{txOutAddress=otherAddress} = addr == otherAddress
getContinuingOutputs _ = traceError "Lf" -- "Can't get any continuing outputs"

{-# INLINABLE txSignedBy #-}
-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy TxInfo{txInfoSignatories} k = case find ((==) k) txInfoSignatories of
    Just _  -> True
    Nothing -> False

{-# INLINABLE ownHashes #-}
-- | Get the validator and datum hashes of the output that is curently being validated
ownHashes :: ScriptContext -> (ValidatorHash, DatumHash)
ownHashes (findOwnInput -> Just TxInInfo{txInInfoResolved=TxOut{txOutAddress=Address (ScriptCredential s) _, txOutDatumHash=Just dh}}) = (s,dh)
ownHashes _ = traceError "Lg" -- "Can't get validator and datum hashes"

{-# INLINABLE ownHash #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash :: ScriptContext -> ValidatorHash
ownHash p = fst (ownHashes p)

{-# INLINABLE scriptOutputsAt #-}
-- | Get the list of 'TxOut' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt :: ValidatorHash -> TxInfo -> [(DatumHash, Value)]
scriptOutputsAt h p =
    let flt TxOut{txOutDatumHash=Just ds, txOutAddress=Address (ScriptCredential s) _, txOutValue} | s == h = Just (ds, txOutValue)
        flt _ = Nothing
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
    let flt TxOut{txOutAddress = Address (PubKeyCredential pk') _, txOutValue} | pk == pk' = Just txOutValue
        flt _                             = Nothing
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
signsTransaction (Signature sig) (PubKey (LedgerBytes pk)) TxInfo{txInfoId=TxId h} =
    verifySignature pk h sig

{-# INLINABLE valueSpent #-}
-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> Value
valueSpent = foldMap (txOutValue . txInInfoResolved) . txInfoInputs

{-# INLINABLE valueProduced #-}
-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> Value
valueProduced = foldMap txOutValue . txInfoOutputs

{-# INLINABLE ownCurrencySymbol #-}
-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> CurrencySymbol
ownCurrencySymbol ScriptContext{scriptContextPurpose=Minting cs} = cs
ownCurrencySymbol _                                              = traceError "Lh" -- "Can't get currency symbol of the current validator script"

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

makeLift ''TxInfo
makeIsDataIndexed ''TxInfo [('TxInfo,0)]

makeLift ''ScriptContext
makeIsDataIndexed ''ScriptContext [('ScriptContext,0)]
