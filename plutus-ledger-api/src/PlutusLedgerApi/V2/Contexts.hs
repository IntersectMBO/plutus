-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V2.Contexts
  ( -- * Pending transactions and related types
    TxInfo (..)
  , ScriptContext (..)
  , ScriptPurpose (..)
  , TxId (..)
  , TxOut (..)
  , TxOutRef (..)
  , TxInInfo (..)
  , findOwnInput
  , findDatum
  , findDatumHash
  , findTxInByTxOutRef
  , findContinuingOutputs
  , getContinuingOutputs

    -- * Validator functions
  , pubKeyOutputsAt
  , valuePaidTo
  , spendsOutput
  , txSignedBy
  , valueSpent
  , valueProduced
  , ownCurrencySymbol
  ) where

import PlutusTx.Prelude
import Prelude qualified as Haskell

import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Address (Address (..))
import PlutusLedgerApi.V1.Contexts (ScriptPurpose (..))
import PlutusLedgerApi.V1.Credential (Credential (..), StakingCredential)
import PlutusLedgerApi.V1.Crypto (PubKeyHash (..))
import PlutusLedgerApi.V1.DCert (DCert (..))
import PlutusLedgerApi.V1.Scripts (Datum, DatumHash, Redeemer)
import PlutusLedgerApi.V1.Time (POSIXTimeRange)
import PlutusLedgerApi.V1.Value (CurrencySymbol, Value)
import PlutusLedgerApi.V2.Tx (TxId (..), TxOut (..), TxOutRef (..))
import PlutusTx.AssocMap (Map, lookup, toList)
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)
import PlutusTx.Blueprint.Definition.Derive (definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Foldable qualified as F
import PlutusTx.Lift (makeLift)
import PlutusTx.List
import Prettyprinter (Pretty (..), nest, vsep, (<+>))

-- | An input of a pending transaction.
data TxInInfo = TxInInfo
  { txInInfoOutRef :: TxOutRef
  , txInInfoResolved :: TxOut
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

instance Eq TxInInfo where
  TxInInfo ref res == TxInInfo ref' res' = ref == ref' && res == res'

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data TxInfo = TxInfo
  { txInfoInputs :: [TxInInfo]
  -- ^ Transaction inputs; cannot be an empty list
  , txInfoReferenceInputs :: [TxInInfo]
  -- ^ /Added in V2:/ Transaction reference inputs
  , txInfoOutputs :: [TxOut]
  -- ^ Transaction outputs
  , txInfoFee :: Value
  -- ^ The fee paid by this transaction.
  , txInfoMint :: Value
  -- ^ The 'Value' minted by this transaction.
  , txInfoDCert :: [DCert]
  -- ^ Digests of certificates included in this transaction
  , txInfoWdrl :: Map StakingCredential Integer
  {-^ Withdrawals
  /V1->V2/: changed from assoc list to a 'PlutusTx.AssocMap' -}
  , txInfoValidRange :: POSIXTimeRange
  -- ^ The valid range for the transaction.
  , txInfoSignatories :: [PubKeyHash]
  -- ^ Signatures provided with the transaction, attested that they all signed the tx
  , txInfoRedeemers :: Map ScriptPurpose Redeemer
  -- ^ /Added in V2:/ a table of redeemers attached to the transaction
  , txInfoData :: Map DatumHash Datum
  {-^ The lookup table of datums attached to the transaction
  /V1->V2/: changed from assoc list to a 'PlutusTx.AssocMap' -}
  , txInfoId :: TxId
  -- ^ Hash of the pending transaction body (i.e. transaction excluding witnesses)
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

instance Pretty TxInfo where
  pretty TxInfo {txInfoInputs, txInfoReferenceInputs, txInfoOutputs, txInfoFee, txInfoMint, txInfoDCert, txInfoWdrl, txInfoValidRange, txInfoSignatories, txInfoRedeemers, txInfoData, txInfoId} =
    vsep
      [ "TxId:" <+> pretty txInfoId
      , "Inputs:" <+> pretty txInfoInputs
      , "Reference inputs:" <+> pretty txInfoReferenceInputs
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

-- | The context that the currently-executing script can access.
data ScriptContext = ScriptContext
  { scriptContextTxInfo :: TxInfo
  -- ^ information about the transaction the currently-executing script is included in
  , scriptContextPurpose :: ScriptPurpose
  -- ^ the purpose of the currently-executing script
  }
  deriving stock (Generic, Haskell.Eq, Haskell.Show)

instance Pretty ScriptContext where
  pretty ScriptContext {scriptContextTxInfo, scriptContextPurpose} =
    vsep
      [ "Purpose:" <+> pretty scriptContextPurpose
      , nest 2 $ vsep ["TxInfo:", pretty scriptContextTxInfo]
      ]

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext {scriptContextTxInfo = TxInfo {txInfoInputs}, scriptContextPurpose = Spending txOutRef} =
  find (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
findOwnInput _ = Nothing
{-# INLINEABLE findOwnInput #-}

-- | Find the data corresponding to a data hash, if there is one
findDatum :: DatumHash -> TxInfo -> Maybe Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData
{-# INLINEABLE findDatum #-}

{-| Find the hash of a datum, if it is part of the pending transaction's
hashes -}
findDatumHash :: Datum -> TxInfo -> Maybe DatumHash
findDatumHash ds TxInfo {txInfoData} = fst <$> find f (toList txInfoData)
  where
    f (_, ds') = ds' == ds
{-# INLINEABLE findDatumHash #-}

{-| Given a UTXO reference and a transaction (`TxInfo`), resolve it to one of the transaction's inputs (`TxInInfo`).
Note: this only searches the true transaction inputs and not the referenced transaction inputs. -}
findTxInByTxOutRef :: TxOutRef -> TxInfo -> Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  find (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef == outRef) txInfoInputs
{-# INLINEABLE findTxInByTxOutRef #-}

-- | Find the indices of all the outputs that pay to the same script address we are currently spending from, if any.
findContinuingOutputs :: ScriptContext -> [Integer]
findContinuingOutputs ctx | Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx = findIndices (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
  where
    f addr TxOut {txOutAddress = otherAddress} = addr == otherAddress
findContinuingOutputs _ = traceError "Le" -- "Can't find any continuing outputs"
{-# INLINEABLE findContinuingOutputs #-}

-- | Get all the outputs that pay to the same script address we are currently spending from, if any.
getContinuingOutputs :: ScriptContext -> [TxOut]
getContinuingOutputs ctx | Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx = filter (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
  where
    f addr TxOut {txOutAddress = otherAddress} = addr == otherAddress
getContinuingOutputs _ = traceError "Lf" -- "Can't get any continuing outputs"
{-# INLINEABLE getContinuingOutputs #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy TxInfo {txInfoSignatories} k = case find ((==) k) txInfoSignatories of
  Just _ -> True
  Nothing -> False
{-# INLINEABLE txSignedBy #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKeyHash -> TxInfo -> [Value]
pubKeyOutputsAt pk p =
  let flt TxOut {txOutAddress = Address (PubKeyCredential pk') _, txOutValue} | pk == pk' = Just txOutValue
      flt _ = Nothing
   in mapMaybe flt (txInfoOutputs p)
{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> PubKeyHash -> Value
valuePaidTo ptx pkh = mconcat (pubKeyOutputsAt pkh ptx)
{-# INLINEABLE valuePaidTo #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> Value
valueSpent = F.foldMap (txOutValue . txInInfoResolved) . txInfoInputs
{-# INLINEABLE valueSpent #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> Value
valueProduced = F.foldMap txOutValue . txInfoOutputs
{-# INLINEABLE valueProduced #-}

-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextPurpose = Minting cs} = cs
ownCurrencySymbol _ = traceError "Lh" -- "Can't get currency symbol of the current validator script"
{-# INLINEABLE ownCurrencySymbol #-}

{-| Check if the pending transaction spends a specific transaction output
(identified by the hash of a transaction and an index into that
transactions' outputs) -}
spendsOutput :: TxInfo -> TxId -> Integer -> Bool
spendsOutput p h i =
  let spendsOutRef inp =
        let outRef = txInInfoOutRef inp
         in h
              == txOutRefId outRef
              && i
              == txOutRefIdx outRef
   in any spendsOutRef (txInfoInputs p)
{-# INLINEABLE spendsOutput #-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''TxInInfo)
$(makeLift ''TxInfo)
$(makeLift ''ScriptContext)

$(makeIsDataSchemaIndexed ''TxInInfo [('TxInInfo, 0)])
$(makeIsDataSchemaIndexed ''TxInfo [('TxInfo, 0)])
$(makeIsDataSchemaIndexed ''ScriptContext [('ScriptContext, 0)])
