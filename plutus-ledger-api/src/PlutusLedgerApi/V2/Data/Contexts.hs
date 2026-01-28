{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
-- needed for asData pattern synonyms
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V2.Data.Contexts
  ( -- * Pending transactions and related types
    TxInfo
  , pattern TxInfo
  , txInfoInputs
  , txInfoReferenceInputs
  , txInfoOutputs
  , txInfoFee
  , txInfoMint
  , txInfoDCert
  , txInfoWdrl
  , txInfoValidRange
  , txInfoSignatories
  , txInfoRedeemers
  , txInfoData
  , txInfoId
  , ScriptContext
  , pattern ScriptContext
  , scriptContextTxInfo
  , scriptContextPurpose
  , ScriptPurpose
  , pattern Minting
  , pattern Spending
  , pattern Rewarding
  , pattern Certifying
  , TxId (..)
  , TxOut
  , pattern TxOut
  , txOutAddress
  , txOutValue
  , txOutDatum
  , txOutReferenceScript
  , TxOutRef
  , pattern TxOutRef
  , txOutRefId
  , txOutRefIdx
  , TxInInfo
  , pattern TxInInfo
  , txInInfoOutRef
  , txInInfoResolved
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

import GHC.Generics (Generic)
import PlutusTx
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins.Internal qualified as Builtins
import PlutusTx.Data.AssocMap hiding (any)
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude
import Prettyprinter (Pretty (..), nest, vsep, (<+>))

import PlutusLedgerApi.V1.Crypto (PubKeyHash (..))
import PlutusLedgerApi.V1.Data.Address (pattern Address)
import PlutusLedgerApi.V1.Data.Contexts
  ( ScriptPurpose
  , pattern Certifying
  , pattern Minting
  , pattern Rewarding
  , pattern Spending
  )
import PlutusLedgerApi.V1.Data.Credential (StakingCredential, pattern PubKeyCredential)
import PlutusLedgerApi.V1.Data.DCert (DCert)
import PlutusLedgerApi.V1.Data.Time (POSIXTimeRange)
import PlutusLedgerApi.V1.Data.Value (CurrencySymbol, Value)
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V2.Data.Tx
  ( TxId (..)
  , TxOut
  , TxOutRef
  , txOutAddress
  , txOutDatum
  , txOutRefId
  , txOutRefIdx
  , txOutReferenceScript
  , txOutValue
  , pattern TxOut
  , pattern TxOutRef
  )

import Prelude qualified as Haskell

-- | An input of a pending transaction.
PlutusTx.asData
  [d|
    data TxInInfo = TxInInfo
      { txInInfoOutRef :: TxOutRef
      , txInInfoResolved :: TxOut
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

deriveEq ''TxInInfo
makeLift ''TxInInfo

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

{-| A pending transaction. This is the view as seen by validator scripts,
so some details are stripped out. -}
PlutusTx.asData
  [d|
    data TxInfo = TxInfo
      { txInfoInputs :: List TxInInfo
      , -- \^ Transaction inputs; cannot be an empty list
        txInfoReferenceInputs :: List TxInInfo
      , -- \^ /Added in V2:/ Transaction reference inputs
        txInfoOutputs :: List TxOut
      , -- \^ Transaction outputs
        txInfoFee :: Value
      , -- \^ The fee paid by this transaction.
        txInfoMint :: Value
      , -- \^ The 'Value' minted by this transaction.
        txInfoDCert :: List DCert
      , -- \^ Digests of certificates included in this transaction
        txInfoWdrl :: Map StakingCredential Integer
      , -- \^ Withdrawals
        -- /V1->V2/: changed from assoc list to a 'PlutusTx.AssocMap'
        txInfoValidRange :: POSIXTimeRange
      , -- \^ The valid range for the transaction.
        txInfoSignatories :: List PubKeyHash
      , -- \^ Signatures provided with the transaction, attested that they all signed the tx
        txInfoRedeemers :: Map ScriptPurpose Redeemer
      , -- \^ /Added in V2:/ a table of redeemers attached to the transaction
        txInfoData :: Map DatumHash Datum
      , -- \^ The lookup table of datums attached to the transaction
        -- /V1->V2/: changed from assoc list to a 'PlutusTx.AssocMap'
        txInfoId :: TxId
      }
      -- \^ Hash of the pending transaction body (i.e. transaction excluding witnesses)

      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

makeLift ''TxInfo

instance Pretty TxInfo where
  pretty
    TxInfo
      { txInfoInputs
      , txInfoReferenceInputs
      , txInfoOutputs
      , txInfoFee
      , txInfoMint
      , txInfoDCert
      , txInfoWdrl
      , txInfoValidRange
      , txInfoSignatories
      , txInfoRedeemers
      , txInfoData
      , txInfoId
      } =
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
PlutusTx.asData
  [d|
    data ScriptContext = ScriptContext
      { scriptContextTxInfo :: TxInfo
      , -- \^ information about the transaction the currently-executing script is included in
        scriptContextPurpose :: ScriptPurpose
      }
      -- \^ the purpose of the currently-executing script

      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

makeLift ''ScriptContext

instance Pretty ScriptContext where
  pretty ScriptContext {scriptContextTxInfo, scriptContextPurpose} =
    vsep
      [ "Purpose:" <+> pretty scriptContextPurpose
      , nest 2 $ vsep ["TxInfo:", pretty scriptContextTxInfo]
      ]

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput
  ScriptContext
    { scriptContextTxInfo = TxInfo {txInfoInputs}
    , scriptContextPurpose = Spending txOutRef
    } =
    Data.List.find
      (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef == txOutRef)
      txInfoInputs
findOwnInput _ = Nothing
{-# INLINEABLE findOwnInput #-}

-- | Find the data corresponding to a data hash, if there is one
findDatum :: DatumHash -> TxInfo -> Maybe Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData
{-# INLINEABLE findDatum #-}

{-| Find the hash of a datum, if it is part of the pending transaction's
hashes -}
findDatumHash :: Datum -> TxInfo -> Maybe DatumHash
findDatumHash ds TxInfo {txInfoData} = do
  getHash <$> BuiltinList.find matchDatum (toBuiltinList txInfoData)
  where
    getHash = unsafeFromBuiltinData . Builtins.fst
    matchDatum pair = Builtins.snd pair == getDatum ds
{-# INLINEABLE findDatumHash #-}

{-| Given a UTXO reference and a transaction (`TxInfo`), resolve it to one
of the transaction's inputs (`TxInInfo`).
Note: this only searches the true transaction inputs and not the referenced
transaction inputs. -}
findTxInByTxOutRef :: TxOutRef -> TxInfo -> Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  Data.List.find
    (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef == outRef)
    txInfoInputs
{-# INLINEABLE findTxInByTxOutRef #-}

{-| Find the indices of all the outputs that pay to the same script address
we are currently spending from, if any. -}
findContinuingOutputs :: ScriptContext -> List Integer
findContinuingOutputs ctx
  | Just
      TxInInfo
        { txInInfoResolved = TxOut {txOutAddress = addr}
        } <-
      findOwnInput ctx =
      Data.List.findIndices (f addr) (txInfoOutputs $ scriptContextTxInfo ctx)
  where
    f addr TxOut {txOutAddress = otherAddress} = addr == otherAddress
findContinuingOutputs _ = traceError "Le" -- "Can't find any continuing outputs"
{-# INLINEABLE findContinuingOutputs #-}

{-| Get all the outputs that pay to the same script address we are currently spending
from, if any. -}
getContinuingOutputs :: ScriptContext -> List TxOut
getContinuingOutputs ctx
  | Just
      TxInInfo
        { txInInfoResolved = TxOut {txOutAddress = addr}
        } <-
      findOwnInput ctx =
      Data.List.filter (f addr) (txInfoOutputs $ scriptContextTxInfo ctx)
  where
    f addr TxOut {txOutAddress = otherAddress} = addr == otherAddress
getContinuingOutputs _ = traceError "Lf" -- "Can't get any continuing outputs"
{-# INLINEABLE getContinuingOutputs #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy TxInfo {txInfoSignatories} k =
  case Data.List.find ((==) k) txInfoSignatories of
    Just _ -> True
    Nothing -> False
{-# INLINEABLE txSignedBy #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKeyHash -> TxInfo -> List Value
pubKeyOutputsAt pk p =
  let flt
        TxOut
          { txOutAddress = Address (PubKeyCredential pk') _
          , txOutValue = txOutVal
          } | pk == pk' = Just txOutVal
      flt _ = Nothing
   in Data.List.mapMaybe flt (txInfoOutputs p)
{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> PubKeyHash -> Value
valuePaidTo ptx pkh = Data.List.mconcat (pubKeyOutputsAt pkh ptx)
{-# INLINEABLE valuePaidTo #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> Value
valueSpent = Data.List.foldMap (txOutValue . txInInfoResolved) . txInfoInputs
{-# INLINEABLE valueSpent #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> Value
valueProduced = Data.List.foldMap txOutValue . txInfoOutputs
{-# INLINEABLE valueProduced #-}

-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextPurpose = Minting cs} = cs
ownCurrencySymbol _ =
  traceError "Lh" -- "Can't get currency symbol of the current validator script"
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
   in Data.List.any spendsOutRef (txInfoInputs p)
{-# INLINEABLE spendsOutput #-}
