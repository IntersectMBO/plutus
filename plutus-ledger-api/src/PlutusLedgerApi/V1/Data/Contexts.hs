-- editorconfig-checker-disable-file
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusLedgerApi.V1.Data.Contexts
    (
    -- * Pending transactions and related types
      TxInfo(..)
    , ScriptContext(..)
    , ScriptPurpose(..)
    , TxId (..)
    , TxOut(..)
    , TxOutRef(..)
    , TxInInfo(..)
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
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude
import Prettyprinter
import Prettyprinter.Extras

import PlutusLedgerApi.V1.Crypto (PubKeyHash (..))
import PlutusLedgerApi.V1.Data.Address (pattern Address)
import PlutusLedgerApi.V1.Data.Credential (StakingCredential, pattern PubKeyCredential)
import PlutusLedgerApi.V1.Data.Tx (TxId (..), TxOut (..), TxOutRef (..))
import PlutusLedgerApi.V1.Data.Value (CurrencySymbol (..), Value)
import PlutusLedgerApi.V1.DCert (DCert (..))
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V1.Time (POSIXTimeRange)
import Prelude qualified as Haskell

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
    { txInInfoOutRef   :: TxOutRef
    , txInInfoResolved :: TxOut
    } deriving stock (Generic, Haskell.Show, Haskell.Eq)

makeLift ''TxInInfo
makeIsDataIndexed ''TxInInfo [('TxInInfo,0)]

instance Eq TxInInfo where
    TxInInfo ref res == TxInInfo ref' res' = ref == ref' && res == res'

instance Pretty TxInInfo where
    pretty TxInInfo{txInInfoOutRef, txInInfoResolved} =
        pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | Purpose of the script that is currently running
data ScriptPurpose
    = Minting CurrencySymbol
    | Spending TxOutRef
    | Rewarding StakingCredential
    | Certifying DCert
    deriving stock (Generic, Haskell.Show, Haskell.Eq)
    deriving Pretty via (PrettyShow ScriptPurpose)

makeLift ''ScriptPurpose
makeIsDataIndexed ''ScriptPurpose
    [ ('Minting,0)
    , ('Spending,1)
    , ('Rewarding,2)
    , ('Certifying,3)
    ]

instance Eq ScriptPurpose where
    {-# INLINABLE (==) #-}
    Minting cs == Minting cs'           = cs == cs'
    Spending ref == Spending ref'       = ref == ref'
    Rewarding sc == Rewarding sc'       = sc == sc'
    Certifying cert == Certifying cert' = cert == cert'
    _ == _                              = False

-- | A pending transaction. This is the view as seen by validator scripts, so some details are stripped out.
data TxInfo = TxInfo
    { txInfoInputs      :: List TxInInfo -- ^ Transaction inputs; cannot be an empty list
    , txInfoOutputs     :: List TxOut -- ^ Transaction outputs
    , txInfoFee         :: Value -- ^ The fee paid by this transaction.
    , txInfoMint        :: Value -- ^ The 'Value' minted by this transaction.
    , txInfoDCert       :: List DCert -- ^ Digests of certificates included in this transaction
    -- TODO: is this a map? is this a list?
    , txInfoWdrl        :: [(StakingCredential, Integer)] -- ^ Withdrawals
    , txInfoValidRange  :: POSIXTimeRange -- ^ The valid range for the transaction.
    , txInfoSignatories :: List PubKeyHash -- ^ Signatures provided with the transaction, attested that they all signed the tx
    -- TODO: is this a map? is this a list?
    , txInfoData        :: [(DatumHash, Datum)] -- ^ The lookup table of datums attached to the transaction
    , txInfoId          :: TxId  -- ^ Hash of the pending transaction body (i.e. transaction excluding witnesses)
    } deriving stock (Generic, Haskell.Show, Haskell.Eq)

makeLift ''TxInfo
makeIsDataIndexed ''TxInfo [('TxInfo,0)]

instance Eq TxInfo where
    {-# INLINABLE (==) #-}
    TxInfo i o f m c w r s d tid == TxInfo i' o' f' m' c' w' r' s' d' tid' =
        i == i' && o == o' && f == f' && m == m' && c == c' && w == w' && r == r' && s == s' && d == d' && tid == tid'

instance Pretty TxInfo where
    pretty TxInfo{txInfoInputs, txInfoOutputs, txInfoFee, txInfoMint, txInfoDCert, txInfoWdrl, txInfoValidRange, txInfoSignatories, txInfoData, txInfoId} =
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
            , "Datums:" <+> pretty txInfoData
            ]

-- | The context that the currently-executing script can access.
data ScriptContext = ScriptContext
    { scriptContextTxInfo  :: TxInfo -- ^ information about the transaction the currently-executing script is included in
    , scriptContextPurpose :: ScriptPurpose -- ^ the purpose of the currently-executing script
    }
    deriving stock (Generic, Haskell.Eq, Haskell.Show)

makeLift ''ScriptContext
makeIsDataIndexed ''ScriptContext [('ScriptContext,0)]

instance Eq ScriptContext where
    {-# INLINABLE (==) #-}
    ScriptContext info purpose == ScriptContext info' purpose' = info == info' && purpose == purpose'

instance Pretty ScriptContext where
    pretty ScriptContext{scriptContextTxInfo, scriptContextPurpose} =
        vsep
            [ "Purpose:" <+> pretty scriptContextPurpose
            , nest 2 $ vsep ["TxInfo:", pretty scriptContextTxInfo]
            ]

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs}, scriptContextPurpose=Spending txOutRef} =
    Data.List.find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
findOwnInput _ = Nothing
{-# INLINABLE findOwnInput #-}

-- | Find the data corresponding to a data hash, if there is one
findDatum :: DatumHash -> TxInfo -> Maybe Datum
findDatum dsh TxInfo{txInfoData} = snd <$> find f txInfoData
    where
        f (dsh', _) = dsh' == dsh
{-# INLINABLE findDatum #-}

-- | Find the hash of a datum, if it is part of the pending transaction's
--   hashes
findDatumHash :: Datum -> TxInfo -> Maybe DatumHash
findDatumHash ds TxInfo{txInfoData} = fst <$> find f txInfoData
    where
        f (_, ds') = ds' == ds
{-# INLINABLE findDatumHash #-}

-- | Given a UTXO reference and a transaction (`TxInfo`), resolve it to one of the transaction's inputs (`TxInInfo`).
findTxInByTxOutRef :: TxOutRef -> TxInfo -> Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo{txInfoInputs} =
    Data.List.find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == outRef) txInfoInputs
{-# INLINABLE findTxInByTxOutRef #-}

-- | Finds all the outputs that pay to the same script address that we are currently spending from, if any.
findContinuingOutputs :: ScriptContext -> List Integer
findContinuingOutputs ctx | Just TxInInfo{txInInfoResolved=TxOut{txOutAddress}} <- findOwnInput ctx = Data.List.findIndices (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
    where
        f addr TxOut{txOutAddress=otherAddress} = addr == otherAddress
findContinuingOutputs _ = traceError "Le" -- "Can't find any continuing outputs"
{-# INLINABLE findContinuingOutputs #-}

-- | Get all the outputs that pay to the same script address we are currently spending from, if any.
getContinuingOutputs :: ScriptContext -> List TxOut
getContinuingOutputs ctx | Just TxInInfo{txInInfoResolved=TxOut{txOutAddress}} <- findOwnInput ctx = Data.List.filter (f txOutAddress) (txInfoOutputs $ scriptContextTxInfo ctx)
    where
        f addr TxOut{txOutAddress=otherAddress} = addr == otherAddress
getContinuingOutputs _ = traceError "Lf" -- "Can't get any continuing outputs"
{-# INLINABLE getContinuingOutputs #-}

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

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy TxInfo{txInfoSignatories} k = case Data.List.find ((==) k) txInfoSignatories of
    Just _  -> True
    Nothing -> False
{-# INLINABLE txSignedBy #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: PubKeyHash -> TxInfo -> List Value
pubKeyOutputsAt pk p =
    let flt TxOut{txOutAddress = Address (PubKeyCredential pk') _, txOutValue} | pk == pk' = Just txOutValue
        flt _                             = Nothing
    in Data.List.mapMaybe flt (txInfoOutputs p)
{-# INLINABLE pubKeyOutputsAt #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> PubKeyHash -> Value
valuePaidTo ptx pkh = Data.List.mconcat (pubKeyOutputsAt pkh ptx)
{-# INLINABLE valuePaidTo #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> Value
valueSpent = Data.List.foldMap (txOutValue . txInInfoResolved) . txInfoInputs
{-# INLINABLE valueSpent #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> Value
valueProduced = Data.List.foldMap txOutValue . txInfoOutputs
{-# INLINABLE valueProduced #-}

-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> CurrencySymbol
ownCurrencySymbol ScriptContext{scriptContextPurpose=Minting cs} = cs
ownCurrencySymbol _                                              = traceError "Lh" -- "Can't get currency symbol of the current validator script"
{-# INLINABLE ownCurrencySymbol #-}

{- | Check if the pending transaction spends a specific transaction output
(identified by the hash of a transaction and an index into that
transactions' outputs)
-}
spendsOutput :: TxInfo -> TxId -> Integer -> Bool
spendsOutput p h i =
    let spendsOutRef inp =
            let outRef = txInInfoOutRef inp
            in h == txOutRefId outRef
                && i == txOutRefIdx outRef
    in Data.List.any spendsOutRef (txInfoInputs p)
{-# INLINABLE spendsOutput #-}
