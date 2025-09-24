{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.V3.Data.ScriptContexts where

import PlutusLedgerApi.Data.V1 qualified as PlutusTx
import PlutusLedgerApi.Data.V3 (PubKeyHash (..), Redeemer (..), ScriptContext, TxId (..), TxInfo,
                                TxOut, always, emptyMintValue, mintValueMinted,
                                pattern CertifyingScript, pattern MintingScript,
                                pattern NoOutputDatum, pattern ProposingScript,
                                pattern RewardingScript, pattern ScriptContext,
                                pattern SpendingScript, pattern TxInfo, pattern TxOut,
                                pattern TxOutRef, pattern VotingScript, txInInfoOutRef,
                                txInfoCurrentTreasuryAmount, txInfoData, txInfoFee, txInfoId,
                                txInfoInputs, txInfoMint, txInfoOutputs, txInfoProposalProcedures,
                                txInfoRedeemers, txInfoReferenceInputs, txInfoSignatories,
                                txInfoTreasuryDonation, txInfoTxCerts, txInfoValidRange,
                                txInfoVotes, txInfoWdrl, txOutAddress, txOutDatum,
                                txOutReferenceScript, txOutValue)
import PlutusLedgerApi.V1.Data.Address
import PlutusLedgerApi.V1.Data.Value
import PlutusLedgerApi.V3.Data.MintValue (MintValue (..))
import PlutusTx qualified
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List qualified as List
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as PlutusTx

{-| A very crude deterministic generator for 'ScriptContext's with size
approximately proportional to the input integer.
-}
mkScriptContext :: Integer -> ScriptContext
mkScriptContext i =
  ScriptContext
    (mkTxInfo i)
    (Redeemer (PlutusTx.toBuiltinData (1 :: Integer)))
    (SpendingScript (TxOutRef (TxId "") 0) Nothing)

mkTxInfo :: Integer -> TxInfo
mkTxInfo i =
  TxInfo
    { txInfoInputs = mempty
    , txInfoReferenceInputs = mempty
    , txInfoOutputs = List.map mkTxOut (List.fromSOP ([1 .. i] :: [Integer]))
    , txInfoFee = 10000
    , txInfoMint = emptyMintValue
    , txInfoTxCerts = mempty
    , txInfoWdrl = Map.empty
    , txInfoValidRange = always
    , txInfoSignatories = mempty
    , txInfoRedeemers = Map.empty
    , txInfoData = Map.empty
    , txInfoId = TxId ""
    , txInfoVotes = Map.empty
    , txInfoProposalProcedures = mempty
    , txInfoCurrentTreasuryAmount = Nothing
    , txInfoTreasuryDonation = Nothing
    }

mkTxOut :: Integer -> TxOut
mkTxOut i =
  TxOut
    { txOutAddress = pubKeyHashAddress (PubKeyHash "")
    , txOutValue = mkValue i
    , txOutDatum = NoOutputDatum
    , txOutReferenceScript = Nothing
    }

mkValue :: Integer -> Value
mkValue i = assetClassValue (assetClass adaSymbol adaToken) i

mkMintingScriptContext :: Integer -> ScriptContext
mkMintingScriptContext i =
  ScriptContext
    (mkMintingTxInfo i)
    (Redeemer (PlutusTx.toBuiltinData (1 :: Integer)))
    (MintingScript . CurrencySymbol $ toByteString i)

mkMintingTxInfo :: Integer -> TxInfo
mkMintingTxInfo i =
  TxInfo
    { txInfoInputs = mempty
    , txInfoReferenceInputs = mempty
    , txInfoOutputs = List.map mkTxOut (List.fromSOP ([1 .. i] :: [Integer]))
    , txInfoFee = 10000
    , txInfoMint = mkMintValue i
    , txInfoTxCerts = mempty
    , txInfoWdrl = Map.empty
    , txInfoValidRange = always
    , txInfoSignatories = mempty
    , txInfoRedeemers = Map.empty
    , txInfoData = Map.empty
    , txInfoId = TxId ""
    , txInfoVotes = Map.empty
    , txInfoProposalProcedures = mempty
    , txInfoCurrentTreasuryAmount = Nothing
    , txInfoTreasuryDonation = Nothing
    }

mkMintValue :: Integer -> MintValue
mkMintValue n = listToMintValue
  [(CurrencySymbol (toByteString i), [(TokenName (toByteString i), i)])
    | i <- [0..n]]

toByteString :: Integer -> PlutusTx.BuiltinByteString
toByteString i =
  foldr
    (\_ -> PlutusTx.consByteString 48)
    PlutusTx.emptyByteString
    [0..i]

listToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listToValue = Value . Map.unsafeFromSOPList . map (fmap Map.unsafeFromSOPList)

listToMintValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> MintValue
listToMintValue = UnsafeMintValue . getValue . listToValue

-- This example decodes the script context (which is O(size-of-context) work), and then also
-- does some work that's roughly proportional to the size of the script context (counting the
-- outputs). This should be a somewhat realistic example where a reasonable chunk of work is
-- done in addition to decoding.
checkScriptContext1 :: PlutusTx.BuiltinData -> ()
checkScriptContext1 d =
  -- Bang pattern to ensure this is forced, probably not necesssary
  -- since we do use it later
  let !sc = PlutusTx.unsafeFromBuiltinData d
      ScriptContext txi _ _ = sc
   in if List.length (txInfoOutputs txi) `PlutusTx.modInteger` 2 PlutusTx.== 0
        then ()
        else PlutusTx.traceError "Odd number of outputs"
{-# INLINEABLE checkScriptContext1 #-}

mkCheckScriptContext1Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext1Code sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||checkScriptContext1||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- This example aims to *force* the decoding of the script context and then ignore it entirely.
-- This corresponds to the unfortunate case where the decoding "wrapper" around a script forces
-- all the decoding work to be done even if it isn't used.
checkScriptContext2 :: PlutusTx.BuiltinData -> ()
checkScriptContext2 d =
  let (sc :: ScriptContext) = PlutusTx.unsafeFromBuiltinData d
   in -- Just using a bang pattern was not enough to stop GHC from getting
      -- rid of the dead binding before we even hit the plugin, this works
      -- for now!
      case sc of
        !_ ->
          if 48 PlutusTx.* 9900 PlutusTx.== (475200 :: Integer)
            then ()
            else PlutusTx.traceError "Got my sums wrong"
{-# INLINEABLE checkScriptContext2 #-}

mkCheckScriptContext2Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext2Code sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||checkScriptContext2||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

{- Note [Redundant arguments to equality benchmarks]
The arguments for the benchmarks are passed as terms created with `liftCodeDef`.
But the benchmark still needs to _evaluate_ these terms, which adds overhead that
distracts from the main point.

We can't easily remove the overhead, but we can at least include it in both cases to
make things fairer. Hence we include redundant arguments in the two cases to ensure
the same work is done in both cases. There is a third case that is just this overhead
for comparison.
-}

-- This example checks the script context for equality (with itself) when encoded as `Data`.
-- That means it just takes a single builtin call, which is fast (so long as the builtin is
-- costed cheaply).
scriptContextEqualityData :: ScriptContext -> PlutusTx.BuiltinData -> ()
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityData _ d =
  if PlutusTx.equalsData d d
    then ()
    else PlutusTx.traceError "The argument is not equal to itself"
{-# INLINEABLE scriptContextEqualityData #-}

mkScriptContextEqualityDataCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityDataCode sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||scriptContextEqualityData||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- This example is just the overhead from the previous two
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityOverhead :: ScriptContext -> PlutusTx.BuiltinData -> ()
scriptContextEqualityOverhead _ _ = ()
{-# INLINEABLE scriptContextEqualityOverhead #-}

mkScriptContextEqualityOverheadCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityOverheadCode sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||scriptContextEqualityOverhead||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- From `Cardano.Ledger.Plutus.Preprocessor.Source.V3`.
purposeIsWellFormed :: ScriptContext -> PlutusTx.BuiltinUnit
purposeIsWellFormed = \case
  ScriptContext
    TxInfo
      { txInfoMint = infoMint
      , txInfoInputs = infoInputs
      , txInfoWdrl = infoWdrl
      , txInfoTxCerts = infoTxCerts
      , txInfoVotes = infoVotes
      }
    _redeemer
    scriptInfo -> PlutusTx.check $
      case scriptInfo of
        MintingScript cs ->
          Map.member cs . getValue $ mintValueMinted infoMint
        SpendingScript txOutRef mDatum ->
          case mDatum of
            Just _ -> False
            Nothing ->
              List.null $ List.filter ((txOutRef PlutusTx.==) . txInInfoOutRef) infoInputs
        RewardingScript cred ->
          Map.member cred infoWdrl
        CertifyingScript _idx txCert ->
          List.null $ List.filter (txCert PlutusTx.==) infoTxCerts
        VotingScript voter ->
          Map.member voter infoVotes
        ProposingScript _idx _propProc -> True

compiledPurposeIsWellFormed :: PlutusTx.CompiledCode (ScriptContext -> PlutusTx.BuiltinUnit)
compiledPurposeIsWellFormed = $$(PlutusTx.compile [||purposeIsWellFormed||])

mkPurposeIsWellFormedCode :: ScriptContext -> PlutusTx.CompiledCode PlutusTx.BuiltinUnit
mkPurposeIsWellFormedCode sc =
  compiledPurposeIsWellFormed `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
