{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.ScriptContextBuilder.Builder
  ( UnitTestArgs (..)
  , InputBuilder (..)
  , TxOutBuilder (..)
  , ScriptContextBuilder (..)
  , ScriptContextBuilderState (..)
  , buildScriptContext
  , withRedeemer
  , withFee
  , withSigner
  , withSigners
  , withMint
  , withMintingScript
  , withSpendingScript
  , withRewardingScript
  , withRewardingScriptWithBuilder
  , withOutput
  , withInput
  , withScriptInput
  , withReferenceInput
  , withValue
  , withValidRange
  , withOutRef
  , withInlineDatum
  , withReferenceScript
  , withAddress
  , withWithdrawal
  , mkInput
  , addInput
  , addMint
  , mkMintingScriptWithPurpose
  , addChangeOutput
  , signAndAddChangeOutput
  , mkAdaValue
  , mkTxOut
  , withTxOutReferenceScript
  , withTxOutInlineDatum
  , withTxOutValue
  , withTxOutAddress
  , addOutput
  , addReferenceInput
  , buildBalancedScriptContext
  , balanceWithChangeOutput
  , builderPlaceHolderTxOutRef

    -- * Helpers
  , currencySymbolFromHex
  , singleCurrencySymbol
  )
where

import Control.Lens ((%~), (&), (.~), (^.))
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BS8
import Data.Function (on)
import Data.List qualified as List
import Data.Maybe (isJust)
import Data.Ord (comparing)
import GHC.Generics (Generic)
import PlutusLedgerApi.Test.ScriptContextBuilder.Lenses
  ( scriptContextTxInfoL
  , txInfoFeeL
  , txInfoInputsL
  , txInfoMintL
  , txInfoOutputsL
  , txInfoRedeemersAssocL
  , txInfoReferenceInputsL
  , txInfoSignatoriesL
  )
import PlutusLedgerApi.V1.Address (toPubKeyHash, toScriptHash)
import PlutusLedgerApi.V3
  ( Address (Address)
  , BuiltinData
  , Credential (PubKeyCredential)
  , CurrencySymbol (CurrencySymbol)
  , Datum (Datum)
  , Lovelace (getLovelace)
  , OutputDatum (..)
  , POSIXTimeRange
  , PubKeyHash (PubKeyHash)
  , Redeemer (Redeemer)
  , ScriptContext (ScriptContext, scriptContextRedeemer, scriptContextScriptInfo, scriptContextTxInfo)
  , ScriptHash
  , ScriptInfo (MintingScript, RewardingScript, SpendingScript)
  , ScriptPurpose (..)
  , TxCert
  , TxId (TxId)
  , TxInInfo (TxInInfo, txInInfoOutRef, txInInfoResolved)
  , TxInfo (..)
  , TxOut (TxOut, txOutAddress, txOutDatum, txOutReferenceScript, txOutValue)
  , TxOutRef (TxOutRef)
  , Value (Value, getValue)
  , adaSymbol
  , adaToken
  , always
  , singleton
  )
import PlutusLedgerApi.V3.MintValue (MintValue (UnsafeMintValue), mintValueToMap)
import PlutusTx qualified
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Builtins.Internal (BuiltinByteString (..))
import PlutusTx.Eq qualified
import PlutusTx.Numeric qualified as PlutusTx

instance PlutusTx.Eq.Eq ScriptPurpose where
  a == b = PlutusTx.toBuiltinData a == PlutusTx.toBuiltinData b

-- | Arguments for a unit test: a script context and additional parameters.
data UnitTestArgs = UnitTestArgs
  { utaScriptContext :: ScriptContext
  , utaParameters :: [BuiltinData]
  }
  deriving stock (Generic)

-- | Create a 'Value' containing only ADA from a 'Lovelace' amount.
mkAdaValue :: Lovelace -> Value
mkAdaValue = singleton adaSymbol adaToken . getLovelace

-- | Add a minting entry to an existing 'ScriptContext'.
addMint :: ScriptContext -> Value -> BuiltinData -> ScriptContext
addMint ctx newMint redeemer =
  let existingMint = Value $ mintValueToMap (ctx ^. scriptContextTxInfoL . txInfoMintL)
      mergedMint = UnsafeMintValue (getValue (existingMint <> newMint))
      mintCS = singleCurrencySymbol newMint
   in ctx
        & scriptContextTxInfoL . txInfoMintL .~ mergedMint
        & scriptContextTxInfoL . txInfoRedeemersAssocL
          %~ Map.insert (Minting mintCS) (Redeemer redeemer)

-- | Add a transaction input to an existing 'ScriptContext', sorted by 'TxOutRef'.
addInput :: TxInInfo -> ScriptContext -> ScriptContext
addInput newInput =
  scriptContextTxInfoL . txInfoInputsL
    %~ List.insertBy (comparing txInInfoOutRef) newInput

-- | Add a reference input to an existing 'ScriptContext', sorted by 'TxOutRef'.
addReferenceInput :: TxInInfo -> ScriptContext -> ScriptContext
addReferenceInput newInput =
  scriptContextTxInfoL . txInfoReferenceInputsL
    %~ List.insertBy (comparing txInInfoOutRef) newInput

-- | Prepend a transaction output to an existing 'ScriptContext'.
addOutput :: TxOut -> ScriptContext -> ScriptContext
addOutput newOutput =
  scriptContextTxInfoL . txInfoOutputsL %~ (newOutput :)

-- | A composable builder for constructing transaction inputs.
newtype InputBuilder = InputBuilder {runInputBuilder :: InputBuilderState -> InputBuilderState}

-- | Accumulated state for 'InputBuilder'.
data InputBuilderState = InputBuilderState
  { ibOutRef :: TxOutRef
  -- ^ UTXO reference for the input.
  , ibAddress :: Address
  -- ^ Address of the input.
  , ibValue :: Value
  -- ^ The value (assets) contained in the input.
  , ibDatum :: OutputDatum
  -- ^ Optional inline datum.
  , ibReferenceScript :: Maybe ScriptHash
  -- ^ Optional reference script.
  }

instance Semigroup InputBuilder where
  InputBuilder a <> InputBuilder b = InputBuilder (a . b)

instance Monoid InputBuilder where
  mempty = InputBuilder id

-- | Default placeholder 'TxOutRef' used when none is specified.
builderPlaceHolderTxOutRef :: TxOutRef
builderPlaceHolderTxOutRef = TxOutRef "deadbeef" 0

builderPlaceHolderAddress :: Address
builderPlaceHolderAddress = Address (PubKeyCredential (PubKeyHash "deadbeef")) Nothing

defaultInputBuilderState :: InputBuilderState
defaultInputBuilderState =
  InputBuilderState
    { ibOutRef = builderPlaceHolderTxOutRef
    , ibAddress = builderPlaceHolderAddress
    , ibValue = mempty
    , ibDatum = NoOutputDatum
    , ibReferenceScript = Nothing
    }

-- | Set the UTXO reference for an input.
withOutRef :: TxOutRef -> InputBuilder
withOutRef outRef =
  InputBuilder \inputBuilder -> inputBuilder {ibOutRef = outRef}

-- | Set the address for an input.
withAddress :: Address -> InputBuilder
withAddress address =
  InputBuilder \inputBuilder -> inputBuilder {ibAddress = address}

-- | Set the value for an input.
withValue :: Value -> InputBuilder
withValue value =
  InputBuilder \inputBuilder -> inputBuilder {ibValue = value}

-- | Attach an inline datum to an input.
withInlineDatum :: BuiltinData -> InputBuilder
withInlineDatum datum =
  InputBuilder \inputBuilder -> inputBuilder {ibDatum = OutputDatum (Datum datum)}

-- | Attach a reference script to an input.
withReferenceScript :: ScriptHash -> InputBuilder
withReferenceScript scriptHash =
  InputBuilder \inputBuilder -> inputBuilder {ibReferenceScript = Just scriptHash}

-- | Finalize an 'InputBuilder' into a 'TxInInfo'.
mkInput :: InputBuilder -> TxInInfo
mkInput (InputBuilder modify) =
  let builder = modify defaultInputBuilderState
   in TxInInfo
        { txInInfoOutRef = ibOutRef builder
        , txInInfoResolved =
            TxOut
              { txOutAddress = ibAddress builder
              , txOutValue = ibValue builder
              , txOutDatum = ibDatum builder
              , txOutReferenceScript = Nothing
              }
        }

-- | A composable builder for constructing transaction outputs.
newtype TxOutBuilder = TxOutBuilder
  { runTxOutBuilder :: TxOutBuilderState -> TxOutBuilderState
  }

-- | Accumulated state for 'TxOutBuilder'.
data TxOutBuilderState = TxOutBuilderState
  { tobAddress :: Address
  , tobValue :: Value
  , tobDatum :: OutputDatum
  , tobReferenceScript :: Maybe ScriptHash
  }

defaultTxOutBuilderState :: TxOutBuilderState
defaultTxOutBuilderState =
  TxOutBuilderState
    { tobAddress = builderPlaceHolderAddress
    , tobValue = mempty
    , tobDatum = NoOutputDatum
    , tobReferenceScript = Nothing
    }

instance Semigroup TxOutBuilder where
  TxOutBuilder f <> TxOutBuilder g = TxOutBuilder (f . g)

instance Monoid TxOutBuilder where
  mempty = TxOutBuilder id

-- | Set the address for a transaction output.
withTxOutAddress :: Address -> TxOutBuilder
withTxOutAddress addr =
  TxOutBuilder \tob -> tob {tobAddress = addr}

-- | Add value to a transaction output (accumulates with existing value).
withTxOutValue :: Value -> TxOutBuilder
withTxOutValue val =
  TxOutBuilder \tob -> tob {tobValue = tobValue tob <> val}

-- | Attach an inline datum to a transaction output.
withTxOutInlineDatum :: BuiltinData -> TxOutBuilder
withTxOutInlineDatum datum =
  TxOutBuilder \tob -> tob {tobDatum = OutputDatum $ Datum datum}

-- | Attach a reference script to a transaction output.
withTxOutReferenceScript :: ScriptHash -> TxOutBuilder
withTxOutReferenceScript scriptHash =
  TxOutBuilder \tob -> tob {tobReferenceScript = Just scriptHash}

-- | Finalize a 'TxOutBuilder' into a 'TxOut'.
mkTxOut :: TxOutBuilder -> TxOut
mkTxOut (TxOutBuilder modify) =
  let finalState = modify defaultTxOutBuilderState
   in TxOut
        { txOutAddress = tobAddress finalState
        , txOutValue = tobValue finalState
        , txOutDatum = tobDatum finalState
        , txOutReferenceScript = tobReferenceScript finalState
        }

-- | Create a minimal 'ScriptContext' for a minting script.
mkMintingScriptWithPurpose :: Value -> BuiltinData -> ScriptContext
mkMintingScriptWithPurpose mintValue redeemer =
  ScriptContext
    { scriptContextTxInfo = mintingScriptTxInfo
    , scriptContextRedeemer = Redeemer redeemer
    , scriptContextScriptInfo = MintingScript mintCS
    }
  where
    mintCS :: CurrencySymbol
    mintCS = singleCurrencySymbol mintValue

    mintingScriptTxInfo :: TxInfo
    mintingScriptTxInfo =
      TxInfo
        { txInfoInputs = mempty
        , txInfoReferenceInputs = mempty
        , txInfoOutputs = mempty
        , txInfoFee = 0
        , txInfoMint = UnsafeMintValue (getValue mintValue)
        , txInfoTxCerts = mempty
        , txInfoWdrl = Map.empty
        , txInfoValidRange = always
        , txInfoSignatories = mempty
        , txInfoRedeemers = Map.singleton (Minting mintCS) (Redeemer redeemer)
        , txInfoData = Map.empty
        , txInfoId = TxId ""
        , txInfoVotes = Map.empty
        , txInfoProposalProcedures = mempty
        , txInfoCurrentTreasuryAmount = Nothing
        , txInfoTreasuryDonation = Nothing
        }

-- | Compute and add a change output to the given public key hash.
addChangeOutput :: PubKeyHash -> ScriptContext -> ScriptContext
addChangeOutput signerPkh ctx =
  let info = ctx ^. scriptContextTxInfoL
      totalInputValue = foldMap (txOutValue . txInInfoResolved) (info ^. txInfoInputsL)
      totalOutputValue = foldMap txOutValue (info ^. txInfoOutputsL)
      feeValue = mkAdaValue (info ^. txInfoFeeL)
      mintedValue = Value (mintValueToMap (info ^. txInfoMintL))
      changeOutput =
        TxOut
          (Address (PubKeyCredential signerPkh) Nothing)
          ( mintedValue
              <> totalInputValue
              <> PlutusTx.negate feeValue
              <> PlutusTx.negate totalOutputValue
          )
          NoOutputDatum
          Nothing
   in ctx & scriptContextTxInfoL . txInfoOutputsL %~ (changeOutput :)

-- | Balance the transaction by adding a change output to the first public key input.
balanceWithChangeOutput :: ScriptContext -> ScriptContext
balanceWithChangeOutput ctx =
  let info = ctx ^. scriptContextTxInfoL
      resolvedInputs = map txInInfoResolved (info ^. txInfoInputsL)
      signerPkh = case filter (isJust . toPubKeyHash . txOutAddress) resolvedInputs of
        TxOut (Address (PubKeyCredential pkh) _) _ _ _ : _ -> pkh
        _ -> PubKeyHash "deadbeef"
      -- \^ Fallback to default if no public key input is found
      totalInputValue = foldMap (txOutValue . txInInfoResolved) (info ^. txInfoInputsL)
      totalOutputValue = foldMap txOutValue (info ^. txInfoOutputsL)
      feeValue = mkAdaValue (info ^. txInfoFeeL)
      mintedValue = Value $ mintValueToMap (info ^. txInfoMintL)
      changeOutput =
        TxOut
          (Address (PubKeyCredential signerPkh) Nothing)
          ( mintedValue
              <> totalInputValue
              <> PlutusTx.negate feeValue
              <> PlutusTx.negate totalOutputValue
          )
          NoOutputDatum
          Nothing
   in ctx & scriptContextTxInfoL . txInfoOutputsL %~ (<> [changeOutput])

-- | Add a signatory to an existing 'ScriptContext'.
addSigner :: PubKeyHash -> ScriptContext -> ScriptContext
addSigner signerPkh =
  scriptContextTxInfoL . txInfoSignatoriesL %~ (signerPkh :)

-- | Add a signatory and compute a change output for the same public key hash.
signAndAddChangeOutput :: PubKeyHash -> ScriptContext -> ScriptContext
signAndAddChangeOutput signerPkh ctx =
  addSigner signerPkh (addChangeOutput signerPkh ctx)

-- | A composable builder for constructing a 'ScriptContext'.
newtype ScriptContextBuilder = ScriptContextBuilder
  { runBuilder :: ScriptContextBuilderState -> ScriptContextBuilderState
  }

-- | Accumulated state for 'ScriptContextBuilder'.
data ScriptContextBuilderState = ScriptContextBuilderState
  { scbInputs :: [TxInInfo]
  , scbReferenceInputs :: [TxInInfo]
  , scbOutputs :: [TxOut]
  , scbFee :: Integer
  , scbMint :: Value
  , scbCerts :: [TxCert]
  , scbWdrl :: Map.Map Credential Lovelace
  , scbValidRange :: POSIXTimeRange
  , scbSignatories :: [PubKeyHash]
  , scbRedeemers :: Map.Map ScriptPurpose Redeemer
  , scbTxId :: TxId
  , scbScriptInfo :: ScriptInfo
  , scbRedeemer :: BuiltinData
  }

defaultScriptContextBuilderState :: ScriptContextBuilderState
defaultScriptContextBuilderState =
  ScriptContextBuilderState
    { scbInputs = []
    , scbReferenceInputs = []
    , scbOutputs = []
    , scbFee = 0
    , scbMint = mempty
    , scbCerts = []
    , scbWdrl = Map.empty
    , scbValidRange = always
    , scbRedeemers = Map.empty
    , scbSignatories = []
    , scbTxId = TxId "deadbeef"
    , scbScriptInfo = MintingScript $ currencySymbolFromHex "deadbeef"
    , scbRedeemer = PlutusTx.toBuiltinData ()
    }

instance Semigroup ScriptContextBuilder where
  (ScriptContextBuilder f) <> (ScriptContextBuilder g) = ScriptContextBuilder (g . f)

instance Monoid ScriptContextBuilder where
  mempty = ScriptContextBuilder id

-- | Set the transaction fee.
withFee :: Integer -> ScriptContextBuilder
withFee fee = ScriptContextBuilder \scb -> scb {scbFee = fee}

-- | Set the transaction validity time range.
withValidRange :: POSIXTimeRange -> ScriptContextBuilder
withValidRange validRange = ScriptContextBuilder \scb -> scb {scbValidRange = validRange}

-- | Add a signatory to the transaction.
withSigner :: PubKeyHash -> ScriptContextBuilder
withSigner pkh = ScriptContextBuilder \scb ->
  scb {scbSignatories = List.insert pkh (scbSignatories scb)}

-- | Add multiple signatories to the transaction.
withSigners :: [PubKeyHash] -> ScriptContextBuilder
withSigners pks = ScriptContextBuilder \scb ->
  scb {scbSignatories = foldr (\p acc -> List.insert p acc) (scbSignatories scb) pks}

-- | Add a minting entry with the given value and redeemer.
withMint :: Value -> BuiltinData -> ScriptContextBuilder
withMint value redeemer = ScriptContextBuilder \scb ->
  let mintCS = singleCurrencySymbol value
      newRedeemers = Map.insert (Minting mintCS) (Redeemer redeemer) (scbRedeemers scb)
   in scb {scbMint = scbMint scb <> value, scbRedeemers = newRedeemers}

-- | Add a transaction output.
withOutput :: TxOutBuilder -> ScriptContextBuilder
withOutput modify = ScriptContextBuilder \scb ->
  scb {scbOutputs = mkTxOut modify : scbOutputs scb}

-- | Add a public-key input. Errors if the address is a script address.
withInput :: InputBuilder -> ScriptContextBuilder
withInput inputBuilder = ScriptContextBuilder \scb ->
  if isJust (toPubKeyHash (txOutAddress (txInInfoResolved newInput)))
    then scb {scbInputs = List.insertBy (comparing txInInfoOutRef) newInput (scbInputs scb)}
    else error "withInput: Input address is not a public key address"
  where
    newInput :: TxInInfo
    newInput = mkInput inputBuilder

-- | Add a script input with a redeemer. Errors if the address is not a script address.
withScriptInput :: BuiltinData -> InputBuilder -> ScriptContextBuilder
withScriptInput redeemer modify = ScriptContextBuilder \scb ->
  let newInput = mkInput modify
      inputOutRef = txInInfoOutRef newInput
      newRedeemers = Map.insert (Spending inputOutRef) (Redeemer redeemer) (scbRedeemers scb)
   in if isJust (toScriptHash (txOutAddress $ txInInfoResolved newInput))
        then
          scb
            { scbInputs = List.insertBy (comparing txInInfoOutRef) newInput (scbInputs scb)
            , scbRedeemers = newRedeemers
            }
        else error "withScriptInput: Input address is not a script address"

-- | Add a reference input (read-only, not spent).
withReferenceInput :: InputBuilder -> ScriptContextBuilder
withReferenceInput inputBuilder = ScriptContextBuilder \scb ->
  scb
    { scbReferenceInputs =
        List.insertBy
          (comparing txInInfoOutRef)
          (mkInput inputBuilder)
          (scbReferenceInputs scb)
    }

-- | Set the script purpose to minting and add a mint entry.
withMintingScript :: Value -> BuiltinData -> ScriptContextBuilder
withMintingScript mintValue redeemer =
  withMint mintValue redeemer <> ScriptContextBuilder \scb ->
    scb {scbScriptInfo = MintingScript (singleCurrencySymbol mintValue)}

-- | Set the script purpose to spending and add the script input.
withSpendingScript :: BuiltinData -> InputBuilder -> ScriptContextBuilder
withSpendingScript redeemer modify = ScriptContextBuilder \scb ->
  let scriptInput = mkInput modify
      outRef = txInInfoOutRef scriptInput
      newRedeemers = Map.insert (Spending outRef) (Redeemer redeemer) (scbRedeemers scb)
      datum =
        case txOutDatum (txInInfoResolved scriptInput) of
          NoOutputDatum -> Nothing
          OutputDatum (Datum dat) -> Just (Datum dat)
          OutputDatumHash {} -> Nothing
   in scb
        { scbScriptInfo = SpendingScript outRef datum
        , scbInputs = List.insertBy (comparing txInInfoOutRef) scriptInput (scbInputs scb)
        , scbRedeemers = newRedeemers
        , scbRedeemer = redeemer
        }

-- | Set the script purpose to rewarding with a fixed redeemer.
withRewardingScript :: BuiltinData -> Credential -> Integer -> ScriptContextBuilder
withRewardingScript redeemer cred adaAmount =
  ScriptContextBuilder \scb ->
    scb
      { scbWdrl = Map.insert cred (fromIntegral adaAmount) (scbWdrl scb)
      , scbRedeemers = Map.insert (Rewarding cred) (Redeemer redeemer) (scbRedeemers scb)
      , scbRedeemer = redeemer
      , scbScriptInfo = RewardingScript cred
      }

-- | Set the script purpose to rewarding with a redeemer computed from the builder state.
withRewardingScriptWithBuilder
  :: (ScriptContextBuilderState -> BuiltinData)
  -> Credential
  -> Integer
  -> ScriptContextBuilder
withRewardingScriptWithBuilder mkRedeemer cred adaAmount =
  ScriptContextBuilder \scb ->
    let redeemer = mkRedeemer scb
     in scb
          { scbWdrl = Map.insert cred (fromIntegral adaAmount) (scbWdrl scb)
          , scbRedeemers = Map.insert (Rewarding cred) (Redeemer redeemer) (scbRedeemers scb)
          , scbRedeemer = redeemer
          , scbScriptInfo = RewardingScript cred
          }

-- | Add a withdrawal entry for a credential and ADA amount.
withWithdrawal :: Credential -> Integer -> ScriptContextBuilder
withWithdrawal cred adaAmount = ScriptContextBuilder \scb ->
  scb {scbWdrl = Map.insert cred (fromIntegral adaAmount) (scbWdrl scb)}

-- | Set the top-level redeemer for the script context.
withRedeemer :: BuiltinData -> ScriptContextBuilder
withRedeemer redeemer = ScriptContextBuilder \scb -> scb {scbRedeemer = redeemer}

-- | Build a 'ScriptContext' from a 'ScriptContextBuilder'.
buildScriptContext :: ScriptContextBuilder -> ScriptContext
buildScriptContext modify =
  ScriptContext
    { scriptContextTxInfo =
        TxInfo
          { txInfoInputs = reverse $ scbInputs finalState
          , txInfoReferenceInputs = reverse $ scbReferenceInputs finalState
          , txInfoOutputs = reverse $ scbOutputs finalState
          , txInfoMint = UnsafeMintValue $ getValue (scbMint finalState)
          , txInfoRedeemers = scbRedeemers finalState
          , txInfoFee = fromIntegral (scbFee finalState)
          , txInfoSignatories = scbSignatories finalState
          , txInfoTxCerts = scbCerts finalState
          , txInfoWdrl = scbWdrl finalState
          , txInfoValidRange = scbValidRange finalState
          , txInfoData = Map.empty
          , txInfoId = scbTxId finalState
          , txInfoVotes = Map.empty
          , txInfoProposalProcedures = []
          , txInfoCurrentTreasuryAmount = Nothing
          , txInfoTreasuryDonation = Nothing
          }
    , scriptContextRedeemer = Redeemer $ scbRedeemer finalState
    , scriptContextScriptInfo = scbScriptInfo finalState
    }
  where
    finalState = runBuilder modify defaultScriptContextBuilderState

comparePurposeLedger :: ScriptPurpose -> ScriptPurpose -> Ordering
comparePurposeLedger = comparing \case
  Spending {} -> 0 :: Word
  Minting {} -> 1
  Certifying {} -> 2
  Rewarding {} -> 3
  Voting {} -> 4
  Proposing {} -> 5

-- | Build a 'ScriptContext' and automatically balance it with a change output.
buildBalancedScriptContext :: ScriptContextBuilder -> ScriptContext
buildBalancedScriptContext modify =
  balanceWithChangeOutput
    ScriptContext
      { scriptContextTxInfo =
          TxInfo
            { txInfoInputs = scbInputs finalState
            , txInfoReferenceInputs = scbReferenceInputs finalState
            , txInfoOutputs = scbOutputs finalState
            , txInfoMint = UnsafeMintValue (getValue (scbMint finalState))
            , txInfoRedeemers =
                Map.unsafeFromList $
                  List.sortBy (comparePurposeLedger `on` fst) $
                    Map.toList $
                      scbRedeemers finalState
            , txInfoFee = fromIntegral (scbFee finalState)
            , txInfoSignatories = scbSignatories finalState
            , txInfoTxCerts = scbCerts finalState
            , txInfoWdrl = scbWdrl finalState
            , txInfoValidRange = scbValidRange finalState
            , txInfoData = Map.empty
            , txInfoId = scbTxId finalState
            , txInfoVotes = Map.empty
            , txInfoProposalProcedures = []
            , txInfoCurrentTreasuryAmount = Nothing
            , txInfoTreasuryDonation = Nothing
            }
      , scriptContextRedeemer = Redeemer (scbRedeemer finalState)
      , scriptContextScriptInfo = scbScriptInfo finalState
      }
  where
    finalState = runBuilder modify defaultScriptContextBuilderState

-- * Helpers

-- | Convert a hex encoded Haskell 'String' to a 'CurrencySymbol'.
currencySymbolFromHex :: String -> CurrencySymbol
currencySymbolFromHex hexStr =
  case Base16.decode (BS8.pack hexStr) of
    Left err -> error $ "currencySymbolFromHex: invalid hex: " <> err
    Right bs -> CurrencySymbol (BuiltinByteString bs)

{-| Extract the single currency symbol from a 'Value'. Errors if the value
contains zero or more than one currency symbol. -}
singleCurrencySymbol :: Value -> CurrencySymbol
singleCurrencySymbol val = case Map.keys (getValue val) of
  [cs] -> cs
  keys ->
    error $
      "singleCurrencySymbol: expected exactly 1 currency symbol, got "
        <> show (length keys)
