{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect'
    in the emulator
-}
module Plutus.ChainIndex.Emulator.Handlers(
    handleQuery
    , handleControl
    , ChainIndexEmulatorState(..)
    , diskState
    , utxoIndex
    ) where

import           Control.Lens                          (at, ix, makeLenses, over, preview, set, to, view, (&))
import           Control.Monad.Freer                   (Eff, Member, type (~>))
import           Control.Monad.Freer.Error             (Error, throwError)
import           Control.Monad.Freer.Extras.Log        (LogMsg, logDebug, logError, logWarn)
import           Control.Monad.Freer.Extras.Pagination (pageOf)
import           Control.Monad.Freer.State             (State, get, gets, modify, put)
import           Data.Maybe                            (catMaybes, fromMaybe)
import           Data.Semigroup.Generic                (GenericSemigroupMonoid (..))
import qualified Data.Set                              as Set
import           GHC.Generics                          (Generic)
import           Ledger                                (Address (addressCredential), ChainIndexTxOut (..),
                                                        MintingPolicy (MintingPolicy),
                                                        MintingPolicyHash (MintingPolicyHash),
                                                        StakeValidator (StakeValidator),
                                                        StakeValidatorHash (StakeValidatorHash), TxId,
                                                        TxOut (txOutAddress), TxOutRef (..), Validator (Validator),
                                                        ValidatorHash (ValidatorHash), txOutDatumHash, txOutValue)
import           Ledger.Scripts                        (ScriptHash (ScriptHash))
import           Plutus.ChainIndex.ChainIndexError     (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog       (ChainIndexLog (..))
import           Plutus.ChainIndex.Effects             (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Emulator.DiskState  (DiskState, addressMap, assetClassMap, dataMap, redeemerMap,
                                                        scriptMap, txMap)
import qualified Plutus.ChainIndex.Emulator.DiskState  as DiskState
import           Plutus.ChainIndex.Tx                  (ChainIndexTx, _ValidTx, citxOutputs)
import qualified Plutus.ChainIndex.TxUtxoBalance       as TxUtxoBalance
import           Plutus.ChainIndex.Types               (Diagnostics (..), Point (PointAtGenesis), Tip (..),
                                                        TxUtxoBalance (..))
import           Plutus.ChainIndex.UtxoState           (InsertUtxoSuccess (..), RollbackResult (..), UtxoIndex, tip,
                                                        utxoState)
import qualified Plutus.ChainIndex.UtxoState           as UtxoState
import           Plutus.V1.Ledger.Api                  (Credential (PubKeyCredential, ScriptCredential))

data ChainIndexEmulatorState =
    ChainIndexEmulatorState
        { _diskState :: DiskState
        , _utxoIndex :: UtxoIndex TxUtxoBalance
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ChainIndexEmulatorState)

makeLenses ''ChainIndexEmulatorState

-- | Get the 'ChainIndexTx' for a transaction ID
getTxFromTxId ::
    forall effs.
    (Member (State ChainIndexEmulatorState) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => TxId
    -> Eff effs (Maybe ChainIndexTx)
getTxFromTxId i = do
    result <- gets (view $ diskState . txMap . at i)
    case result of
        Nothing -> logWarn (TxNotFound i) >> pure Nothing
        _       -> pure result

-- | Get the 'ChainIndexTxOut' for a 'TxOutRef'.
getTxOutFromRef ::
  forall effs.
  ( Member (State ChainIndexEmulatorState) effs
  , Member (LogMsg ChainIndexLog) effs
  )
  => TxOutRef
  -> Eff effs (Maybe ChainIndexTxOut)
getTxOutFromRef ref@TxOutRef{txOutRefId, txOutRefIdx} = do
  ds <- gets (view diskState)
  -- Find the output in the tx matching the output ref
  case preview (txMap . ix txOutRefId . citxOutputs . _ValidTx . ix (fromIntegral txOutRefIdx)) ds of
    Nothing -> logWarn (TxOutNotFound ref) >> pure Nothing
    Just txout -> do
      -- The output might come from a public key address or a script address.
      -- We need to handle them differently.
      case addressCredential $ txOutAddress txout of
        PubKeyCredential _ ->
          pure $ Just $ PublicKeyChainIndexTxOut (txOutAddress txout) (txOutValue txout)
        ScriptCredential vh@(ValidatorHash h) -> do
          case txOutDatumHash txout of
            Nothing -> do
              -- If the txout comes from a script address, the Datum should not be Nothing
              logWarn $ NoDatumScriptAddr txout
              pure Nothing
            Just dh -> do
              let v = maybe (Left vh) (Right . Validator) $ preview (scriptMap . ix (ScriptHash h)) ds
              let d = maybe (Left dh) Right $ preview (dataMap . ix dh) ds
              pure $ Just $ ScriptChainIndexTxOut (txOutAddress txout) v d (txOutValue txout)

handleQuery ::
    forall effs.
    ( Member (State ChainIndexEmulatorState) effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = \case
    DatumFromHash h -> gets (view $ diskState . dataMap . at h)
    ValidatorFromHash (ValidatorHash h) ->  do
      gets (fmap (fmap Validator) . view $ diskState . scriptMap . at (ScriptHash h))
    MintingPolicyFromHash (MintingPolicyHash h) ->
      gets (fmap (fmap MintingPolicy) . view $ diskState . scriptMap . at (ScriptHash h))
    StakeValidatorFromHash (StakeValidatorHash h) ->
      gets (fmap (fmap StakeValidator) . view $ diskState . scriptMap . at (ScriptHash h))
    TxOutFromRef ref -> getTxOutFromRef ref
    RedeemerFromHash h -> gets (view $ diskState . redeemerMap . at h)
    TxFromTxId i -> getTxFromTxId i
    UtxoSetMembership r -> do
        utxo <- gets (utxoState . view utxoIndex)
        case tip utxo of
            TipAtGenesis -> throwError QueryFailedNoTip
            tp           -> pure (tp, TxUtxoBalance.isUnspentOutput r utxo)
    UtxoSetAtAddress pageQuery cred -> do
        state <- get
        let outRefs = view (diskState . addressMap . at cred) state
            utxo = view (utxoIndex . to utxoState) state
            utxoRefs = Set.filter (flip TxUtxoBalance.isUnspentOutput utxo)
                                  (fromMaybe mempty outRefs)
            page = pageOf pageQuery utxoRefs
        case tip utxo of
            TipAtGenesis -> do
                logWarn TipIsGenesis
                pure (TipAtGenesis, pageOf pageQuery Set.empty)
            tp           -> pure (tp, page)
    UtxoSetWithCurrency pageQuery assetClass -> do
        state <- get
        let outRefs = view (diskState . assetClassMap . at assetClass) state
            utxo = view (utxoIndex . to utxoState) state
            utxoRefs = Set.filter (flip TxUtxoBalance.isUnspentOutput utxo) (fromMaybe mempty outRefs)
            page = pageOf pageQuery utxoRefs
        case tip utxo of
            TipAtGenesis -> do
                logWarn TipIsGenesis
                pure (TipAtGenesis, pageOf pageQuery Set.empty)
            tp           -> pure (tp, page)
    GetTip ->
        gets (tip . utxoState . view utxoIndex)

handleControl ::
    forall effs.
    ( Member (State ChainIndexEmulatorState) effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    )
    => ChainIndexControlEffect
    ~> Eff effs
handleControl = \case
    AppendBlock tip_ transactions -> do
        oldState <- get @ChainIndexEmulatorState
        case UtxoState.insert (TxUtxoBalance.fromBlock tip_ transactions) (view utxoIndex oldState) of
            Left err -> do
                let reason = InsertionFailed err
                logError $ Err reason
                throwError reason
            Right InsertUtxoSuccess{newIndex, insertPosition} -> do
                put $ oldState
                        & set utxoIndex newIndex
                        & over diskState (mappend $ foldMap DiskState.fromTx transactions)
                logDebug $ InsertionSuccess tip_ insertPosition
    Rollback tip_ -> do
        oldState <- get @ChainIndexEmulatorState
        case TxUtxoBalance.rollback tip_ (view utxoIndex oldState) of
            Left err -> do
                let reason = RollbackFailed err
                logError $ Err reason
                throwError reason
            Right RollbackResult{newTip, rolledBackIndex} -> do
                put $ oldState & set utxoIndex rolledBackIndex
                logDebug $ RollbackSuccess newTip
    ResumeSync PointAtGenesis -> pure ()
    ResumeSync _ ->
        -- The emulator can only resume from genesis.
        throwError ResumeNotSupported
    CollectGarbage -> do
        -- Rebuild the index using only transactions that still have at
        -- least one output in the UTXO set
        utxos <- gets $
            Set.toList
            . Set.map txOutRefId
            . TxUtxoBalance.unspentOutputs
            . UtxoState.utxoState
            . view utxoIndex
        newDiskState <- foldMap DiskState.fromTx . catMaybes <$> mapM getTxFromTxId utxos
        modify $ set diskState newDiskState
    GetDiagnostics -> diagnostics <$> get @ChainIndexEmulatorState

diagnostics :: ChainIndexEmulatorState -> Diagnostics
diagnostics (ChainIndexEmulatorState ds ui) =
    let TxUtxoBalance outputs inputs = UtxoState._usTxUtxoData $ UtxoState.utxoState ui
    in (DiskState.diagnostics ds)
        { numUnspentOutputs  = length outputs
        , numUnmatchedInputs = length inputs
        }
