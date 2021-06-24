{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect'
    in the emulator
-}
module Plutus.ChainIndex.Emulator.Handlers(
    handleQuery
    , handleControl
    , ChainIndexEmulatorState
    , diskState
    , utxoIndex
    , ChainIndexError(..)
    , ChainIndexLog(..)
    ) where

import           Control.Lens                         (at, ix, makeLenses, over, preview, set, to, view, (&))
import           Control.Monad.Freer                  (Eff, Member, type (~>))
import           Control.Monad.Freer.Error            (Error, throwError)
import           Control.Monad.Freer.Extras.Log       (LogMsg, logDebug, logError)
import           Control.Monad.Freer.State            (State, get, gets, modify, put)
import           Data.Default                         (Default (..))
import           Data.FingerTree                      (Measured (..))
import           Data.Maybe                           (catMaybes, fromMaybe)
import qualified Data.Set                             as Set
import           Ledger                               (TxId, TxOutRef (..))
import           Plutus.ChainIndex.Effects            (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Emulator.DiskState (DiskState, addressMap, dataMap, mintingPolicyMap, txMap,
                                                       validatorMap)
import qualified Plutus.ChainIndex.Emulator.DiskState as DiskState
import           Plutus.ChainIndex.Tx                 (ChainIndexTx, citxOutputs)
import           Plutus.ChainIndex.Types              (Tip, pageOf)
import           Plutus.ChainIndex.UtxoState          (InsertUtxoPosition, InsertUtxoSuccess (..), RollbackResult (..),
                                                       UtxoIndex, isUnspentOutput, tip)
import qualified Plutus.ChainIndex.UtxoState          as UtxoState

data ChainIndexEmulatorState =
    ChainIndexEmulatorState
        { _diskState :: DiskState
        , _utxoIndex :: UtxoIndex
        }

makeLenses ''ChainIndexEmulatorState

-- | Get the 'ChainIndexTx' for a transaction ID
getTxFromTxId ::
    forall effs.
    (Member (State ChainIndexEmulatorState) effs)
    => TxId
    -> Eff effs (Maybe ChainIndexTx)
getTxFromTxId i = gets (view $ diskState . txMap . at i)

handleQuery ::
    forall effs.
    ( Member (State ChainIndexEmulatorState) effs
    , Member (Error ChainIndexError) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = \case
    DatumFromHash h -> gets (view $ diskState . dataMap . at h)
    ValidatorFromHash h -> gets (view $ diskState . validatorMap . at h)
    MintingPolicyFromHash h -> gets (view $ diskState . mintingPolicyMap . at h)
    TxOutFromRef TxOutRef{txOutRefId, txOutRefIdx} -> gets @ChainIndexEmulatorState (preview $ diskState . txMap . ix txOutRefId . citxOutputs . ix (fromIntegral txOutRefIdx))
    TxFromTxId i -> getTxFromTxId i
    UtxoSetMembership r -> do
        utxoState <- gets (measure . view utxoIndex)
        case tip utxoState of
            Nothing -> throwError QueryFailedNoTip
            Just tp -> pure (tp, isUnspentOutput r utxoState)
    UtxoSetAtAddress cred -> do
        state <- get
        let outRefs = view (diskState . addressMap . at cred) state
            utxoState = view (utxoIndex . to measure) state
            page = pageOf def $ Set.filter (\r -> isUnspentOutput r utxoState) (fromMaybe mempty outRefs)
        case tip utxoState of
            Nothing -> throwError QueryFailedNoTip
            Just tp -> pure (tp, page)
    GetTip ->
        gets (tip . measure . view utxoIndex) >>= maybe (throwError QueryFailedNoTip) pure

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
        case UtxoState.insert (UtxoState.fromBlock tip_ transactions) (view utxoIndex oldState) of
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
        case UtxoState.rollback tip_ (view utxoIndex oldState) of
            Left err -> do
                let reason = RollbackFailed err
                logError $ Err reason
                throwError reason
            Right RollbackResult{newTip, rolledBackIndex} -> do
                put $ oldState & set utxoIndex rolledBackIndex
                logDebug $ RollbackSuccess newTip
    CollectGarbage -> do
        -- Rebuild the index using only transactions that still have at
        -- least one output in the UTXO set
        utxos <- gets (Set.toList . Set.map txOutRefId . UtxoState.unspentOutputs . UtxoState.utxoState . view utxoIndex)
        newDiskState <- foldMap DiskState.fromTx . catMaybes <$> mapM getTxFromTxId utxos
        modify $ set diskState newDiskState

data ChainIndexError =
    InsertionFailed UtxoState.InsertUtxoFailed
    | RollbackFailed UtxoState.RollbackFailed
    | QueryFailedNoTip -- ^ Query failed because the chain index does not have a tip (not synchronised with node)

data ChainIndexLog =
    InsertionSuccess Tip InsertUtxoPosition
    | RollbackSuccess Tip
    | Err ChainIndexError
