{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect'
    in the emulator
-}
module Plutus.ChainIndex.Emulator.Handlers(
    handleQuery
    , handleControl
    , ChainIndexEmulatorState(..)
    , diskState
    , utxoIndex
    , ChainIndexError(..)
    , ChainIndexLog(..)
    ) where

import           Cardano.BM.Data.Tracer               (ToObject (..))
import           Control.Lens                         (at, ix, makeLenses, over, preview, set, to, view, (&))
import           Control.Monad.Freer                  (Eff, Member, type (~>))
import           Control.Monad.Freer.Error            (Error, throwError)
import           Control.Monad.Freer.Extras.Log       (LogMsg, logDebug, logError, logWarn)
import           Control.Monad.Freer.State            (State, get, gets, modify, put)
import           Data.Aeson                           (FromJSON, ToJSON)
import           Data.Default                         (Default (..))
import           Data.FingerTree                      (Measured (..))
import           Data.Maybe                           (catMaybes, fromMaybe)
import           Data.Semigroup.Generic               (GenericSemigroupMonoid (..))
import qualified Data.Set                             as Set
import           GHC.Generics                         (Generic)
import           Ledger                               (Address (addressCredential),
                                                       ChainIndexTxOut (PublicKeyChainIndexTxOut), TxId,
                                                       TxOut (txOutAddress), TxOutRef (..), txOutDatumHash, txOutValue)
import           Ledger.Tx                            (ChainIndexTxOut (ScriptChainIndexTxOut))
import           Plutus.ChainIndex.Effects            (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Emulator.DiskState (DiskState, addressMap, dataMap, mintingPolicyMap, redeemerMap,
                                                       stakeValidatorMap, txMap, validatorMap)
import qualified Plutus.ChainIndex.Emulator.DiskState as DiskState
import           Plutus.ChainIndex.Tx                 (ChainIndexTx, _ValidTx, citxOutputs)
import           Plutus.ChainIndex.Types              (Tip (..), pageOf)
import           Plutus.ChainIndex.UtxoState          (InsertUtxoPosition, InsertUtxoSuccess (..), RollbackResult (..),
                                                       TxUtxoBalance, UtxoIndex, isUnspentOutput, tip)
import qualified Plutus.ChainIndex.UtxoState          as UtxoState
import           Plutus.Contract.CardanoAPI           (FromCardanoError (..))
import           Plutus.V1.Ledger.Api                 (Credential (PubKeyCredential, ScriptCredential))
import           Prettyprinter                        (Pretty (..), colon, (<+>))

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
        ScriptCredential vh -> do
          case txOutDatumHash txout of
            Nothing -> do
              -- If the txout comes from a script address, the Datum should not be Nothing
              logWarn $ NoDatumScriptAddr txout
              pure Nothing
            Just dh -> do
              let v = maybe (Left vh) Right $ preview (validatorMap . ix vh) ds
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
    ValidatorFromHash h -> gets (view $ diskState . validatorMap . at h)
    MintingPolicyFromHash h -> gets (view $ diskState . mintingPolicyMap . at h)
    StakeValidatorFromHash h -> gets (view $ diskState . stakeValidatorMap . at h)
    TxOutFromRef ref -> getTxOutFromRef ref
    RedeemerFromHash h -> gets (view $ diskState . redeemerMap . at h)
    TxFromTxId i -> getTxFromTxId i
    UtxoSetMembership r -> do
        utxoState <- gets (measure . view utxoIndex)
        case tip utxoState of
            TipAtGenesis -> throwError QueryFailedNoTip
            tp           -> pure (tp, isUnspentOutput r utxoState)
    UtxoSetAtAddress cred -> do
        state <- get
        let outRefs = view (diskState . addressMap . at cred) state
            utxoState = view (utxoIndex . to measure) state
            page = pageOf def $ Set.filter (\r -> isUnspentOutput r utxoState) (fromMaybe mempty outRefs)
        case tip utxoState of
            TipAtGenesis -> do
                logWarn TipIsGenesis
                pure (TipAtGenesis, pageOf def Set.empty)
            tp           -> pure (tp, page)
    GetTip ->
        gets (tip . measure . view utxoIndex)

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
        utxos <- gets $
            Set.toList
            . Set.map txOutRefId
            . UtxoState.unspentOutputs
            . UtxoState.utxoState
            . view utxoIndex
        newDiskState <- foldMap DiskState.fromTx . catMaybes <$> mapM getTxFromTxId utxos
        modify $ set diskState newDiskState

data ChainIndexError =
    InsertionFailed UtxoState.InsertUtxoFailed
    | RollbackFailed UtxoState.RollbackFailed
    | QueryFailedNoTip -- ^ Query failed because the chain index does not have a tip (not synchronised with node)
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty ChainIndexError where
  pretty = \case
    InsertionFailed err -> "Insertion failed" <> colon <+> pretty err
    RollbackFailed err  -> "Rollback failed" <> colon <+> pretty err
    QueryFailedNoTip    -> "Query failed" <> colon <+> "No tip."

data ChainIndexLog =
    InsertionSuccess Tip InsertUtxoPosition
    | ConversionFailed FromCardanoError
    | RollbackSuccess Tip
    | Err ChainIndexError
    | TxNotFound TxId
    | TxOutNotFound TxOutRef
    | TipIsGenesis
    | NoDatumScriptAddr TxOut
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToObject)

instance Pretty ChainIndexLog where
  pretty = \case
    InsertionSuccess t p ->
         "InsertionSuccess"
      <> colon
      <+> "New tip is"
      <+> pretty t
      <> "."
      <+> pretty p
    RollbackSuccess t -> "RollbackSuccess: New tip is" <+> pretty t
    ConversionFailed cvError -> "Conversion failed: " <+> pretty cvError
    Err ciError -> "ChainIndexError:" <+> pretty ciError
    TxNotFound txid -> "TxNotFound:" <+> pretty txid
    TxOutNotFound ref -> "TxOut not found with:" <+> pretty ref
    TipIsGenesis -> "TipIsGenesis"
    NoDatumScriptAddr txout -> "The following transaction output from a script adress does not have a datum:" <+> pretty txout
