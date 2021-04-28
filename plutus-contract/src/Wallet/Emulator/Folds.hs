{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-
This module provides a list of folds over the emulator event stream. To apply
the folds in this module to a stream of events, use
'Wallet.Emulator.Stream.foldEmulatorStreamM'. See note [Emulator event stream].

-}
module Wallet.Emulator.Folds (
    EmulatorEventFold
    , EmulatorEventFoldM
    , EmulatorFoldErr(..)
    -- * Folds for contract instances
    , instanceState
    , instanceRequests
    , instanceResponses
    , instanceOutcome
    , instanceTransactions
    , Outcome(..)
    , instanceLog
    , instanceAccumState
    -- * Folds for transactions and the UTXO set
    , chainEvents
    , failedTransactions
    , validatedTransactions
    , scriptEvents
    , utxoAtAddress
    , valueAtAddress
    -- * Folds for individual wallets (emulated agents)
    , walletWatchingAddress
    , walletFunds
    , walletFees
    -- * Folds that are used in the Playground
    , annotatedBlockchain
    , blockchain
    , emulatorLog
    , userLog
    -- * Etc.
    , renderLines
    , preMapMaybeM
    , preMapMaybe
    , postMapM
    ) where

import           Control.Foldl                          (Fold (..), FoldM (..))
import qualified Control.Foldl                          as L
import           Control.Lens                           hiding (Empty, Fold)
import           Control.Monad                          ((>=>))
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import qualified Data.Aeson                             as JSON
import           Data.Foldable                          (fold, toList)
import qualified Data.Map                               as Map
import           Data.Maybe                             (fromMaybe, mapMaybe)
import           Data.Text                              (Text)
import           Data.Text.Prettyprint.Doc              (Pretty (..), defaultLayoutOptions, layoutPretty, vsep)
import           Data.Text.Prettyprint.Doc.Render.Text  (renderStrict)
import           Ledger                                 (Block, OnChainTx (..), TxId)
import           Ledger.AddressMap                      (UtxoMap)
import qualified Ledger.AddressMap                      as AM
import           Ledger.Constraints.OffChain            (UnbalancedTx)
import           Ledger.Index                           (ScriptValidationEvent, ValidationError, ValidationPhase (..))
import           Ledger.Tx                              (Address, Tx, TxOut (..), TxOutTx (..))
import           Ledger.Value                           (Value)
import           Plutus.Contract                        (Contract)
import           Plutus.Contract.Effects.WriteTx        (HasWriteTx, pendingTransaction)
import           Plutus.Contract.Resumable              (Request, Response)
import qualified Plutus.Contract.Resumable              as State
import           Plutus.Contract.Schema                 (Event (..), Handlers)
import           Plutus.Contract.Types                  (ResumableResult (..))
import           Plutus.Trace.Emulator.ContractInstance (ContractInstanceState, addEventInstanceState,
                                                         emptyInstanceState, instContractState, instEvents,
                                                         instHandlersHistory)
import           Plutus.Trace.Emulator.Types            (ContractConstraints, ContractInstanceLog, ContractInstanceTag,
                                                         UserThreadMsg, _HandledRequest, cilMessage, cilTag,
                                                         toInstanceState)
import           Wallet.Emulator.Chain                  (ChainEvent (..), _TxnValidate, _TxnValidationFail)
import           Wallet.Emulator.ChainIndex             (_AddressStartWatching)
import           Wallet.Emulator.MultiAgent             (EmulatorEvent, EmulatorTimeEvent, chainEvent, chainIndexEvent,
                                                         eteEvent, instanceEvent, userThreadEvent, walletClientEvent)
import           Wallet.Emulator.NodeClient             (_TxSubmit)
import           Wallet.Emulator.Wallet                 (Wallet, walletAddress)
import qualified Wallet.Rollup                          as Rollup
import           Wallet.Rollup.Types                    (AnnotatedTx)

type EmulatorEventFold a = Fold EmulatorEvent a

-- | A fold over emulator events that can fail with 'EmulatorFoldErr'
type EmulatorEventFoldM effs a = FoldM (Eff effs) EmulatorEvent a

-- | Transactions that failed to validate
failedTransactions :: Maybe ValidationPhase -> EmulatorEventFold [(TxId, Tx, ValidationError, [ScriptValidationEvent])]
failedTransactions phase = preMapMaybe (preview (eteEvent . chainEvent . _TxnValidationFail) >=> filterPhase phase) L.list
    where
        filterPhase Nothing (_, i, t, v, e)   = Just (i, t, v, e)
        filterPhase (Just p) (p', i, t, v, e) = if p == p' then Just (i, t, v, e) else Nothing

-- | Transactions that were validated
validatedTransactions :: EmulatorEventFold [(TxId, Tx, [ScriptValidationEvent])]
validatedTransactions = preMapMaybe (preview (eteEvent . chainEvent . _TxnValidate)) L.list

-- | All scripts that are run during transaction validation
scriptEvents :: EmulatorEventFold [ScriptValidationEvent]
scriptEvents = preMapMaybe (preview (eteEvent . chainEvent) >=> getEvent) (concat <$> L.list) where
    getEvent :: ChainEvent -> Maybe [ScriptValidationEvent]
    getEvent = \case
        TxnValidate _ _ es           -> Just es
        TxnValidationFail _ _ _ _ es -> Just es
        SlotAdd _                    -> Nothing

-- | The state of a contract instance, recovered from the emulator log.
instanceState ::
    forall w s e a effs.
    ( ContractConstraints s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs (Maybe (ContractInstanceState w s e a))
instanceState con tag =
    let flt :: EmulatorEvent -> Maybe (Response JSON.Value)
        flt = preview (eteEvent . instanceEvent . filtered ((==) tag . view cilTag) . cilMessage . _HandledRequest)
        decode :: forall effs'. Member (Error EmulatorFoldErr) effs' => EmulatorEvent -> Eff effs' (Maybe (Response (Event s)))
        decode e = do
            case flt e of
                Nothing -> pure Nothing
                Just response -> case traverse (JSON.fromJSON @(Event s)) response of
                    JSON.Error e'   -> throwError $ JSONDecodingError e' response
                    JSON.Success e' -> pure (Just e')

    in preMapMaybeM decode $ L.generalize $ Fold (\s r -> s >>= addEventInstanceState r) (Just $ emptyInstanceState con) (fmap toInstanceState)

-- | The list of open requests of the contract instance at its latest iteration
instanceRequests ::
    forall w s e a effs.
    ( ContractConstraints s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs [Request (Handlers s)]
instanceRequests con = fmap g . instanceState con where
    g = fromMaybe [] . fmap (State.unRequests . _requests . instContractState)

-- | The unbalanced transactions generated by the contract instance.
instanceTransactions ::
    forall w s e a effs.
    ( ContractConstraints s
    , HasWriteTx s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs [UnbalancedTx]
instanceTransactions con = fmap g . instanceState con where
    g = fromMaybe [] . fmap (concat . fmap (mapMaybe (pendingTransaction @s . State.rqRequest)) . toList . instHandlersHistory)

-- | The reponses received by the contract instance
instanceResponses ::
    forall w s e a effs.
    ( ContractConstraints s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs [Response (Event s)]
instanceResponses con = fmap (fromMaybe [] . fmap (toList . instEvents)) . instanceState con

-- | Accumulated state of the contract instance
instanceAccumState ::
    forall w s e a effs.
    ( ContractConstraints s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs w
instanceAccumState con = fmap (maybe mempty (_observableState . instContractState)) . instanceState con

-- | The log messages produced by the contract instance.
instanceLog :: ContractInstanceTag -> EmulatorEventFold [EmulatorTimeEvent ContractInstanceLog]
instanceLog tag =
    let flt :: EmulatorEvent -> Maybe (EmulatorTimeEvent ContractInstanceLog)
        flt = traverse (preview (instanceEvent . filtered ((==) tag . view cilTag)))
    in preMapMaybe flt L.list

-- | Log and error messages produced by the main (user) thread in the emulator
userLog :: EmulatorEventFold [EmulatorTimeEvent UserThreadMsg]
userLog =
    let flt :: EmulatorEvent -> Maybe (EmulatorTimeEvent UserThreadMsg)
        flt = traverse (preview userThreadEvent)
    in preMapMaybe flt L.list

data Outcome e a =
    Done a
    -- ^ The contract finished without errors and produced a result
    | NotDone
    -- ^ The contract is waiting for more input.
    | Failed e
    -- ^ The contract failed with an error.
    deriving (Eq, Show)

fromResumableResult :: ResumableResult w e i o a -> Outcome e a
fromResumableResult = either Failed (maybe NotDone Done) . _finalState

-- | The final state of the instance
instanceOutcome ::
    forall w s e a effs.
    ( ContractConstraints s
    , Member (Error EmulatorFoldErr) effs
    , Monoid w
    )
    => Contract w s e a
    -> ContractInstanceTag
    -> EmulatorEventFoldM effs (Outcome e a)
instanceOutcome con =
    fmap (fromMaybe NotDone . fmap (fromResumableResult . instContractState)) . instanceState con

-- | Unspent outputs at an address
utxoAtAddress :: Address -> EmulatorEventFold UtxoMap
utxoAtAddress addr =
    preMapMaybe (preview (eteEvent . chainEvent . _TxnValidate . _2 ))
    $ Fold (flip (AM.updateAddresses . Valid)) (AM.addAddress addr mempty) (view (AM.fundsAt addr))

-- | The total value of unspent outputs at an address
valueAtAddress :: Address -> EmulatorEventFold Value
valueAtAddress = fmap (foldMap (txOutValue . txOutTxOut)) . utxoAtAddress

-- | The funds belonging to a wallet
walletFunds :: Wallet -> EmulatorEventFold Value
walletFunds = valueAtAddress . walletAddress

-- | The fees paid by a wallet
walletFees :: Wallet -> EmulatorEventFold Value
walletFees w = fees <$> walletSubmittedFees <*> validatedTransactions <*> failedTransactions (Just Phase2)
    where
        fees submitted txsV txsF = findFees (\(i, _, _) -> i) submitted txsV <> findFees (\(i, _, _, _) -> i) submitted txsF
        findFees getId submitted = foldMap (\t -> fold (Map.lookup (getId t) submitted))
        walletSubmittedFees = L.handles (eteEvent . walletClientEvent w . _TxSubmit) L.map

-- | Whether the wallet is watching an address
walletWatchingAddress :: Wallet -> Address -> EmulatorEventFold Bool
walletWatchingAddress wllt addr =
    preMapMaybe (preview (eteEvent . chainIndexEvent wllt . _AddressStartWatching))
    $ L.any ((==) addr)

-- | Annotate the transactions that were validated by the node
annotatedBlockchain :: EmulatorEventFold [[AnnotatedTx]]
annotatedBlockchain =
    preMapMaybe (preview (eteEvent . chainEvent))
    $ Fold Rollup.handleChainEvent Rollup.initialState Rollup.getAnnotatedTransactions

-- | All chain events emitted by the node
chainEvents :: EmulatorEventFold [ChainEvent]
chainEvents = preMapMaybe (preview (eteEvent . chainEvent)) L.list

-- | All transactions that happened during the simulation
blockchain :: EmulatorEventFold [Block]
blockchain =
    let step (currentBlock, otherBlocks) = \case
            SlotAdd _                          -> ([], currentBlock : otherBlocks)
            TxnValidate _ txn _                -> (Valid txn : currentBlock, otherBlocks)
            TxnValidationFail Phase1 _ _   _ _ -> (currentBlock, otherBlocks)
            TxnValidationFail Phase2 _ txn _ _ -> (Invalid txn : currentBlock, otherBlocks)
        initial = ([], [])
        extract (currentBlock, otherBlocks) =
            reverse (currentBlock : otherBlocks)
    in preMapMaybe (preview (eteEvent . chainEvent))
        $ Fold step initial extract

-- | The list of all emulator events
emulatorLog :: EmulatorEventFold [EmulatorEvent]
emulatorLog = L.list

-- | Pretty-print each element into a new line.
renderLines :: forall a. Pretty a => Fold a Text
renderLines =
    let rnd = renderStrict . layoutPretty defaultLayoutOptions in
    dimap pretty (rnd . vsep) L.list

-- | An effectful 'Data.Maybe.mapMaybe' for 'FoldM'.
preMapMaybeM ::
    Monad m
    => (a -> m (Maybe b))
    -> FoldM m b r
    -> FoldM m a r
preMapMaybeM f (FoldM step begin done) = FoldM step' begin done where
    step' x a = do
        result <- f a
        case result of
            Nothing -> pure x
            Just a' -> step x a'

-- | 'Data.Maybe.mapMaybe' for 'Fold'.
preMapMaybe :: (a -> Maybe b) -> Fold b r -> Fold a r
preMapMaybe f (Fold step begin done) = Fold step' begin done where
    step' x a = case f a of
        Nothing -> x
        Just b  -> step x b

-- | Effectfully map the result of a 'FoldM'
postMapM ::
    Monad m
    => (b -> m c)
    -> FoldM m a b
    -> FoldM m a c
postMapM f (FoldM step begin done) = FoldM step begin (done >=> f)

data EmulatorFoldErr =
    JSONDecodingError String (Response JSON.Value)
    deriving stock (Eq, Ord, Show)
