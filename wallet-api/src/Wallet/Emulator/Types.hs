{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
module Wallet.Emulator.Types(
    -- * Wallets
    Wallet(..),
    TxPool,
    -- * Emulator
    Assertion(OwnFundsEqual, IsValidated),
    assert,
    assertIsValidated,
    AssertionError,
    Event(..),
    Notification(..),
    EmulatorEvent(..),
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownKeyPair,
    ownFunds,
    addressMap,
    walletSlot,
    -- ** Traces
    Trace,
    runTraceChain,
    runTraceTxPool,
    evalTraceTxPool,
    execTraceTxPool,
    walletAction,
    walletRecvNotifications,
    walletNotifyBlock,
    walletsNotifyBlock,
    processPending,
    addBlocks,
    addBlocksAndNotify,
    assertion,
    assertOwnFundsEq,
    -- * Emulator internals
    MockWallet(..),
    handleNotifications,
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    chainNewestFirst,
    chainOldestFirst,
    txPool,
    walletStates,
    index,
    MonadEmulator,
    validateEm,
    validateBlock,
    ValidatedBlock(..),
    liftMockWallet,
    evalEmulated,
    processEmulated,
    runWalletActionAndProcessPending,
    fundsDistribution,
    emLog,
    selectCoin
    ) where

import           Control.Lens               hiding (index)
import           Control.Monad.Except
import           Control.Monad.Operational  as Op hiding (view)
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Newtype.Generics   (Newtype)
import           Data.Aeson                 (FromJSON, ToJSON, ToJSONKey)
import           Data.Bifunctor             (Bifunctor (..))
import           Data.Foldable              (foldl', traverse_)
import           Data.List                  (partition)
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe
import qualified Data.Set                   as Set
import qualified Data.Text                  as T
import           Data.Traversable           (for)
import           GHC.Generics               (Generic)
import           Prelude                    as P
import           Servant.API                (FromHttpApiData, ToHttpApiData)

import           Data.Hashable              (Hashable)
import           Ledger                     (Address, Block, Blockchain, Slot, Tx (..), TxId, TxOut, TxOutOf (..),
                                             TxOutRef, Value, hashTx, lastSlot, pubKeyAddress, pubKeyTxIn, pubKeyTxOut,
                                             txOutAddress)
import qualified Ledger.Index               as Index
import qualified Ledger.Interval            as Interval
import qualified Ledger.Value               as Value
import           Wallet.API                 (EventHandler (..), EventTrigger, KeyPair (..), WalletAPI (..),
                                             WalletAPIError (..), WalletDiagnostics (..), WalletLog (..), addresses,
                                             annTruthValue, getAnnot, keyPair, pubKey, signature)
import qualified Wallet.Emulator.AddressMap as AM

-- | A wallet in the emulator model.
newtype Wallet = Wallet { getWallet :: Int }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData, Hashable)
    deriving anyclass (Newtype, ToJSON, FromJSON, ToJSONKey)

-- | A pool of transactions which have yet to be validated.
type TxPool = [Tx]

-- | A notification sent to a wallet about a change in the ledger.
data Notification = BlockValidated Block -- ^ A new block has been validated.
                  | CurrentSlot Slot -- ^ The current slot has changed.
                  deriving (Show, Eq, Ord)

-- manually records the list of transactions to be submitted
-- | A mock wallet environment to allow pure testing of the wallet API. This type simply records the list of transactions
-- which are requested to be submitted.
newtype MockWallet a = MockWallet { runMockWallet :: (ExceptT WalletAPIError (StateT WalletState (Writer (WalletLog, [Tx])))) a }
    deriving newtype (Functor, Applicative, Monad, MonadState WalletState, MonadError WalletAPIError, MonadWriter (WalletLog, [Tx]))

instance WalletDiagnostics MockWallet where
    logMsg t = tell (WalletLog [t], [])

tellTx :: [Tx] -> MockWallet ()
tellTx tx = MockWallet $ tell (mempty, tx)

-- Wallet code

-- | The state used by the mock wallet environment.
data WalletState = WalletState {
    _ownKeyPair :: KeyPair,
    -- ^ User's 'KeyPair'.
    _walletSlot :: Slot,
    -- ^ Current slot as far as the wallet is concerned.
    _addressMap :: AM.AddressMap,
    -- ^ Addresses that we watch.
    _triggers   :: Map EventTrigger (EventHandler MockWallet)
    -- ^ Triggers registered by the user.
    }

instance Show WalletState where
    showsPrec p (WalletState kp bh wa tr) = showParen (p > 10)
        (showString "WalletState"
            . showChar ' ' . showsPrec 10 kp
            . showChar ' ' . showsPrec 10 bh
            . showChar ' ' . showsPrec 10 wa
            . showChar ' ' . showsPrec 10 (Map.map (const ("<..>" :: String)) tr))

makeLenses ''WalletState

-- | Get the user's own public-key address.
ownAddress :: WalletState -> Address
ownAddress = pubKeyAddress . pubKey . view ownKeyPair

-- | Get the funds available at the user's own public-key address.
ownFunds :: Lens' WalletState (Map TxOutRef TxOut)
ownFunds = lens g s where
    g ws = fromMaybe Map.empty $ ws ^. addressMap . at (ownAddress ws)
    s ws utxo = ws & addressMap . at (ownAddress ws) ?~ utxo


-- | An empty wallet state with the public/private key pair for a wallet, and the public-key address
-- for that wallet as the sole watched address.
emptyWalletState :: Wallet -> WalletState
emptyWalletState (Wallet i) = WalletState kp 0 oa Map.empty where
    oa = AM.addAddress ownAddr mempty
    kp = keyPair i
    ownAddr = pubKeyAddress $ pubKey kp

-- | Events produced by the blockchain emulator.
data EmulatorEvent =
    TxnSubmit TxId
    -- ^ A transaction has been added to the pool of pending transactions.
    | TxnValidate TxId
    -- ^ A transaction has been validated and added to the blockchain.
    | TxnValidationFail TxId Index.ValidationError
    -- ^ A transaction failed  to validate.
    | SlotAdd Slot
    -- ^ A slot has passed, and a block was added to the blockchain.
    | WalletError Wallet WalletAPIError
    -- ^ A 'WalletAPI' action produced an error.
    | WalletInfo Wallet T.Text
    -- ^ Debug information produced by a wallet.
    deriving (Eq, Ord, Show, Generic)

instance FromJSON EmulatorEvent
instance ToJSON EmulatorEvent

-- | Process a list of 'Notification's in the mock wallet environment.
handleNotifications :: [Notification] -> MockWallet ()
handleNotifications = mapM_ (updateState >=> runTriggers)  where
    updateState = \case
            CurrentSlot h -> modify (walletSlot .~ h)
            BlockValidated blck -> mapM_ (modify . update) blck >> modify (walletSlot %~ succ)

    runTriggers _ = do
        h <- gets (view walletSlot)
        adrs <- gets (view addressMap)
        trg <- gets (view triggers)

        let values = AM.values adrs
            annotate = annTruthValue h values

        let runIfTrue annotTr action =
                if getAnnot annotTr -- get the top-level annotation (just like `checkTrigger`, but here we need to hold on to the `annotTr` value to pass it to the handler)
                then runEventHandler action annotTr
                else pure ()

        traverse_ (uncurry runIfTrue)
            $ first annotate
            <$> Map.toList trg

    -- Remove spent outputs and add unspent ones, for the addresses that we care about
    update t = over addressMap (AM.updateAddresses t)

instance WalletAPI MockWallet where

    submitTxn txn =
        let adrs = txOutAddress <$> txOutputs txn in
        modifying addressMap (AM.addAddresses adrs) >>
        tellTx [txn]

    myKeyPair = use ownKeyPair

    createPaymentWithChange vl = do
        ws <- get
        let fnds = ws ^. ownFunds
            kp    = ws ^. ownKeyPair
            sig   = signature kp
        (spend, change) <- selectCoin (second txOutValue <$> Map.toList fnds) vl
        let
            txOutput = if Value.gt change Value.zero then Just (pubKeyTxOut change (pubKey kp)) else Nothing
            ins = Set.fromList (flip pubKeyTxIn sig . fst <$> spend)
        pure (ins, txOutput)

    register tr action =
        modify (over triggers (Map.insertWith (<>) tr action))
        >> modify (over addressMap (AM.addAddresses (addresses tr)))

    watchedAddresses = use addressMap

    startWatching = modifying addressMap . AM.addAddress

    slot = use walletSlot

-- | Given a set of @a@s with coin values, and a target value, select a number
-- of @a@ such that their total value is greater than or equal to the target.
selectCoin :: (MonadError WalletAPIError m)
    => [(a, Value)]
    -> Value
    -> m ([(a, Value)], Value)
selectCoin fnds vl =
        let
            total = foldl' Value.plus Value.zero $ fmap snd fnds
            fundsWithTotal = P.zip fnds (drop 1 $ P.scanl Value.plus Value.zero $ fmap snd fnds)
            err   = throwError
                    $ InsufficientFunds
                    $ T.unwords
                        [ "Total:", T.pack $ show total
                        , "expected:", T.pack $ show vl]
        in  if total `Value.lt` vl
            then err
            else
                let
                    fundsToSpend   = takeUntil (\(_, runningTotal) -> vl `Value.leq` runningTotal) fundsWithTotal
                    totalSpent     = case reverse fundsToSpend of
                                        []            -> Value.zero
                                        (_, total'):_ -> total'
                    change         = totalSpent `Value.minus` vl
                in pure (fst <$> fundsToSpend, change)

-- | Take elements from a list until the predicate is satisfied.
-- 'takeUntil' @p@ includes the first element for wich @p@ is true
-- (unlike @takeWhile (not . p)@).
takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil _ []       = []
takeUntil p (x:xs)
    | p x            = [x]
    | otherwise      = x : takeUntil p xs

-- Emulator code

-- | Assertions which will be checked during execution of the emulator.
data Assertion
  = IsValidated Tx -- ^ Assert that the given transaction is validated.
  | OwnFundsEqual Wallet Value -- ^ Assert that the funds belonging to a wallet's public-key address are equal to a value.

-- | An error emitted when an 'Assertion' fails.
newtype AssertionError = AssertionError T.Text
    deriving Show

-- | The type of events in the emulator. @n@ is the type (usually a monad implementing 'WalletAPI') in
-- which wallet actions take place.
data Event n a where
    -- | An direct action performed by a wallet. Usually represents a "user action", as it is
    -- triggered externally.
    WalletAction :: Wallet -> n () -> Event n [Tx]
    -- | A wallet receiving some notifications, and reacting to them.
    WalletRecvNotification :: Wallet -> [Notification] -> Event n [Tx]
    -- | The blockchain processing pending transactions, producing a new block
    --   from the valid ones and discarding the invalid ones.
    BlockchainProcessPending :: Event n Block
    -- | An assertion in the event stream, which can inspect the current state.
    Assertion :: Assertion -> Event n ()


-- Program is like Free, except it makes the Functor for us so we can have a nice GADT
-- | A series of 'Event's.
type Trace m = Op.Program (Event m)

-- | The state of the emulator itself.
data EmulatorState = EmulatorState {
    _chainNewestFirst :: Blockchain, -- ^ The current chain, with the newest transactions first in the list.
    _txPool           :: TxPool, -- ^ The pool of pending transactions.
    _walletStates     :: Map Wallet WalletState, -- ^ The state of each wallet.
    _index            :: Index.UtxoIndex, -- ^ The UTxO index, used for validation.
    _emulatorLog      :: [EmulatorEvent] -- ^ The emulator events, with the newest first.
    } deriving (Show)

makeLenses ''EmulatorState

-- | Get a map with the total value of each wallet's "own funds".
fundsDistribution :: EmulatorState -> Map Wallet Value
fundsDistribution = Map.map (Map.foldl' Value.plus Value.zero . fmap txOutValue . view ownFunds) . view walletStates

-- | Get the emulator log.
emLog :: EmulatorState -> [EmulatorEvent]
emLog = view emulatorLog

-- | Get the blockchain as a list of blocks, starting with the oldest (genesis)
--   block.
chainOldestFirst :: Lens' EmulatorState Blockchain
chainOldestFirst = chainNewestFirst . reversed

type MonadEmulator m = (MonadState EmulatorState m, MonadError AssertionError m)

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState {
    _chainNewestFirst = [],
    _txPool = [],
    _walletStates = Map.empty,
    _index = mempty,
    _emulatorLog = []
    }

-- | Issue an 'Assertion'.
assert :: (MonadEmulator m) => Assertion -> m ()
assert (IsValidated txn)            = isValidated txn
assert (OwnFundsEqual wallet value) = ownFundsEqual wallet value

-- | Issue an assertion that the funds for a given wallet have the given value.
ownFundsEqual :: (MonadEmulator m) => Wallet -> Value -> m ()
ownFundsEqual wallet value = do
    es <- get
    ws <- case Map.lookup wallet $ _walletStates es of
        Nothing -> throwError $ AssertionError "Wallet not found"
        Just ws -> pure ws
    let total = foldl' Value.plus Value.zero $ fmap txOutValue $ ws ^. ownFunds
    if value == total
    then pure ()
    else throwError . AssertionError $ T.unwords ["Funds in wallet", tshow wallet, "were", tshow total, ". Expected:", tshow value]
    where
    tshow :: Show a => a -> T.Text
    tshow = T.pack . show

-- | Issue an assertion that the given transaction has been validated.
isValidated :: (MonadEmulator m) => Tx -> m ()
isValidated txn = do
    emState <- get
    if notElem txn (join $ _chainNewestFirst emState)
        then throwError $ AssertionError $ "Txn not validated: " <> T.pack (show txn)
        else pure ()

-- | Initialise the emulator state with a blockchain.
emulatorState :: Blockchain -> EmulatorState
emulatorState bc = emptyEmulatorState
    & chainNewestFirst .~ bc
    & index .~ Index.initialise bc

-- | Initialise the emulator state with a pool of pending transactions.
emulatorState' :: TxPool -> EmulatorState
emulatorState' tp = emptyEmulatorState
    & txPool .~ tp

-- | Validate a transaction in the current emulator state.
validateEm :: MonadState Index.UtxoIndex m => Slot -> Tx -> m (Maybe Index.ValidationError)
validateEm h txn = do
    idx <- get
    let result = Index.runValidation (Index.validateTransaction h txn) idx
    case result of
        Left e -> pure (Just e)
        Right idx' -> do
            _ <- put idx'
            pure Nothing

-- | Lift an action that runs in 'MockWallet' into one that runs in an @MonadState EmulatorState@ monad by
-- running it for a particular 'Wallet'. This produces a list of transactions to be submitted, and either
-- a value or an error.
liftMockWallet :: (MonadState EmulatorState m) => Wallet -> MockWallet a -> m ([Tx], Either WalletAPIError a)
liftMockWallet wallet act = do
    emState <- get
    let walletState = fromMaybe (emptyWalletState wallet) $ Map.lookup wallet $ _walletStates emState
        ((out, newState), (msgs, txns)) = runWriter $ runStateT (runExceptT (runMockWallet act)) walletState
        events = (TxnSubmit . hashTx <$> txns) ++ (WalletInfo wallet <$> getWalletLog msgs)
    put emState {
        _txPool = txns ++ _txPool emState,
        _walletStates = Map.insert wallet newState $ _walletStates emState,
        _emulatorLog = events ++ _emulatorLog emState
        }
    pure (txns, out)

-- | Evaluate an 'Event' in a 'MonadEmulator' monad.
evalEmulated :: (MonadEmulator m) => Event MockWallet a -> m a
evalEmulated = \case
    WalletAction wallet action -> do
        (txns, result) <- liftMockWallet wallet action
        case result of
            Right _ -> pure txns
            Left err -> do
                _ <- modifying emulatorLog (WalletError wallet err :)
                pure txns
    WalletRecvNotification wallet trigger -> fst <$> liftMockWallet wallet (handleNotifications trigger)
    BlockchainProcessPending -> do
        emState <- get
        let
            currentSlot = lastSlot (_chainNewestFirst emState)
            idx         = _index emState
            pool        = _txPool emState
            (ValidatedBlock block events rest idx') =
                validateBlock currentSlot idx pool
            newChain = block : _chainNewestFirst emState
        put emState {
            _chainNewestFirst = newChain,
            _txPool = rest,
            _index = idx',
            _emulatorLog   = SlotAdd (lastSlot newChain) : events ++ _emulatorLog emState
            }
        pure block
    Assertion a -> assert a

-- | The result of validating a block.
data ValidatedBlock = ValidatedBlock
    { vlbValid  :: [Tx]
    -- ^ The transactions that have been validated in this block.
    , vlbEvents :: [EmulatorEvent]
    -- ^ Transaction validation events for the transactions in this block.
    , vlbRest   :: [Tx]
    -- ^ The transactions that haven't been validated because the current slot is
    --   not in their validation interval.
    , vlbIndex  :: Index.UtxoIndex
    -- ^ The updated UTxO index.
    }

-- | Validate a block given the current slot and UTxO index, returning the valid
--   transactions, success/failure events, remaining transactions and the
--   updated UTxO set.
validateBlock :: Slot -> Index.UtxoIndex -> [Tx] -> ValidatedBlock
validateBlock currentSlot idx txns =
    let
        -- Select those transactions that can be validated in the
        -- current slot
        (eligibleTxns, rest) = partition (canValidateNow currentSlot) txns

        -- Validate eligible transactions, updating the UTXO index each time
        (processed, idx') =
            flip runState idx $ for eligibleTxns $ \t -> do
                r <- validateEm currentSlot t
                pure (t, r)

        -- The new block contains all transaction that were validated
        -- successfully
        block = fst <$> filter (isNothing . snd) processed

        -- Also return an `EmulatorEvent` for each transaction that was
        -- processed
        events = uncurry mkEvent <$> processed

    in ValidatedBlock block events rest idx'

-- | Check whether the given transaction can be validated in the given slot.
canValidateNow :: Slot -> Tx -> Bool
canValidateNow currentSlot tx = $$(Interval.member) currentSlot (txValidRange tx)

mkEvent :: Tx -> Maybe Index.ValidationError -> EmulatorEvent
mkEvent t result =
    case result of
        Nothing  -> TxnValidate (hashTx t)
        Just err -> TxnValidationFail (hashTx t) err

processEmulated :: (MonadEmulator m) => Trace MockWallet a -> m a
processEmulated = interpretWithMonad evalEmulated

-- | Perform a wallet action as the given 'Wallet'.
walletAction :: Wallet -> m () -> Trace m [Tx]
walletAction w = Op.singleton . WalletAction w

-- | Notify the given 'Wallet' of some blockchain events.
walletRecvNotifications :: Wallet -> [Notification] -> Trace m [Tx]
walletRecvNotifications w = Op.singleton . WalletRecvNotification w

-- | Notify the given 'Wallet' that a block has been validated.
walletNotifyBlock :: Wallet -> Block -> Trace m [Tx]
walletNotifyBlock w = walletRecvNotifications w . pure . BlockValidated

-- | Notify a list of 'Wallet's that a block has been validated.
walletsNotifyBlock :: [Wallet] -> Block -> Trace m [Tx]
walletsNotifyBlock wls b = foldM (\ts w -> (ts ++) <$> walletNotifyBlock w b) [] wls

-- | Validate all pending transactions.
processPending :: Trace m Block
processPending = Op.singleton BlockchainProcessPending

-- | Add a number of empty blocks to the blockchain, by performing
--   'processPending' @n@ times.
addBlocks :: Int -> Trace m [Block]
addBlocks i = traverse (const processPending) [1..i]

-- | Add a number of blocks, notifying all the given 'Wallet's after each block.
addBlocksAndNotify :: [Wallet] -> Int -> Trace m ()
addBlocksAndNotify wallets i =
    traverse_ (\_ -> processPending >>= walletsNotifyBlock wallets) [1..i]

-- | Issue an 'Assertion'.
assertion :: Assertion -> Trace m ()
assertion = Op.singleton . Assertion

-- | Issue an assertion that the funds for a given wallet have the given value.
assertOwnFundsEq :: Wallet -> Value -> Trace m ()
assertOwnFundsEq wallet = assertion . OwnFundsEqual wallet

-- | Issue an assertion that the given transaction has been validated.
assertIsValidated :: Tx -> Trace m ()
assertIsValidated = assertion . IsValidated

-- | Run an 'Trace' on a blockchain.
runTraceChain :: Blockchain -> Trace MockWallet a -> (Either AssertionError a, EmulatorState)
runTraceChain ch t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorState ch

-- | Run a 'Trace' on an empty blockchain with a pool of pending transactions.
runTraceTxPool :: TxPool -> Trace MockWallet a -> (Either AssertionError a, EmulatorState)
runTraceTxPool tp t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorState' tp

-- | Evaluate a 'Trace' on an empty blockchain with a pool of pending
--   transactions and return the final value, discarding the final
--   'EmulatorState'.
evalTraceTxPool :: TxPool -> Trace MockWallet a -> Either AssertionError a
evalTraceTxPool pl = fst . runTraceTxPool pl

-- | Evaluate a 'Trace' on an empty blockchain with a pool of pending
--   transactions and return the final 'EmulatorState', discarding the final
--   value.
execTraceTxPool :: TxPool -> Trace MockWallet a -> EmulatorState
execTraceTxPool pl = snd . runTraceTxPool pl

-- | Run an action as a wallet, subsequently process any pending transactions and
-- notify wallets.
runWalletActionAndProcessPending :: [Wallet] -> Wallet -> m () -> Trace m [Tx]
runWalletActionAndProcessPending allWallets wallet action = do
  _ <- walletAction wallet action
  block <- processPending
  walletsNotifyBlock allWallets block
