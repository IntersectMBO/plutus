{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Wallet.Emulator.Types(
    -- * Wallet API
    WalletAPI(..),
    Wallet(..),
    TxPool,
    Notification(..),
    -- * Emulator
    WalletState(..),
    emptyWalletState,
    EmulatedWalletApi(..),
    handleNotifications,
    Assertion,
    isValidated,
    AssertionError,
    Event(..),
    Trace,
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    MonadEmulator,
    validateEm,
    liftEmulatedWallet,
    eval,
    process
    ) where

import           Control.Monad.Except
import           Control.Monad.Operational as Op
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Map                  as Map
import           Data.Maybe
import           Data.Text                 as T

import           Wallet.UTXO               (Block, Blockchain, Tx (..), validTx)

-- agents/wallets
newtype Wallet = Wallet Int
    deriving (Show, Eq, Ord)

type TxPool = [Tx]

data Notification = BlockValidated Block
                  | BlockHeight Int
                  deriving (Show, Eq, Ord)

-- Wallet code

data WalletState = WalletState
    deriving (Show, Eq, Ord)

emptyWalletState :: WalletState
emptyWalletState = WalletState

-- manually records the list of transactions to be submitted
newtype EmulatedWalletApi a = EmulatedWalletApi { runEmulatedWalletApi :: StateT WalletState (Writer [Tx]) a }
    deriving (Functor, Applicative, Monad, MonadState WalletState, MonadWriter [Tx])

handleNotifications :: [Notification] -> EmulatedWalletApi ()
handleNotifications _ = return () -- TODO: Actually handle notifications

instance WalletAPI EmulatedWalletApi where
    submitTxn txn = tell [txn]

-- TODO: richer interface
class WalletAPI m where
    submitTxn :: Tx -> m ()

-- Emulator code

type Assertion = EmulatorState -> Maybe AssertionError
data AssertionError = AssertionError T.Text
    deriving Show

isValidated :: Tx -> Assertion
isValidated txn emState =
    if notElem txn (join $ emChain emState) then Just $ AssertionError $ "Txn not validated: " <> T.pack (show txn) else Nothing

-- | The type of events in the emulator. @n@ is the type (usually a monad) in which wallet actions
-- take place.
data Event n a where
    -- | An direct action performed by a wallet. Usually represents a "user action", as it is
    -- triggered externally.
    WalletAction :: Wallet -> n () -> Event n [Tx]
    -- | A wallet receiving some notifications, and reacting to them.
    WalletRecvNotification :: Wallet -> [Notification] -> Event n [Tx]
    -- | The blockchain performing actions, resulting in a validated block.
    BlockchainActions :: Event n Block
    -- | An assertion in the event stream, which can inspect the current state.
    Assertion :: Assertion -> Event n ()

-- Program is like Free, except it makes the Functor for us so we can have a nice GADT
type Trace = Op.Program (Event EmulatedWalletApi)

data EmulatorState = EmulatorState { emChain :: Blockchain, emTxPool :: TxPool, emWalletState :: Map Wallet WalletState }
    deriving (Show, Eq, Ord)

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState { emChain = [], emTxPool = [], emWalletState = Map.empty }

-- | Initialise the emulator state with a blockchain
emulatorState :: Blockchain -> EmulatorState
emulatorState bc = emptyEmulatorState { emChain = bc }

type MonadEmulator m = (MonadState EmulatorState m, MonadError AssertionError m)

-- | Validate a transaction in the current emulator state
validateEm :: (MonadEmulator m) => Tx -> m (Maybe Tx)
validateEm txn = do
    bc <- gets emChain
    pure $ case validTx txn bc of
        True  -> Just txn
        False -> Nothing

liftEmulatedWallet :: (MonadEmulator m) => Wallet -> EmulatedWalletApi a -> m ([Tx], a)
liftEmulatedWallet wallet act = do
    emState <- get
    let walletState = fromMaybe emptyWalletState $ Map.lookup wallet $ emWalletState emState
    let ((out, newState), txns) = runWriter $ runStateT (runEmulatedWalletApi act) walletState
    put emState {
        emTxPool = txns ++ emTxPool emState,
        emWalletState = Map.insert wallet newState $ emWalletState emState
        }
    pure (txns, out)

eval :: (MonadEmulator m) => Event EmulatedWalletApi a -> m a
eval = \case
    WalletAction wallet action -> fst <$> liftEmulatedWallet wallet action
    WalletRecvNotification wallet trigger -> fst <$> liftEmulatedWallet wallet (handleNotifications trigger)
    BlockchainActions -> do
        emState <- get
        processed <- forM (emTxPool emState) validateEm
        let validated = catMaybes processed
        let block = validated
        put emState {
            emChain = block : emChain emState,
            emTxPool = []
            }
        pure block
    Assertion assertion -> do
        s <- get
        case assertion s of
            Just err -> throwError err
            Nothing  -> pure ()

process :: (MonadState EmulatorState m, MonadError AssertionError m) => Trace a -> m a
process = interpretWithMonad eval
