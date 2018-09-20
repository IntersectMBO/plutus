{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Wallet.Emulator.Types where

import           Control.Monad.Except
import           Control.Monad.Operational as Op
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Map                  as Map
import           Data.Maybe
import           Data.Text                 as T

-- Basic types (should be replaced by "real" types later)

-- don’t care what these are, some data to allow typeclasses
data Tx = Tx Int
    deriving (Show, Eq, Ord)
-- agents/wallets
data Wallet = Wallet Int
    deriving (Show, Eq, Ord)

type Block = [Tx]
type Chain = [Block]
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
handleNotifications = undefined -- TODO

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

data EmulatorState = EmulatorState { emChain :: Chain, emTxPool :: TxPool, emWalletState :: Map Wallet WalletState }
    deriving (Show, Eq, Ord)

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState { emChain = [], emTxPool = [], emWalletState = Map.empty }

type MonadEmulator m = (MonadState EmulatorState m, MonadError AssertionError m)

-- TODO: actual validation
validate :: (MonadEmulator m) => Tx -> m (Maybe Tx)
validate txn = pure $ Just txn

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
        processed <- forM (emTxPool emState) validate
        let validated = catMaybes processed
        let block = validated
        put emState {
            emChain = block : emChain emState
            }
        pure block
    Assertion assertion -> do
        s <- get
        case assertion s of
            Just err -> throwError err
            Nothing  -> pure ()

process :: (MonadState EmulatorState m, MonadError AssertionError m) => Trace a -> m a
process = interpretWithMonad eval

-- Example

trace :: Trace ()
trace = do
    [txn] <- Op.singleton $ WalletAction (Wallet 1) $ submitTxn (Tx 1)
    _ <- Op.singleton $ BlockchainActions
    Op.singleton $ Assertion $ isValidated txn
