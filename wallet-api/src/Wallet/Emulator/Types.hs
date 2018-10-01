{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Wallet.Emulator.Types(
    -- * Wallets
    Wallet(..),
    TxPool,
    -- * Emulator
    Assertion,
    isValidated,
    AssertionError,
    Event(..),
    WalletState(..),
    Notification(..),
    -- ** Traces
    Trace,
    runTrace,
    walletAction,
    walletRecvNotifications,
    blockchainActions,
    assertion,
    -- * Emulator internals
    emptyWalletState,
    EmulatedWalletApi(..),
    handleNotifications,
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
import           Data.Bifunctor            (Bifunctor (..))
import           Data.List                 (uncons)
import           Data.Map                  as Map
import           Data.Maybe
import qualified Data.Set                  as Set
import qualified Data.Text                 as T
import           Prelude                   as P

import           Wallet.API                (KeyPair (..), WalletAPI (..), WalletAPIError (..), keyPair, pubKey,
                                            signature)
import           Wallet.UTXO               (Block, Blockchain, Tx (..), TxOutRef', Value, pubKeyTxIn, pubKeyTxOut,
                                            validTx)

-- agents/wallets
newtype Wallet = Wallet Int
    deriving (Show, Eq, Ord)

type TxPool = [Tx]

data Notification = BlockValidated Block
                  | BlockHeight Int
                  deriving (Show, Eq, Ord)

-- Wallet code

data WalletState = WalletState {
    walletStateKeyPair      :: KeyPair,
    walletStateOwnAddresses :: Map TxOutRef' Value -- ^ Addresses locked by the public key of our key pair
    }
    deriving (Show, Eq, Ord)

emptyWalletState :: WalletState
emptyWalletState = WalletState (keyPair 0) Map.empty

-- manually records the list of transactions to be submitted
newtype EmulatedWalletApi a = EmulatedWalletApi { runEmulatedWalletApi :: (ExceptT WalletAPIError (StateT WalletState (Writer [Tx] ))) a }
    deriving (Functor, Applicative, Monad, MonadState WalletState, MonadWriter [Tx], MonadError WalletAPIError)

handleNotifications :: [Notification] -> EmulatedWalletApi ()
handleNotifications _ = return () -- TODO: Actually handle notifications

instance WalletAPI EmulatedWalletApi where
    submitTxn txn = tell [txn]

    myKeyPair = gets walletStateKeyPair

    createPayment vl = do
        WalletState{..} <- get
        let total = getSum $ foldMap Sum walletStateOwnAddresses
            sig   = signature walletStateKeyPair
        if total < vl || Map.null walletStateOwnAddresses
        then throwError $ InsufficientFunds $ T.unwords ["Total:", T.pack $ show total, "expected:", T.pack $ show vl]
        else return $ Set.fromList
                $ fmap (flip pubKeyTxIn sig . fst)
                -- This is the coin selection algorithm
                -- TODO: Should be customisable
                $ P.takeWhile ((>) vl . snd)
                $ maybe [] (uncurry (P.scanl (\t v -> second (+ snd v) t)))
                $ uncons
                $ Map.toList walletStateOwnAddresses

    register _ _ = pure () -- TODO: Keep track of triggers in emulated wallet

    payToPublicKey v = pubKeyTxOut v . pubKey <$> myKeyPair


-- Emulator code

type Assertion = EmulatorState -> Maybe AssertionError
newtype AssertionError = AssertionError T.Text
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
    pure $ if validTx txn bc then Just txn else Nothing

liftEmulatedWallet :: (MonadEmulator m) => Wallet -> EmulatedWalletApi a -> m ([Tx], Either WalletAPIError a)
liftEmulatedWallet wallet act = do
    emState <- get
    let walletState = fromMaybe emptyWalletState $ Map.lookup wallet $ emWalletState emState
    let ((out, newState), txns) = runWriter $ runStateT (runExceptT (runEmulatedWalletApi act)) walletState
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
    Assertion at -> do
        s <- get
        case at s of
            Just err -> throwError err
            Nothing  -> pure ()

process :: (MonadState EmulatorState m, MonadError AssertionError m) => Trace a -> m a
process = interpretWithMonad eval

-- | Interact with a wallet
walletAction :: Wallet -> EmulatedWalletApi () -> Trace [Tx]
walletAction w = Op.singleton . WalletAction w

-- | Notify a wallet of blockchain events
walletRecvNotifications :: Wallet -> [Notification] -> Trace [Tx]
walletRecvNotifications w = Op.singleton . WalletRecvNotification w

-- | Validate all pending transactions
blockchainActions :: Trace Block
blockchainActions = Op.singleton BlockchainActions

-- | Make an assertion about the emulator state
assertion :: Assertion -> Trace ()
assertion = Op.singleton . Assertion

-- | Run an emulator trace on a blockchain
runTrace :: Blockchain -> Trace a -> (Either AssertionError a, EmulatorState)
runTrace chain t = runState (runExceptT $ process t) emState where
    emState = emulatorState chain
