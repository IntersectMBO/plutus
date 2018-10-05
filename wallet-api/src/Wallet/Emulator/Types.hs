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
    Notification(..),
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownKeyPair,
    ownAddresses,
    blockHeight,
    -- ** Traces
    Trace,
    runTraceChain,
    runTraceTxPool,
    walletAction,
    walletRecvNotifications,
    walletNotifyBlock,
    walletsNotifyBlock,
    blockchainActions,
    assertion,
    assertOwnFunds,
    assertOwnFundsEq,
    setValidationData,
    -- * Emulator internals
    EmulatedWalletApi(..),
    handleNotifications,
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    chain,
    txPool,
    walletStates,
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
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe
import qualified Data.Set                  as Set
import qualified Data.Text                 as T
import           Lens.Micro
import           Prelude                   as P

import           Wallet.API                (KeyPair (..), WalletAPI (..), WalletAPIError (..), keyPair, pubKey,
                                            signature)
import           Wallet.UTXO               (Block, Blockchain, Height, Tx (..), TxIn (..), TxOut (..), TxOutRef (..),
                                            TxOutRef', ValidationData, Value, hashTx, pubKeyTxIn, pubKeyTxOut,
                                            txOutPubKey, unitValidationData, validTx)

-- agents/wallets
newtype Wallet = Wallet { getWallet :: Int }
    deriving (Show, Eq, Ord)

type TxPool = [Tx]

data Notification = BlockValidated Block
                  | BlockHeight Height
                  deriving (Show, Eq, Ord)

-- Wallet code

data WalletState = WalletState {
    walletStateKeyPair      :: KeyPair,
    walletStateOwnAddresses :: Map TxOutRef' Value, -- ^ Addresses locked by the public key of our key pair
    walletStateBlockHeight  :: Height -- ^  Height of the blockchain as far as the wallet is concerned
    }
    deriving (Show, Eq, Ord)

ownKeyPair :: Lens' WalletState KeyPair
ownKeyPair = lens g s where
    g = walletStateKeyPair
    s ws kp = ws { walletStateKeyPair = kp }

ownAddresses :: Lens' WalletState (Map TxOutRef' Value)
ownAddresses = lens g s where
    g = walletStateOwnAddresses
    s ws oa = ws { walletStateOwnAddresses = oa }

blockHeight :: Lens' WalletState Height
blockHeight = lens g s where
    g = walletStateBlockHeight
    s ws bh = ws { walletStateBlockHeight = bh }

-- | An empty wallet state with the public/private key pair for a wallet
emptyWalletState :: Wallet -> WalletState
emptyWalletState (Wallet i) = WalletState (keyPair i) Map.empty 0

-- manually records the list of transactions to be submitted
newtype EmulatedWalletApi a = EmulatedWalletApi { runEmulatedWalletApi :: (ExceptT WalletAPIError (StateT WalletState (Writer [Tx] ))) a }
    deriving (Functor, Applicative, Monad, MonadState WalletState, MonadWriter [Tx], MonadError WalletAPIError)

handleNotifications :: [Notification] -> EmulatedWalletApi ()
handleNotifications ns = pubKey <$> myKeyPair >>= \k -> mapM_ (go k) ns where
    go k = \case
            BlockHeight h -> modify (blockHeight .~ h)
            BlockValidated blck -> mapM_ (modify . update k) blck

    -- | Remove spent outputs and add unspent ones that can be unlocked with our key
    update k t@Tx{..} =
        over ownAddresses (`Map.difference` (Map.fromSet (const ()) $ Set.map txInRef txInputs))
        . over ownAddresses (`Map.union` (Map.fromList $ (mkUtxo $ hashTx t) <$> (filter (isOwn k) $ zip [0..] txOutputs)))
    mkUtxo tx (i, TxOut{..}) = (TxOutRef tx i, txOutValue)
    isOwn k = (==) (Just k) . txOutPubKey . snd

instance WalletAPI EmulatedWalletApi where
    submitTxn txn = tell [txn]

    myKeyPair = gets walletStateKeyPair

    createPaymentWithChange vl = do
        WalletState{..} <- get
        let total = getSum $ foldMap Sum walletStateOwnAddresses
            sig   = signature walletStateKeyPair
        if total < vl || Map.null walletStateOwnAddresses
        then throwError $ InsufficientFunds $ T.unwords ["Total:", T.pack $ show total, "expected:", T.pack $ show vl]
        else
            -- This is the coin selection algorithm
            -- TODO: Should be customisable
            let funds = P.takeWhile ((vl <) . snd)
                        $ maybe [] (uncurry (P.scanl (\t v -> second (+ snd v) t)))
                        $ uncons
                        $ Map.toList walletStateOwnAddresses
                ins   = Set.fromList (flip pubKeyTxIn sig . fst <$> funds)
                diff  = maximum (snd <$> funds) - vl
                out   = pubKeyTxOut diff (pubKey walletStateKeyPair) in

            pure (ins, out)

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
    -- | Change the data used to validate transactions.
    SetValidationData :: ValidationData -> Event n ()


-- Program is like Free, except it makes the Functor for us so we can have a nice GADT
type Trace = Op.Program (Event EmulatedWalletApi)

data EmulatorState = EmulatorState {
    emChain          :: Blockchain,
    emTxPool         :: TxPool,
    emWalletState    :: Map Wallet WalletState,
    emValidationData :: ValidationData -- ^ Value that will be used to validate transactions with scripts. Since we cannot generate this data at runtime, we need to set it manually here.
    } deriving (Show)

chain :: Lens' EmulatorState Blockchain
chain = lens g s where
    g = emChain
    s es ch = es { emChain = ch }

txPool :: Lens' EmulatorState TxPool
txPool = lens g s where
    g = emTxPool
    s es tp = es { emTxPool = tp }

walletStates :: Lens' EmulatorState  (Map Wallet WalletState)
walletStates = lens g s where
    g = emWalletState
    s es ws = es { emWalletState = ws }

validationData :: Lens' EmulatorState ValidationData
validationData = lens g s where
    g = emValidationData
    s es vd = es { emValidationData = vd }

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState {
    emChain = [],
    emTxPool = [],
    emWalletState = Map.empty,
    emValidationData = unitValidationData
    }

-- | Initialise the emulator state with a blockchain
emulatorState :: Blockchain -> EmulatorState
emulatorState bc = emptyEmulatorState { emChain = bc }

-- | Initialise the emulator state with a pool of pending transactions
emulatorState' :: TxPool -> EmulatorState
emulatorState' tp = emptyEmulatorState { emTxPool = tp }

type MonadEmulator m = (MonadState EmulatorState m, MonadError AssertionError m)

-- | Validate a transaction in the current emulator state
validateEm :: (MonadEmulator m) => Tx -> m (Maybe Tx)
validateEm txn = do
    EmulatorState{emChain=bc, emValidationData = vd} <- get
    pure $ if validTx vd txn bc then Just txn else Nothing

liftEmulatedWallet :: (MonadEmulator m) => Wallet -> EmulatedWalletApi a -> m ([Tx], Either WalletAPIError a)
liftEmulatedWallet wallet act = do
    emState <- get
    let walletState = fromMaybe (emptyWalletState wallet) $ Map.lookup wallet $ emWalletState emState
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
    Assertion a -> do
        s <- get
        case a s of
            Just err -> throwError err
            Nothing  -> pure ()
    SetValidationData d -> modify (set validationData d)

process :: (MonadState EmulatorState m, MonadError AssertionError m) => Trace a -> m a
process = interpretWithMonad eval

-- | Interact with a wallet
walletAction :: Wallet -> EmulatedWalletApi () -> Trace [Tx]
walletAction w = Op.singleton . WalletAction w

-- | Notify a wallet of blockchain events
walletRecvNotifications :: Wallet -> [Notification] -> Trace [Tx]
walletRecvNotifications w = Op.singleton . WalletRecvNotification w

-- | Notify a wallet that a block has been validated
walletNotifyBlock :: Wallet -> Block -> Trace [Tx]
walletNotifyBlock w = walletRecvNotifications w . pure . BlockValidated

-- | Notify a list of wallets that a block has been validated
walletsNotifyBlock :: [Wallet] -> Block -> Trace [Tx]
walletsNotifyBlock wls b = foldM (\ts w -> (ts ++) <$> walletNotifyBlock w b) [] wls

-- | Validate all pending transactions
blockchainActions :: Trace Block
blockchainActions = Op.singleton BlockchainActions

-- | Make an assertion about the emulator state
assertion :: Assertion -> Trace ()
assertion = Op.singleton . Assertion

-- | Make an assertion about the total value of funds owned by a wallet.
assertOwnFunds :: Wallet -> (Value -> Maybe T.Text) -> Trace ()
assertOwnFunds w p = assertion go where
    go s = case Map.lookup w $ emWalletState s of
                    Nothing -> Just $ AssertionError "Wallet not found"
                    Just ws -> AssertionError <$> p (getSum $ foldMap Sum $ walletStateOwnAddresses ws)

-- | Assert that the funds owned by a wallet are equal to an amount
assertOwnFundsEq :: Wallet -> Value -> Trace ()
assertOwnFundsEq w target = assertOwnFunds w pred where
    tshow :: Show a => a -> T.Text
    tshow = T.pack . show
    pred v
        | v == target = Nothing
        | otherwise   = Just $ T.unwords ["Funds in wallet", tshow w, "were", tshow v, ". Expected:", tshow target]

-- | Set the validation data (in PLC) used to validate transactions that consume
--   output from Pay-To-Script addresses.
setValidationData :: ValidationData -> Trace ()
setValidationData = Op.singleton . SetValidationData

-- | Run an emulator trace on a blockchain
runTraceChain :: Blockchain -> Trace a -> (Either AssertionError a, EmulatorState)
runTraceChain ch t = runState (runExceptT $ process t) emState where
    emState = emulatorState ch

-- | Run an emulator trace on an empty blockchain with a pool of pending transactions
runTraceTxPool :: TxPool -> Trace a -> (Either AssertionError a, EmulatorState)
runTraceTxPool tp t = runState (runExceptT $ process t) emState where
    emState = emulatorState' tp
