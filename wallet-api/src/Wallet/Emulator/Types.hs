{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
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
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownKeyPair,
    ownFunds,
    addressMap,
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
    addBlocks,
    assertion,
    assertOwnFundsEq,
    -- * Emulator internals
    EmulatedWalletApi(..),
    handleNotifications,
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    chain,
    txPool,
    walletStates,
    index,
    MonadEmulator,
    validateEm,
    liftEmulatedWallet,
    evalEmulated,
    processEmulated
    ) where

import           Control.Monad.Except
import           Control.Monad.Operational  as Op hiding (view)
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Bifunctor             (Bifunctor (..))
import           Data.Foldable              (traverse_)
import           Data.List                  (uncons)
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe
import qualified Data.Set                   as Set
import qualified Data.Text                  as T
import           GHC.Generics               (Generic)
import           Lens.Micro
import           Lens.Micro.Extras          (view)
import           Prelude                    as P
import           Servant.API                (FromHttpApiData, ToHttpApiData)

import           Data.Hashable              (Hashable)
import           Wallet.API                 (EventTrigger (..), KeyPair (..), WalletAPI (..), WalletAPIError (..),
                                             addresses, checkTrigger, keyPair, pubKey, signature)
import qualified Wallet.Emulator.AddressMap as AM
import           Wallet.UTXO                (Address', Block, Blockchain, Height, Tx (..), TxOutRef', Value, height,
                                             pubKeyAddress, pubKeyTxIn, pubKeyTxOut, txOutAddress)
import qualified Wallet.UTXO.Index          as Index

-- agents/wallets
newtype Wallet = Wallet { getWallet :: Int }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData, Hashable, ToJSON, FromJSON)

type TxPool = [Tx]

data Notification = BlockValidated Block
                  | BlockHeight Height
                  deriving (Show, Eq, Ord)

-- Wallet code

data WalletState = WalletState {
    walletStateKeyPair          :: KeyPair,
    walletStateBlockHeight      :: Height,
    -- ^  Height of the blockchain as far as the wallet is concerned
    walletStateWatchedAddresses :: AM.AddressMap,
    -- ^ Addresses that we watch. For each address we keep the unspent transaction outputs and their values, so that we can use them in transactions.
    walletStateTriggers         :: Map EventTrigger (EmulatedWalletApi ())
    }

instance Show WalletState where
    showsPrec p (WalletState kp bh wa tr) = showParen (p > 10)
        (showString "WalletState"
            . showChar ' ' . showsPrec 10 kp
            . showChar ' ' . showsPrec 10 bh
            . showChar ' ' . showsPrec 10 wa
            . showChar ' ' . showsPrec 10 (Map.map (const ("<..>" :: String)) tr))

ownKeyPair :: Lens' WalletState KeyPair
ownKeyPair = lens g s where
    g = walletStateKeyPair
    s ws kp = ws { walletStateKeyPair = kp }

ownAddress :: WalletState -> Address'
ownAddress = pubKeyAddress . pubKey . walletStateKeyPair

ownFunds :: Lens' WalletState (Map TxOutRef' Value)
ownFunds = lens g s where
    g ws = fromMaybe Map.empty $ ws ^. addressMap . at (ownAddress ws)
    s ws utxo = ws & addressMap . at (ownAddress ws) ?~ utxo

blockHeight :: Lens' WalletState Height
blockHeight = lens g s where
    g = walletStateBlockHeight
    s ws bh = ws { walletStateBlockHeight = bh }

addressMap :: Lens' WalletState AM.AddressMap
addressMap = lens g s where
    g = walletStateWatchedAddresses
    s ws oa = ws { walletStateWatchedAddresses = oa }

triggers :: Lens' WalletState (Map EventTrigger (EmulatedWalletApi ()))
triggers = lens g s where
    g = walletStateTriggers
    s ws tr = ws { walletStateTriggers = tr }

-- | An empty wallet state with the public/private key pair for a wallet, and the public key address
--   for that wallet as the sole member of `walletStateWatchedAddresses`
emptyWalletState :: Wallet -> WalletState
emptyWalletState (Wallet i) = WalletState kp 0 oa Map.empty where
    oa = AM.addAddress ownAddr mempty
    kp = keyPair i
    ownAddr = pubKeyAddress $ pubKey kp

-- manually records the list of transactions to be submitted
newtype EmulatedWalletApi a = EmulatedWalletApi { runEmulatedWalletApi :: (ExceptT WalletAPIError (StateT WalletState (Writer [Tx] ))) a }
    deriving (Functor, Applicative, Monad, MonadState WalletState, MonadWriter [Tx], MonadError WalletAPIError)

handleNotifications :: [Notification] -> EmulatedWalletApi ()
handleNotifications = mapM_ (updateState >=> runTriggers)  where
    updateState = \case
            BlockHeight h -> modify (blockHeight .~ h)
            BlockValidated blck -> mapM_ (modify . update) blck >> modify (blockHeight %~ succ)

    runTriggers _ = do
        h <- gets (view blockHeight)
        values <- gets (AM.values . view addressMap)
        trg <- gets (view triggers)

        traverse_ snd
            $ filter fst
            $ over _1 (checkTrigger h values)
            <$> Map.toList trg

    -- | Remove spent outputs and add unspent ones, for the addresses that we care about
    update t = over addressMap (AM.updateAddresses t)

instance WalletAPI EmulatedWalletApi where
    submitTxn txn =
        let adrs = txOutAddress <$> txOutputs txn in
        modify (over addressMap (AM.addAddresses adrs)) >>
        tell [txn]

    myKeyPair = gets walletStateKeyPair

    createPaymentWithChange vl = do
        ws <- get
        let fnds = ws ^. ownFunds
            total = getSum $ foldMap Sum fnds
            kp = walletStateKeyPair ws
            sig   = signature kp
        if total < vl || Map.null fnds
        then throwError $ InsufficientFunds $ T.unwords ["Total:", T.pack $ show total, "expected:", T.pack $ show vl]
        else
            -- This is the coin selection algorithm
            -- TODO: Should be customisable
            let funds = P.takeWhile ((vl <) . snd)
                        $ maybe [] (uncurry (P.scanl (\t v -> second (+ snd v) t)))
                        $ uncons
                        $ Map.toList fnds
                ins   = Set.fromList (flip pubKeyTxIn sig . fst <$> funds)
                diff  = maximum (snd <$> funds) - vl
                out   = pubKeyTxOut diff (pubKey kp) in

            pure (ins, out)

    register tr action =
        modify (over triggers (Map.insertWith (>>) tr action))
        >> modify (over addressMap (AM.addAddresses (addresses tr)))

-- Emulator code

data Assertion
  = IsValidated Tx
  | OwnFundsEqual Wallet Value

newtype AssertionError = AssertionError T.Text
    deriving Show

assert :: (MonadEmulator m) => Assertion -> m ()
assert (IsValidated txn)            = isValidated txn
assert (OwnFundsEqual wallet value) = ownFundsEqual wallet value

ownFundsEqual :: (MonadEmulator m) => Wallet -> Value -> m ()
ownFundsEqual wallet value = do
  es <- get
  ws <- case Map.lookup wallet $ emWalletState es of
        Nothing -> throwError $ AssertionError "Wallet not found"
        Just ws -> pure ws
  let total = getSum $ foldMap Sum $ ws ^. ownFunds
  if value == total
    then pure ()
    else throwError . AssertionError $ T.unwords ["Funds in wallet", tshow wallet, "were", tshow total, ". Expected:", tshow value]
  where
    tshow :: Show a => a -> T.Text
    tshow = T.pack . show

isValidated :: (MonadEmulator m) => Tx -> m ()
isValidated txn = do
    emState <- get
    if notElem txn (join $ emChain emState)
      then throwError $ AssertionError $ "Txn not validated: " <> T.pack (show txn)
      else pure ()

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
type Trace m = Op.Program (Event m)

data EmulatorState = EmulatorState {
    emChain       :: Blockchain,
    emTxPool      :: TxPool,
    emWalletState :: Map Wallet WalletState,
    emIndex       :: Index.UtxoIndex
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

index :: Lens' EmulatorState Index.UtxoIndex
index = lens g s where
    g = emIndex
    s es i = es { emIndex = i }

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState {
    emChain = [],
    emTxPool = [],
    emWalletState = Map.empty,
    emIndex = Index.empty
    }

-- | Initialise the emulator state with a blockchain
emulatorState :: Blockchain -> EmulatorState
emulatorState bc = emptyEmulatorState { emChain = bc, emIndex = Index.initialise bc }

-- | Initialise the emulator state with a pool of pending transactions
emulatorState' :: TxPool -> EmulatorState
emulatorState' tp = emptyEmulatorState { emTxPool = tp }

type MonadEmulator m = (MonadState EmulatorState m, MonadError AssertionError m)

-- | Validate a transaction in the current emulator state
validateEm :: EmulatorState -> Tx -> Maybe Tx
validateEm EmulatorState{emIndex=idx, emChain = ch} txn =
    let h = height ch
        result = Index.runValidation (Index.validateTransaction h txn) idx in
    either (const Nothing) (const $ Just txn) result

liftEmulatedWallet :: (MonadState EmulatorState m) => Wallet -> EmulatedWalletApi a -> m ([Tx], Either WalletAPIError a)
liftEmulatedWallet wallet act = do
    emState <- get
    let walletState = fromMaybe (emptyWalletState wallet) $ Map.lookup wallet $ emWalletState emState
    let ((out, newState), txns) = runWriter $ runStateT (runExceptT (runEmulatedWalletApi act)) walletState
    put emState {
        emTxPool = txns ++ emTxPool emState,
        emWalletState = Map.insert wallet newState $ emWalletState emState
        }
    pure (txns, out)

evalEmulated :: (MonadEmulator m) => Event EmulatedWalletApi a -> m a
evalEmulated = \case
    WalletAction wallet action -> fst <$> liftEmulatedWallet wallet action
    WalletRecvNotification wallet trigger -> fst <$> liftEmulatedWallet wallet (handleNotifications trigger)
    BlockchainActions -> do
        emState <- get
        let processed = validateEm emState <$> emTxPool emState
            validated = catMaybes processed
            block = validated
        put emState {
            emChain = block : emChain emState,
            emTxPool = [],
            emIndex = Index.insertBlock block (emIndex emState)
            }
        pure block
    Assertion a -> assert a

processEmulated :: (MonadEmulator m) => Trace EmulatedWalletApi a -> m a
processEmulated = interpretWithMonad evalEmulated

-- | Interact with a wallet
walletAction :: Wallet -> m () -> Trace m [Tx]
walletAction w = Op.singleton . WalletAction w

-- | Notify a wallet of blockchain events
walletRecvNotifications :: Wallet -> [Notification] -> Trace m [Tx]
walletRecvNotifications w = Op.singleton . WalletRecvNotification w

-- | Notify a wallet that a block has been validated
walletNotifyBlock :: Wallet -> Block -> Trace m [Tx]
walletNotifyBlock w = walletRecvNotifications w . pure . BlockValidated

-- | Notify a list of wallets that a block has been validated
walletsNotifyBlock :: [Wallet] -> Block -> Trace m [Tx]
walletsNotifyBlock wls b = foldM (\ts w -> (ts ++) <$> walletNotifyBlock w b) [] wls

-- | Validate all pending transactions
blockchainActions :: Trace m Block
blockchainActions = Op.singleton BlockchainActions

-- | Add a number of empty blocks to the blockchain, by performing
--   `blockchainActions` @n@ times.
addBlocks :: Int -> Trace m [Block]
addBlocks i = traverse (const blockchainActions) [1..i]

-- | Make an assertion about the emulator state
assertion :: Assertion -> Trace m ()
assertion = Op.singleton . Assertion

assertOwnFundsEq :: Wallet -> Value -> Trace m ()
assertOwnFundsEq wallet = assertion . OwnFundsEqual wallet

assertIsValidated :: Tx -> Trace m ()
assertIsValidated = assertion . IsValidated

-- | Run an emulator trace on a blockchain
runTraceChain :: Blockchain -> Trace EmulatedWalletApi a -> (Either AssertionError a, EmulatorState)
runTraceChain ch t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorState ch

-- | Run an emulator trace on an empty blockchain with a pool of pending transactions
runTraceTxPool :: TxPool -> Trace EmulatedWalletApi a -> (Either AssertionError a, EmulatorState)
runTraceTxPool tp t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorState' tp
