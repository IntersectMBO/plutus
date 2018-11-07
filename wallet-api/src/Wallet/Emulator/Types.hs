{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
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
    watchedAddresses,
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
import           Control.Monad.Operational as Op
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Bifunctor            (Bifunctor (..))
import           Data.List                 (uncons)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe
import qualified Data.Set                  as Set
import qualified Data.Text                 as T
import           GHC.Generics              (Generic)
import           Lens.Micro
import           Prelude                   as P
import           Servant.API               (FromHttpApiData, ToHttpApiData)

import           Data.Hashable             (Hashable)
import           Wallet.API                (KeyPair (..), WalletAPI (..), WalletAPIError (..), keyPair, pubKey,
                                            signature)
import           Wallet.UTXO               (Block, Blockchain, Height, Tx (..), TxIn (..), TxOut (..), TxOutRef (..),
                                            TxOutRef', Value, hashTx, height, pubKeyTxIn, pubKeyTxOut, Address', pubKeyAddress)
import qualified Wallet.UTXO.Index         as Index

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
    walletStateKeyPair      :: KeyPair,
    walletStateBlockHeight  :: Height, 
    -- ^  Height of the blockchain as far as the wallet is concerned
    walletStateWatchedAddresses :: Map Address' (Map TxOutRef' Value)
    -- ^ Addresses that we watch. For each address we keep the unspent transaction outputs and their values, so that we can use them in transactions.
    }
    deriving (Show, Eq, Ord)

ownKeyPair :: Lens' WalletState KeyPair
ownKeyPair = lens g s where
    g = walletStateKeyPair
    s ws kp = ws { walletStateKeyPair = kp }

ownAddress :: WalletState -> Address'
ownAddress = pubKeyAddress . pubKey . walletStateKeyPair

ownFunds :: Lens' WalletState (Map TxOutRef' Value)
ownFunds = lens g s where
    g ws = Map.findWithDefault Map.empty (ownAddress ws) $ walletStateWatchedAddresses ws
    s ws oa = over watchedAddresses (Map.alter (const $ Just oa) (ownAddress ws)) ws

blockHeight :: Lens' WalletState Height
blockHeight = lens g s where
    g = walletStateBlockHeight
    s ws bh = ws { walletStateBlockHeight = bh }

watchedAddresses :: Lens' WalletState (Map Address' (Map TxOutRef' Value))
watchedAddresses = lens g s where
    g = walletStateWatchedAddresses
    s ws oa = ws { walletStateWatchedAddresses = oa }

-- | An empty wallet state with the public/private key pair for a wallet, and the public key address
--   for that wallet as the sole member of `walletStateWatchedAddresses`
emptyWalletState :: Wallet -> WalletState
emptyWalletState (Wallet i) = WalletState kp 0 oa where
    oa = Map.singleton (pubKeyAddress $ pubKey kp) Map.empty
    kp = keyPair i

-- manually records the list of transactions to be submitted
newtype EmulatedWalletApi a = EmulatedWalletApi { runEmulatedWalletApi :: (ExceptT WalletAPIError (StateT WalletState (Writer [Tx] ))) a }
    deriving (Functor, Applicative, Monad, MonadState WalletState, MonadWriter [Tx], MonadError WalletAPIError)

handleNotifications :: [Notification] -> EmulatedWalletApi ()
handleNotifications = mapM_ go where
    go = \case
            BlockHeight h -> modify (blockHeight .~ h)
            BlockValidated blck -> mapM_ (modify . update) blck

    -- | Remove spent outputs and add unspent ones, for the addresses that we care about
    update t = over watchedAddresses (updateAddresses t)

-- | Update the list of watched addresses with the inputs and outputs of a new transaction. 
--   `updateAddresses` does not add or remove any keys from its second argument.
updateAddresses :: 
    Tx 
    -> Map Address' (Map TxOutRef' Value) 
    -> Map Address' (Map TxOutRef' Value)
updateAddresses tx utxo = Map.mapWithKey upd utxo where

    -- adds the newly produced outputs, and removed the consumed outputs, for an address
    upd adr mp = Map.union (produced adr) mp `Map.difference` consumed adr where

    -- The following definitions are necessary because there is a
    -- 1-n relationship between `Address'` and `TxOutRef'`, and because we cannot get the
    -- `Address'` a `TxOutRef'` refers to from that reference alone (so we need to get
    -- it from the map of all UTXOs that we care about: `knownAddresses`)
    
    -- The TxOutRefs consumed by the transaction, for a given address
    consumed :: Address' -> Map TxOutRef' ()
    consumed adr = maybe Map.empty (Map.fromSet (const ())) $ Map.lookup adr inputs

    -- The TxOutRefs produced by the transaction, for a given address
    produced :: Address' -> Map TxOutRef' Value
    produced adr = Map.findWithDefault Map.empty adr outputs
        
    -- Addresses of all known tx out references
    knownAddresses :: Map TxOutRef' Address'
    knownAddresses = Map.fromList
        $ (>>= \(a, outRefs) -> (\(rf, _) -> (rf, a)) <$> Map.toList outRefs)
        $ Map.toList utxo

    -- Outputs produced by the transaction
    outputs :: Map Address' (Map TxOutRef' Value)
    outputs = Map.fromListWith Map.union $ mkUtxo <$> zip [0..] (txOutputs tx)

    -- Inputs consumed by the transaction, index by address
    inputs :: Map Address' (Set.Set TxOutRef')
    inputs = Map.fromListWith Set.union
        $ fmap (fmap Set.singleton)
        $ fmap swap
        $ catMaybes
        $ fmap ((\a -> sequence (a, Map.lookup a knownAddresses)) . txInRef)
        $ Set.toList 
        $ txInputs tx

    swap (x, y) = (y, x)
    mkUtxo (i, TxOut{..}) = (txOutAddress, Map.singleton (TxOutRef h i) txOutValue)
    h = hashTx tx

instance WalletAPI EmulatedWalletApi where
    submitTxn txn = tell [txn]

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

    register _ _ = pure () -- TODO: Keep track of triggers in emulated wallet

    payToPublicKey v = pubKeyTxOut v . pubKey <$> myKeyPair


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
