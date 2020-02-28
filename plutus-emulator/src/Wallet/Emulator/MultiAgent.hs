{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Wallet.Emulator.MultiAgent where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras
import           Control.Monad.Freer.State
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import qualified Data.Text                  as T
import           Data.Text.Prettyprint.Doc  hiding (annotate)
import           GHC.Generics               (Generic)
import           Ledger                     hiding (to, value)
import qualified Ledger.AddressMap          as AM
import qualified Ledger.Index               as Index
import qualified Wallet.API                 as WAPI
import qualified Wallet.Emulator.Chain      as Chain
import qualified Wallet.Emulator.ChainIndex as ChainIndex
import qualified Wallet.Emulator.NodeClient as NC
import qualified Wallet.Emulator.Wallet     as Wallet

-- | Assertions which will be checked during execution of the emulator.
data Assertion
  = IsValidated Tx -- ^ Assert that the given transaction is validated.
  | OwnFundsEqual Wallet.Wallet Value -- ^ Assert that the funds belonging to a wallet's public-key address are equal to a value.

-- | An error emitted when an 'Assertion' fails.
newtype AssertionError = GenericAssertion T.Text
    deriving (Show, Eq)
makeClassyPrisms ''AssertionError

-- | This lets people use 'T.Text' as their error type.
instance AsAssertionError T.Text where
    _AssertionError = prism' (T.pack . show) (const Nothing)

-- | Events produced by the blockchain emulator.
data EmulatorEvent =
    ChainEvent Chain.ChainEvent
    | ClientEvent Wallet.Wallet NC.NodeClientEvent
    | WalletEvent Wallet.Wallet Wallet.WalletEvent
    | ChainIndexEvent Wallet.Wallet ChainIndex.ChainIndexEvent
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty EmulatorEvent where
    pretty = \case
        ClientEvent _ e -> pretty e
        ChainEvent e -> pretty e
        WalletEvent _ e -> pretty e
        ChainIndexEvent _ e -> pretty e

chainEvent :: Prism' EmulatorEvent Chain.ChainEvent
chainEvent = prism' ChainEvent (\case { ChainEvent c -> Just c; _ -> Nothing })

walletClientEvent :: Wallet.Wallet -> Prism' EmulatorEvent NC.NodeClientEvent
walletClientEvent w = prism' (ClientEvent w) (\case { ClientEvent w' c | w == w' -> Just c; _ -> Nothing })

walletEvent :: Wallet.Wallet -> Prism' EmulatorEvent Wallet.WalletEvent
walletEvent w = prism' (WalletEvent w) (\case { WalletEvent w' c | w == w' -> Just c; _ -> Nothing })

chainIndexEvent :: Wallet.Wallet -> Prism' EmulatorEvent ChainIndex.ChainIndexEvent
chainIndexEvent w = prism' (ChainIndexEvent w) (\case { ChainIndexEvent w' c | w == w' -> Just c; _ -> Nothing })

-- | The type of actions in the emulator. @n@ is the type (usually a monad implementing 'WalletAPI') in
-- which wallet actions take place.
data MultiAgentEffect r where
    -- | An direct action performed by a wallet. Usually represents a "user action", as it is
    -- triggered externally.
    WalletAction :: Wallet.Wallet -> Eff '[Wallet.WalletEffect, Error WAPI.WalletAPIError, NC.NodeClientEffect, ChainIndex.ChainIndexEffect] r -> MultiAgentEffect r
    -- | An assertion in the event stream, which can inspect the current state.
    Assertion :: Assertion -> MultiAgentEffect ()

walletAction
    :: (Member MultiAgentEffect effs)
    => Wallet.Wallet
    -> Eff '[Wallet.WalletEffect, Error WAPI.WalletAPIError, NC.NodeClientEffect, ChainIndex.ChainIndexEffect] r
    -> Eff effs r
walletAction wallet act = send (WalletAction wallet act)

assertion :: (Member MultiAgentEffect effs) => Assertion -> Eff effs ()
assertion a = send (Assertion a)

-- | Issue an assertion that the funds for a given wallet have the given value.
assertOwnFundsEq :: (Member MultiAgentEffect effs) => Wallet.Wallet -> Value -> Eff effs ()
assertOwnFundsEq wallet = assertion . OwnFundsEqual wallet

-- | Issue an assertion that the given transaction has been validated.
assertIsValidated :: (Member MultiAgentEffect effs) => Tx -> Eff effs ()
assertIsValidated = assertion . IsValidated

-- | The state of the emulator itself.
data EmulatorState = EmulatorState {
    _chainState             :: Chain.ChainState,
    _walletStates           :: Map Wallet.Wallet Wallet.WalletState, -- ^ The state of each wallet.
    _walletClientStates     :: Map Wallet.Wallet NC.NodeClientState, -- ^ The state of each wallet's node client.
    _walletChainIndexStates :: Map Wallet.Wallet ChainIndex.ChainIndexState, -- ^ The state of each wallet's chain index
    _emulatorLog            :: [EmulatorEvent] -- ^ The emulator events, with the newest last.
    } deriving (Show)

makeLenses ''EmulatorState

walletState :: Wallet.Wallet -> Lens' EmulatorState Wallet.WalletState
walletState wallet = walletStates . at wallet . non (Wallet.emptyWalletState wallet)

walletClientState :: Wallet.Wallet -> Lens' EmulatorState NC.NodeClientState
walletClientState wallet = walletClientStates . at wallet . non NC.emptyNodeClientState

walletChainIndexState :: Wallet.Wallet -> Lens' EmulatorState ChainIndex.ChainIndexState
walletChainIndexState wallet = walletChainIndexStates . at wallet . non mempty

-- | Get the blockchain as a list of blocks, starting with the oldest (genesis)
--   block.
chainOldestFirst :: Lens' EmulatorState Blockchain
chainOldestFirst = chainState . Chain.chainNewestFirst . reversed

chainUtxo :: Getter EmulatorState AM.AddressMap
chainUtxo = chainState . Chain.chainNewestFirst . to AM.fromChain

-- | Get a map with the total value of each wallet's "own funds".
fundsDistribution :: EmulatorState -> Map Wallet.Wallet Value
fundsDistribution st =
    let fullState = view chainUtxo st
        wallets = Map.keys (_walletClientStates st)
        walletFunds = flip fmap wallets $ \w ->
            (w, foldMap (txOutValue . txOutTxOut) $ view (AM.fundsAt (Wallet.walletAddress w)) fullState)
    in Map.fromList walletFunds

-- | Get the emulator log.
emLog :: EmulatorState -> [EmulatorEvent]
emLog = view emulatorLog

emptyEmulatorState :: EmulatorState
emptyEmulatorState = EmulatorState {
    _chainState = Chain.emptyChainState,
    _walletStates = mempty,
    _walletClientStates = mempty,
    _walletChainIndexStates = mempty,
    _emulatorLog = mempty
    }

-- | Initialise the emulator state with a blockchain.
emulatorState :: Blockchain -> EmulatorState
emulatorState bc = emptyEmulatorState
    & chainState . Chain.chainNewestFirst .~ bc
    & chainState . Chain.index .~ Index.initialise bc

-- | Initialise the emulator state with a pool of pending transactions.
emulatorStatePool :: Chain.TxPool -> EmulatorState
emulatorStatePool tp = emptyEmulatorState
    & chainState . Chain.txPool .~ tp

-- | Initialise the emulator state with a single pending transaction that
--   creates the initial distribution of funds to public key addresses.
emulatorStateInitialDist :: Map PubKey Value -> EmulatorState
emulatorStateInitialDist mp = emulatorStatePool [tx] where
    tx = Tx
            { txInputs = mempty
            , txOutputs = uncurry (flip pubKeyTxOut) <$> Map.toList mp
            , txForge = foldMap snd $ Map.toList mp
            , txFee = mempty
            , txValidRange = WAPI.defaultSlotRange
            , txForgeScripts = mempty
            , txSignatures = mempty
            , txData = mempty
            }

type MultiAgentEffs = '[State EmulatorState, Error WAPI.WalletAPIError, Error AssertionError, Chain.ChainEffect]

handleMultiAgent
    :: forall effs. Members MultiAgentEffs effs
    => Eff (MultiAgentEffect ': effs) ~> Eff effs
handleMultiAgent = interpret $ \case
    -- TODO: catch, log, and rethrow wallet errors?
    WalletAction wallet act -> act
        & raiseEnd4
        & Wallet.handleWallet
        & subsume
        & NC.handleNodeClient
        & ChainIndex.handleChainIndex
        & interpret (handleZoomedState (walletState wallet))
        & interpret (handleZoomedWriter p1)
        & interpret (handleZoomedState (walletClientState wallet))
        & interpret (handleZoomedWriter p2)
        & interpret (handleZoomedState (walletChainIndexState wallet))
        & interpret (handleZoomedWriter p3)
        & interpret (writeIntoState emulatorLog)
        where
            p1 :: Prism' [EmulatorEvent] [Wallet.WalletEvent]
            p1 = below (walletEvent wallet)
            p2 :: Prism' [EmulatorEvent] [NC.NodeClientEvent]
            p2 = below (walletClientEvent wallet)
            p3 :: Prism' [EmulatorEvent] [ChainIndex.ChainIndexEvent]
            p3 = below (chainIndexEvent wallet)
    Assertion a -> assert a

-- | Issue an 'Assertion'.
assert :: (Members MultiAgentEffs effs) => Assertion -> Eff effs ()
assert (IsValidated txn)            = isValidated txn
assert (OwnFundsEqual wallet value) = ownFundsEqual wallet value

-- | Issue an assertion that the funds for a given wallet have the given value.
ownFundsEqual :: (Members MultiAgentEffs effs) => Wallet.Wallet -> Value -> Eff effs ()
ownFundsEqual wallet value = do
    es <- get
    let total = foldMap (txOutValue . txOutTxOut) $ es ^. chainUtxo . AM.fundsAt (Wallet.walletAddress wallet)
    if value == total
    then pure ()
    else throwError $ GenericAssertion $ T.unwords ["Funds in wallet", tshow wallet, "were", tshow total, ". Expected:", tshow value]
    where
    tshow :: Show a => a -> T.Text
    tshow = T.pack . show

-- | Issue an assertion that the given transaction has been validated.
isValidated :: (Members MultiAgentEffs effs) => Tx -> Eff effs ()
isValidated txn = do
    emState <- get
    if notElem txn (join $ emState ^. chainState . Chain.chainNewestFirst)
        then throwError $ GenericAssertion $ "Txn not validated: " <> T.pack (show txn)
        else pure ()
