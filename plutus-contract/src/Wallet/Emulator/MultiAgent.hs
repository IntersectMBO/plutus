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
import           Control.Monad.Freer.Log        (Log)
import qualified Control.Monad.Freer.Log        as Log
import           Control.Monad.Freer.State
import           Data.Aeson                     (FromJSON, ToJSON)
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import qualified Data.Text                      as T
import           Data.Text.Extras               (tshow)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                   (Generic)
import           Ledger                         hiding (to, value)
import qualified Ledger.AddressMap              as AM
import qualified Ledger.Index                   as Index
import qualified Wallet.API                     as WAPI
import qualified Wallet.Effects                 as Wallet
import qualified Wallet.Emulator.Chain          as Chain
import qualified Wallet.Emulator.ChainIndex     as ChainIndex
import qualified Wallet.Emulator.NodeClient     as NC
import qualified Wallet.Emulator.SigningProcess as SP
import qualified Wallet.Emulator.Wallet         as Wallet

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

type EmulatedWalletEffects =
        '[ Wallet.WalletEffect
         , Error WAPI.WalletAPIError
         , Wallet.NodeClientEffect
         , Wallet.ChainIndexEffect
         , Wallet.SigningProcessEffect
         , Log
         ]

type EmulatedWalletControlEffects =
        '[ NC.NodeClientControlEffect
         , ChainIndex.ChainIndexControlEffect
         , SP.SigningProcessControlEffect
         , Log
        ]

{- Note [Control effects]

Plutus contracts interact with the outside world through a number of different
effects. These effects are captured in 'EmulatedWalletEffects'. They are
supposed to be a realistic representation of the capabilities that contracts
will have in the real world, when the system is released.

In the tests we often want to simulate events that happened "outside of the
contract". For example: A new block is added to the chain, or a user takes the
transaction and emails it to another person to sign, before sending it to the
node. These kinds of events cannot be expressed in 'EmulatedWalletEffects',
because it would make the emulated wallet effects unrealistic - Plutus
contracts in the real world will not have the power to decide when a new block
gets added to the chain, or to control who adds their signature to a
transaction.

But in the emulated world of our unit tests we, the contract authors, would very
much like to have this power. That is why there is a second list of emulator
effects: 'EmulatedWalletControlEffects' are the of effects that only make sense
in the emulator, but not in the real world. With 'EmulatedWalletControlEffects'
we can control the blockchain and the lines of communication between the
emulated components.

By being clear about which of our (ie. the contract authors) actions
require the full power of 'EmulatedWalletControlEffects', we can be more
confident that our contracts will run in the real world, and not just in the
test environment. That is why there are two similar but different constructors
for 'MultiAgentEffect': 'WalletAction' is used for things that we will be able
to do in the real world, and 'WalletControlAction' is for everything else.

-}

-- | The type of actions in the emulator.
data MultiAgentEffect r where
    -- | A direct action performed by a wallet. Usually represents a "user action", as it is
    -- triggered externally.
    WalletAction :: Wallet.Wallet -> Eff EmulatedWalletEffects r -> MultiAgentEffect r
    -- | An action affecting the emulated parts of a wallet (only available in emulator - see note [Control effects].)
    WalletControlAction :: Wallet.Wallet -> Eff EmulatedWalletControlEffects r -> MultiAgentEffect r
    -- | An assertion in the event stream, which can inspect the current state.
    Assertion :: Assertion -> MultiAgentEffect ()

-- | Run an action in the context of a wallet (ie. agent)
walletAction
    :: (Member MultiAgentEffect effs)
    => Wallet.Wallet
    -> Eff EmulatedWalletEffects r
    -> Eff effs r
walletAction wallet act = send (WalletAction wallet act)

-- | Run a control action in the context of a wallet
walletControlAction
    :: (Member MultiAgentEffect effs)
    => Wallet.Wallet
    -> Eff EmulatedWalletControlEffects r
    -> Eff effs r
walletControlAction wallet = send . WalletControlAction wallet

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
    _chainState                 :: Chain.ChainState,
    _walletStates               :: Map Wallet.Wallet Wallet.WalletState, -- ^ The state of each wallet.
    _walletClientStates         :: Map Wallet.Wallet NC.NodeClientState, -- ^ The state of each wallet's node client.
    _walletChainIndexStates     :: Map Wallet.Wallet ChainIndex.ChainIndexState, -- ^ The state of each wallet's chain index
    _walletSigningProcessStates :: Map Wallet.Wallet SP.SigningProcess, -- ^ The wallet's signing process
    _emulatorLog                :: [EmulatorEvent] -- ^ The emulator events, with the newest last.
    } deriving (Show)

makeLenses ''EmulatorState

walletState :: Wallet.Wallet -> Lens' EmulatorState Wallet.WalletState
walletState wallet = walletStates . at wallet . non (Wallet.emptyWalletState wallet)

walletClientState :: Wallet.Wallet -> Lens' EmulatorState NC.NodeClientState
walletClientState wallet = walletClientStates . at wallet . non NC.emptyNodeClientState

walletChainIndexState :: Wallet.Wallet -> Lens' EmulatorState ChainIndex.ChainIndexState
walletChainIndexState wallet = walletChainIndexStates . at wallet . non mempty

signingProcessState :: Wallet.Wallet -> Lens' EmulatorState SP.SigningProcess
signingProcessState wallet = walletSigningProcessStates . at wallet . anon (SP.defaultSigningProcess wallet) (const False)

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
    _walletSigningProcessStates = mempty,
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

type MultiAgentEffs = '[State EmulatorState, Error WAPI.WalletAPIError, Error AssertionError, Chain.ChainEffect, Chain.ChainControlEffect]

handleMultiAgent
    :: forall effs. Members MultiAgentEffs effs
    => Eff (MultiAgentEffect ': effs) ~> Eff effs
handleMultiAgent = interpret $ \case
    -- TODO: catch, log, and rethrow wallet errors?
    WalletAction wallet act -> act
        & raiseEnd6
        & Wallet.handleWallet
        & subsume
        & NC.handleNodeClient
        & ChainIndex.handleChainIndex
        & SP.handleSigningProcess
        & interpret (handleZoomedWriter p4)
        & interpret (handleZoomedState (walletState wallet))
        & interpret (handleZoomedWriter p1)
        & interpret (handleZoomedState (walletClientState wallet))
        & interpret (handleZoomedWriter p2)
        & interpret (handleZoomedState (walletChainIndexState wallet))
        & interpret (handleZoomedWriter p3)
        & interpret (handleZoomedState (signingProcessState wallet))
        & interpret (writeIntoState emulatorLog)
        where
            p1 :: Prism' [EmulatorEvent] [Wallet.WalletEvent]
            p1 = below (walletEvent wallet)
            p2 :: Prism' [EmulatorEvent] [NC.NodeClientEvent]
            p2 = below (walletClientEvent wallet)
            p3 :: Prism' [EmulatorEvent] [ChainIndex.ChainIndexEvent]
            p3 = below (chainIndexEvent wallet)
            p4 :: Prism' [EmulatorEvent] [Log.LogMessage]
            p4 = below (walletEvent wallet . Wallet._WalletMsg)
    WalletControlAction wallet act -> act
        & raiseEnd4
        & NC.handleNodeControl
        & ChainIndex.handleChainIndexControl
        & SP.handleSigningProcessControl
        & interpret (handleZoomedWriter p4)
        & interpret (handleZoomedState (walletState wallet))
        & interpret (handleZoomedWriter p1)
        & interpret (handleZoomedState (walletClientState wallet))
        & interpret (handleZoomedWriter p2)
        & interpret (handleZoomedState (walletChainIndexState wallet))
        & interpret (handleZoomedWriter p3)
        & interpret (handleZoomedState (signingProcessState wallet))
        & interpret (writeIntoState emulatorLog)
        where
            p1 :: Prism' [EmulatorEvent] [Wallet.WalletEvent]
            p1 = below (walletEvent wallet)
            p2 :: Prism' [EmulatorEvent] [NC.NodeClientEvent]
            p2 = below (walletClientEvent wallet)
            p3 :: Prism' [EmulatorEvent] [ChainIndex.ChainIndexEvent]
            p3 = below (chainIndexEvent wallet)
            p4 :: Prism' [EmulatorEvent] [Log.LogMessage]
            p4 = below (walletEvent wallet . Wallet._WalletMsg)
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

-- | Issue an assertion that the given transaction has been validated.
isValidated :: (Members MultiAgentEffs effs) => Tx -> Eff effs ()
isValidated txn = do
    emState <- get
    if notElem txn (join $ emState ^. chainState . Chain.chainNewestFirst)
        then throwError $ GenericAssertion $ "Txn not validated: " <> T.pack (show txn)
        else pure ()
