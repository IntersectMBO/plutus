{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | State machine based generators for constructing mock blockchains for use in property-based testing.
module Wallet.Generators.Mockchain.StateMachine
    ( GeneratorModel(..)
    , initialBalances, chainKeys, transactionKeys, feeEstimator, userActions, userInvariant, initialUserState
    , wallets
    , UserAction(..)
    , Command (..)
    , forAllChains
    , check
    , checkAndRemember
    , update
    , defaultModel
    , initialTransaction
    )
where

import           GHC.Generics                  (Generic, Generic1)

import           Control.Lens                  hiding (Choice, elements, index, transform)
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Except
import           Control.Monad.State           hiding (State, state)

import           Data.Foldable
import qualified Data.Map                      as Map
import           Data.Set                      (Set)
import qualified Data.Set                      as Set

import           Ledger
import qualified Ledger.Ada                    as Ada
import           Ledger.Value                  as Value
import qualified Wallet.API                    as W
import           Wallet.Emulator
import           Wallet.Generators.Mockchain

import           Test.QuickCheck
import           Test.QuickCheck.Monadic       (monadic)
import           Test.StateMachine             hiding (Value, elem)
import qualified Test.StateMachine.Types       as SM
import           Test.StateMachine.Types.Rank2 hiding (fmap, traverse, (<$>))
import qualified Test.StateMachine.Types.Rank2 as SM


-- | Various parameters for generating and updating a random Mockchain.
data GeneratorModel a = GeneratorModel {
    _initialBalances  :: [(PubKey, Value)],
    -- ^ Value created at the beginning of the blockchain.
    _chainKeys        :: Set PubKey,
    -- ^ Public keys to be tracked by the blockchain.
    _transactionKeys  :: Set PubKey,
    -- ^ Public keys that are to be used for generating transactions.
    -- If a public key is not included in this set, the generator will never create transactions to or
    -- from it - this is useful to ensure that e.g. a certain wallet will always have enough coins for
    -- an user-specified transaction.
    _feeEstimator     :: FeeEstimator,
    -- ^ The estimator used to generate fees.
    _userActions      :: [Mockchain -> Gen (UserAction a)],
    -- ^ User-defined actions that may be generated while running the chain.
    -- These may or may not be run, but will always be run in the same order as they are listed.
    _initialUserState :: a,
    -- ^ Initial value for the user-defined state.
    _userInvariant    :: Maybe (EmulatorState -> a -> Logic)
    -- ^ An invariant to be checked after every command.
    }

-- | A user specified action that gets run on arbitrary user-specified state.
data UserAction a = Action
    { uaLabel         :: String
    -- ^ A label for displaying the action.
    , uaCommands      :: forall u . [Command a u]
    -- ^ The effect of this action on the Mockchain.
    , uaConcrete      :: a -> a
    -- ^ The effect of this action on the user-defined part of the state.
    , uaPostcondition :: EmulatorState -> a -> Logic
    -- ^ The postcondition of the action, to be checked immediately after applying it to the concrete state.
    }

instance Show (UserAction a) where
    show = uaLabel

-- | A simple constructor for actions that just check something in their postcondition.
check :: String -> (EmulatorState -> Logic) -> UserAction a
check msg prop = Action { uaLabel = msg, uaCommands = [], uaConcrete = id, uaPostcondition = const . prop }

-- | A simple constructor for actions that just check something in their postcondition and set
-- a flag to record that they have been executed.
checkAndRemember :: String -> (EmulatorState -> Logic) -> UserAction Bool
checkAndRemember msg prop = Action { uaLabel = msg
                                   , uaCommands = []
                                   , uaConcrete = const True
                                   , uaPostcondition = const . prop }

-- | A simple constructor for actions that just update some user-defined concrete state.
update :: String -> (a -> a) -> UserAction a
update msg f = Action { uaLabel = msg, uaCommands = [], uaConcrete = f, uaPostcondition = \_ _ -> Top }

data Command a (u :: * -> *) where
    Initialise  :: Command a u
    Transaction :: Wallet -> Tx -> Command a u
    Block       :: Command a u
    UserAction  :: UserAction a -> Command a u
    deriving (Show, Generic, Generic1)

data Response (u :: * -> *) where
    S :: Response Symbolic
    C :: EmulatorState -> Response Concrete

data State a (u :: * -> *) where
    Initial  :: GeneratorModel a -> State a u
    Symbolic :: GeneratorModel a -> Mockchain -> State a Symbolic
    Concrete :: EmulatorState -> a -> State a Concrete

instance Show (State a Symbolic) where
    show (Initial _)    = "Initial state"
    show (Symbolic _ m) = "Mockchain " ++ show m

makeLenses ''GeneratorModel

wallets :: GeneratorModel a -> [Wallet]
wallets = map (Wallet . getPubKey) . Set.toList . (^. chainKeys)


-- | A generator model with some sensible defaults.
defaultModel :: a -> GeneratorModel a
defaultModel initial =
    GeneratorModel
    { _initialBalances  = zip defaultKeys (repeat defaultInitialBalance)
    , _chainKeys        = Set.fromList defaultKeys
    , _transactionKeys  = Set.fromList defaultKeys
    , _userActions      = []
    , _initialUserState = initial
    , _feeEstimator     = defaultFeeEstimator
    , _userInvariant    = Nothing
    }
    where defaultFeeEstimator = constantFee 1
          defaultInitialBalance = Ada.adaValueOf 100000
          defaultKeys = PubKey <$> [1 .. 5]

-- | Generate a mockchain with an initial block
initialMockchain :: GeneratorModel a -> Mockchain
initialMockchain gm = emptyChain
                      & pendingTransactions .~ [fst $ initialTransaction $ gm^.initialBalances]
                      & currentSlot .~ 1

-- | A transaction with no inputs that forges some value (to be used at the
--   beginning of a blockchain)
initialTransaction :: [(PubKey, Value)] -> (Tx, [TxOut])
initialTransaction ib =
    let o = (uncurry $ flip pubKeyTxOut) <$> ib
        t = foldl' Value.plus Value.zero (snd <$> ib)
    in (Tx {
        txInputs = Set.empty,
        txOutputs = o,
        txForge = t,
        txFee = 0,
        txValidRange = W.intervalFrom 0
        }, o)

-- | A state machine for generating random blockchains.
-- The state machine operates as follows:
-- 1. A mockchain is created containing an initial transaction according to the model
-- 2. Commands are generated and executed sequentially against the abstract state (i.e. the mockchain). The
-- abstract state is used to make sure that e.g. generated transactions are valid.
-- 3. The sequence of commands is then executed against the concrete state, which consists of an 'EmulatorState'
-- and a piece of user-defined state of type @a@.
-- 4. After each step of the concrete run, user-specified invariants are checked (if they exist).
stateMachine :: (MonadEmulator m) => GeneratorModel a -> StateMachine (State a) (Command a) m Response
stateMachine gm = StateMachine
    { initModel = Initial gm
    , transition = transition
    , precondition = precondition
    , postcondition = postcondition
    , invariant = invariant gm
    , generator = generator
    , distribution = Nothing
    , shrinker = shrinker
    , semantics = semantics gm
    , mock = \_ _ -> pure S
    }

-- Our state machine doesn't have any invariants of its own, so the invariant is whatever the gm specifies.
invariant :: GeneratorModel a -> Maybe (State a Concrete -> Logic)
invariant gm = case gm^.userInvariant of
    Nothing -> Nothing
    Just f  -> Just $ \case
        Initial _ -> Top
        Concrete es a -> f es a

-- The default actions (blocks and transactions) have no postconditions. For user-defined actions, we
-- check their user-defined postcondition.
postcondition :: State a Concrete -> Command a Concrete -> Response Concrete -> Logic
postcondition (Concrete _ a) (UserAction Action {..}) (C es) = uaPostcondition es a
postcondition _ _ _                                          = Top

-- The transition function for our state machine.
transition :: State a u -> Command a u -> Response u -> State a u
transition (Initial gm) Initialise S             = Symbolic gm $ initialMockchain gm
transition (Initial gm) Initialise (C es)        = Concrete es $ gm ^. initialUserState
transition (Concrete _ a) (UserAction ua) (C es) = Concrete es (uaConcrete ua a)
transition (Concrete _ a) _ (C es)               = Concrete es a
transition (Symbolic gm mc) (Transaction _ tx) S = Symbolic gm $ submitTxn mc tx
transition (Symbolic gm mc) Block S              = Symbolic gm $ validatePending mc
transition (Symbolic gm mc) (UserAction ua) S    = foldl' (\st cmd -> transition st cmd S) s' (uaCommands ua)
    where s' = Symbolic (over userActions tail gm) mc
-- The following transitions can never appear due to the state machine precondition
transition (Initial _) _ _  = error "Internal error: non-initial transition from initial state"
transition _ Initialise _   = error "Internal error: initial transition from non-initial state"

-- The only precondition we require is that the only transition available from the initial state is
-- initialization - and vice-versa (otherwise shrinking could eliminate the initial transition).
-- Technically we don't need to specify that 'Initialise' can only be executed in the initial state,
-- since the generator ensures that it only appears at the beginning.
precondition :: State a Symbolic -> Command a Symbolic -> Logic
precondition (Initial _) Initialise = Top
precondition (Initial _) _          = Bot
precondition _ Initialise           = Bot
precondition _ _                    = Top

-- Generation of Mockchain actions.
-- At every step, an action is generated that is either:
--   * A new block
--   * A new transaction (either valid or invalid)
--   * The next user-specified action (if there remain user-specified actions to be executed)
generator :: State a Symbolic -> Maybe (Gen (Command a Symbolic))
generator (Initial _)      = Just $ pure Initialise
generator (Symbolic gm mc) = Just $ oneof $ block
                             -- We need to make sure there are at least some entries in the UTxO set to generate
                             -- transactions
                             : if not $ Map.null $ mc^.utxo
                                then [ validTransaction, invalidTransaction ] ++ userAction
                                else []
    where validTransaction =
              Transaction <$> genWallet <*> genValidTransaction keys keys mc (gm^.feeEstimator)
          invalidTransaction =
              Transaction <$> genWallet <*> genInvalidTransaction keys keys mc (gm^.feeEstimator)
          block = pure Block
          userAction = case gm^.userActions of
              []    -> []
              act:_ -> [ UserAction <$> act mc ]
          keys = Set.toList $ gm^.transactionKeys
          genWallet = elements $ wallets gm

-- A trivial shrinker for commands. As implemented here, it means that the only way to shrink an action is to
-- delete it entirely. This is reasonable, since Initialise and Block are atomic and there's no clear
-- "reasonable" way to shrink transactions that doesn't completely change them.
-- User actions could be extended to specify how they are to be shrunk, but this doesn't seem too useful.
shrinker :: State a Symbolic -> Command a Symbolic -> [Command a Symbolic]
shrinker _ Initialise        = []
shrinker _ (UserAction _)    = []
shrinker _ (Transaction _ _) = []
shrinker _ Block             = []

-- Concrete semantics (i.e. in 'MonadEmulator') for Mockchain commands.
semantics :: (MonadEmulator m) => GeneratorModel a -> Command a Concrete -> m (Response Concrete)
semantics gm command = do
    case command of
        Initialise             -> void $ processEmulated $ processPending >>= walletsNotifyBlock (wallets gm)
        Transaction w tx       -> void $ processEmulated $ walletAction w $ W.submitTxn tx
        Block                  -> void $ processEmulated $ processPending >>= walletsNotifyBlock (wallets gm)
        UserAction Action {..} -> forM_ uaCommands (semantics gm)
    gets C

-- | @forAllChains gm p@ tries to check whether every blockchain generated by @stateMachine gm@
-- (and the associated user-defined state) satisfies the property @p@.
-- It also checks that every user-specified postcondition and invariant holds at every point of the
-- execution.
forAllChains :: GeneratorModel a -> (EmulatorState -> a -> Property) -> Property
forAllChains model prop = forAllCommands machine (Just 20)
    $ \cmds -> monadic (ioProperty . flip evalStateT initialEmulatorState . (>>= failOnError) . runExceptT) $ do
    (_hist, state, res) <- runCommands machine cmds
    return $ case state of
        Initial _            -> property Discard
        (Concrete es result) -> res === Ok .&&. prop es result
    where
        initialEmulatorState = emulatorState' [fst $ initialTransaction $ model^.initialBalances]
        machine = stateMachine model
        failOnError (Right p)  = return p
        failOnError (Left err) = throwM err

instance Exception AssertionError

instance SM.Functor (Command a)
instance SM.Foldable (Command a)
instance SM.Traversable (Command a)

instance CommandNames (Command a)

deriving instance Show (Response u)

instance SM.Foldable Response where
    foldMap _ _ = mempty
