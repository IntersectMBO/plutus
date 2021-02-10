{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
module Language.Plutus.Contract.StateMachine(
    -- $statemachine
    StateMachineClient(..)
    , TxConstraints
    , SMContractError(..)
    , AsSMContractError(..)
    , SM.StateMachine(..)
    , SM.StateMachineInstance(..)
    , SM.State(..)
    , OnChainState
    , WaitingResult(..)
    , InvalidTransition(..)
    , TransitionResult(..)
    -- * Constructing the machine instance
    , SM.mkValidator
    , SM.mkStateMachine
    -- * Constructing the state machine client
    , mkStateMachineClient
    , defaultChooser
    , getStates
    -- * Running the state machine
    , runGuardedStep
    , runStep
    , runInitialise
    , getOnChainState
    , waitForUpdate
    , waitForUpdateUntil
    -- * Lower-level API
    , StateMachineTransition(..)
    , mkStep
    -- * Re-exports
    , Void
    ) where

import           Control.Lens
import           Control.Monad.Error.Lens
import           Data.Aeson                                    (FromJSON, ToJSON)
import           Data.Either                                   (rights)
import           Data.Map                                      (Map)
import qualified Data.Map                                      as Map
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text
import           Data.Void                                     (Void, absurd)
import           GHC.Generics                                  (Generic)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.StateMachine.OnChain (State (..), StateMachine (..),
                                                                StateMachineInstance (..))
import qualified Language.Plutus.Contract.StateMachine.OnChain as SM
import qualified Language.PlutusTx                             as PlutusTx
import           Ledger                                        (Slot, Value)
import qualified Ledger
import           Ledger.AddressMap                             (UtxoMap)
import           Ledger.Constraints                            (ScriptLookups, TxConstraints (..), mustPayToTheScript)
import           Ledger.Constraints.OffChain                   (UnbalancedTx)
import qualified Ledger.Constraints.OffChain                   as Constraints
import           Ledger.Constraints.TxConstraints              (InputConstraint (..), OutputConstraint (..))
import           Ledger.Crypto                                 (pubKeyHash)
import           Ledger.Tx                                     as Tx
import qualified Ledger.Typed.Scripts                          as Scripts
import           Ledger.Typed.Tx                               (TypedScriptTxOut (..))
import qualified Ledger.Typed.Tx                               as Typed

-- $statemachine
-- To write your contract as a state machine you need
-- * Two types @state@ and @input@ for the state and inputs of the machine
-- * A 'SM.StateMachineInstance state input' describing the transitions and
--   checks of the state machine (this is the on-chain code)
-- * A 'StateMachineClient state input' with the state machine instance and
--   an allocation function
--
-- In many cases it is enough to define the transition function
-- @t :: (state, Value) -> input -> Maybe (TxConstraints state)@ and use
-- 'mkStateMachine' and 'mkStateMachineClient' to get the client.
-- You can then use 'runInitialise' and 'runStep' to initialise and transition
-- the state machine. 'runStep' gets the current state from the utxo set and
-- makes the transition to the next state using the given input and taking care
-- of all payments.

type OnChainState s i = (Typed.TypedScriptTxOut (SM.StateMachine s i), Typed.TypedScriptTxOutRef (SM.StateMachine s i))

getStates
    :: forall s i
    . (PlutusTx.IsData s)
    => SM.StateMachineInstance s i
    -> Map TxOutRef TxOutTx
    -> [OnChainState s i]
getStates (SM.StateMachineInstance _ si) refMap =
    let lkp (ref, out) = do
            tref <- Typed.typeScriptTxOutRef (\r -> Map.lookup r refMap) si ref
            tout <- Typed.typeScriptTxOut si out
            pure (tout, tref)
    in rights $ fmap lkp $ Map.toList refMap

-- | An invalid transition
data InvalidTransition s i =
    InvalidTransition
        { tfState :: Maybe (State s) -- ^ Current state. 'Nothing' indicates that there is no current state.
        , tfInput :: i -- ^ Transition that was attempted but failed
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

-- | Result of an attempted transition
data TransitionResult s i =
    TransitionFailure (InvalidTransition s i) -- ^ The transition is not allowed
    | TransitionSuccess s -- ^ The transition is allowed and results in a new state

data SMContractError =
    ChooserError Text
    | SMCContractError ContractError
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''SMContractError

instance AsContractError SMContractError where
    _ContractError = _SMCContractError

-- | Client-side definition of a state machine.
data StateMachineClient s i = StateMachineClient
    { scInstance :: SM.StateMachineInstance s i
    -- ^ The instance of the state machine, defining the machine's transitions,
    --   its final states and its check function.
    , scChooser  :: [OnChainState s i] -> Either SMContractError (OnChainState s i)
    -- ^ A function that chooses the relevant on-chain state, given a list of
    --   all potential on-chain states found at the contract address.
    }

-- | A state chooser function that fails if confronted with anything other
--   than exactly one output
defaultChooser ::
    forall state input
    . [OnChainState state input]
    -> Either SMContractError (OnChainState state input)
defaultChooser [x] = Right x
defaultChooser xs  =
    let msg = "Found " <> show (length xs) <> " outputs, expected 1"
    in Left (ChooserError (Text.pack msg))

-- | A state machine client with the 'defaultChooser' function
mkStateMachineClient ::
    forall state input
    . SM.StateMachineInstance state input
    -> StateMachineClient state input
mkStateMachineClient inst =
    StateMachineClient
        { scInstance = inst
        , scChooser  = defaultChooser
        }

{-| Get the current on-chain state of the state machine instance.
    Return Nothing if there is no state on chain.
    Throws an @SMContractError@ if the number of outputs at the machine address is greater than one.
-}
getOnChainState ::
    ( AsSMContractError e
    , PlutusTx.IsData state
    , HasUtxoAt schema)
    => StateMachineClient state i
    -> Contract schema e (Maybe (OnChainState state i, UtxoMap))
getOnChainState StateMachineClient{scInstance, scChooser} = mapError (review _SMContractError) $ do
    utxo <- utxoAt (SM.machineAddress scInstance)
    let states = getStates scInstance utxo
    case states of
        [] -> pure Nothing
        _  -> case scChooser states of
                Left err    -> throwing _SMContractError err
                Right state -> pure $ Just (state, utxo)


data WaitingResult a
    = Timeout Slot
    | ContractEnded
    | WaitingResult a
  deriving (Show)


-- | Wait for the on-chain state of the state machine instance to change until timeoutSlot,
--   and return the new state, or return 'ContractEnded' if the instance has been
--   terminated. If 'waitForUpdate' is called before the instance has even
--   started then it returns the first state of the instance as soon as it
--   has started.
waitForUpdateUntil ::
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.IsData state
    , HasAwaitSlot schema
    , HasWatchAddress schema)
    => StateMachineClient state i
    -> Slot
    -> Contract schema e (WaitingResult state)
waitForUpdateUntil StateMachineClient{scInstance, scChooser} timeoutSlot = do
    let addr = Scripts.scriptAddress $ validatorInstance scInstance
        outputsMap :: Ledger.Tx -> Map.Map TxOutRef TxOutTx
        outputsMap t =
                fmap (\txout -> TxOutTx{txOutTxTx=t, txOutTxOut = txout})
                $ Map.filter ((==) addr . Tx.txOutAddress)
                $ Tx.unspentOutputsTx t
    let go sl = do
            txns <- acrTxns <$> addressChangeRequest AddressChangeRequest{acreqSlot = sl, acreqAddress=addr}
            if null txns && sl < timeoutSlot
                then go (succ sl)
                else pure txns

    initial <- currentSlot
    txns <- go initial
    slot <- currentSlot -- current slot, can be after timeout
    let states = txns >>= getStates scInstance . outputsMap
    case states of
        [] | slot < timeoutSlot -> pure ContractEnded
        [] | slot >= timeoutSlot -> pure $ Timeout timeoutSlot
        xs -> case scChooser xs of
                Left err         -> throwing _SMContractError err
                Right (state, _) -> pure $ WaitingResult (tyTxOutData state)


-- | Wait until the on-chain state of the state machine instance has changed,
--   and return the new state, or return 'Nothing' if the instance has been
--   terminated. If 'waitForUpdate' is called before the instance has even
--   started then it returns the first state of the instance as soon as it
--   has started.
waitForUpdate ::
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.IsData state
    , HasAwaitSlot schema
    , HasWatchAddress schema)
    => StateMachineClient state i
    -> Contract schema e (Maybe (OnChainState state i))
waitForUpdate StateMachineClient{scInstance, scChooser} = do
    let addr = Scripts.scriptAddress $ validatorInstance scInstance
        outputsMap :: Ledger.Tx -> Map TxOutRef TxOutTx
        outputsMap t =
                fmap (\txout -> TxOutTx{txOutTxTx=t, txOutTxOut = txout})
                $ Map.filter ((==) addr . Tx.txOutAddress)
                $ Tx.unspentOutputsTx t
    txns <- nextTransactionsAt addr
    let states = txns >>= getStates scInstance . outputsMap
    case states of
        [] -> pure Nothing
        xs -> either (throwing _SMContractError) (pure . Just) (scChooser xs)

-- | Tries to run one step of a state machine: If the /guard/ (the last argument) returns @'Nothing'@ when given the
-- unbalanced transaction to be submitted, the old state and the new step, the step is run and @'Right'@ the new state is returned.
-- If the guard returns @'Just' a@, @'Left' a@ is returned instead.
runGuardedStep ::
    forall a e state schema input.
    ( AsSMContractError e
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasUtxoAt schema
    , HasWriteTx schema
    , HasOwnPubKey schema
    , HasTxConfirmation schema
    )
    => StateMachineClient state input              -- ^ The state machine
    -> input                                       -- ^ The input to apply to the state machine
    -> (UnbalancedTx -> state -> state -> Maybe a) -- ^ The guard to check before running the step
    -> Contract schema e (Either a (TransitionResult state input))
runGuardedStep smc input guard = mapError (review _SMContractError) $ mkStep smc input >>= \case
    Right (StateMachineTransition{smtConstraints,smtOldState=State{stateData=os}, smtNewState=State{stateData=ns}, smtLookups}) -> do
        pk <- ownPubKey
        let lookups = smtLookups { Constraints.slOwnPubkey = Just $ pubKeyHash pk }
        utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups smtConstraints)
        case guard utx os ns of
            Nothing -> do
                submitTxConfirmed utx
                pure $ Right $ TransitionSuccess ns
            Just a  -> pure $ Left a
    Left e -> pure $ Right $ TransitionFailure e

-- | Run one step of a state machine, returning the new state.
runStep ::
    forall e state schema input.
    ( AsSMContractError e
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasUtxoAt schema
    , HasWriteTx schema
    , HasOwnPubKey schema
    , HasTxConfirmation schema
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> input
    -- ^ The input to apply to the state machine
    -> Contract schema e (TransitionResult state input)
runStep smc input =
    runGuardedStep smc input (\_ _ _ -> Nothing) >>= pure . \case
        Left a  -> absurd a
        Right a -> a

-- | Initialise a state machine
runInitialise ::
    forall e state schema input.
    ( PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasTxConfirmation schema
    , HasWriteTx schema
    , AsSMContractError e
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> state
    -- ^ The initial state
    -> Value
    -- ^ The value locked by the contract at the beginning
    -> Contract schema e state
runInitialise StateMachineClient{scInstance} initialState initialValue = mapError (review _SMContractError) $ do
    let StateMachineInstance{validatorInstance} = scInstance
        tx = mustPayToTheScript initialState initialValue
    let lookups = Constraints.scriptInstanceLookups validatorInstance
    utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups tx)
    submitTxConfirmed utx
    pure initialState

-- | Constraints & lookups needed to transition a state machine instance
data StateMachineTransition state input =
    StateMachineTransition
        { smtConstraints :: TxConstraints (Scripts.RedeemerType (StateMachine state input)) (Scripts.DatumType (StateMachine state input))
        , smtOldState    :: State state
        , smtNewState    :: State state
        , smtLookups     :: ScriptLookups (StateMachine state input)
        }

-- | Given a state machine client and an input to apply to
--   the client's state machine instance, compute the 'StateMachineTransition'
--   that can produce an actual transaction performing the transition
mkStep ::
    forall e state schema input.
    ( AsSMContractError e
    , HasUtxoAt schema
    , PlutusTx.IsData state
    )
    => StateMachineClient state input
    -> input
    -> Contract schema e (Either (InvalidTransition state input) (StateMachineTransition state input))
mkStep client@StateMachineClient{scInstance} input = do
    let StateMachineInstance{stateMachine=StateMachine{smTransition}, validatorInstance} = scInstance
    maybeState <- getOnChainState client
    case maybeState of
        Nothing -> pure $ Left $ InvalidTransition Nothing input
        Just (onChainState, utxo) -> do
            let (TypedScriptTxOut{tyTxOutData=currentState, tyTxOutTxOut}, txOutRef) = onChainState
                oldState = State{stateData = currentState, stateValue = Ledger.txOutValue tyTxOutTxOut}
                inputConstraints = [InputConstraint{icRedeemer=input, icTxOutRef = Typed.tyTxOutRefRef txOutRef }]

            case smTransition oldState input of
                Just (newConstraints, newState)  ->
                    let lookups =
                            Constraints.scriptInstanceLookups validatorInstance
                            <> Constraints.unspentOutputs utxo
                        outputConstraints =
                            if smFinal (SM.stateMachine scInstance) (stateData newState)
                                then []
                                else [OutputConstraint{ocDatum = stateData newState, ocValue = stateValue newState }]
                    in pure
                        $ Right
                        $ StateMachineTransition
                            { smtConstraints =
                                newConstraints
                                    { txOwnInputs = inputConstraints
                                    , txOwnOutputs = outputConstraints
                                    }
                            , smtOldState = oldState
                            , smtNewState = newState
                            , smtLookups = lookups
                            }
                Nothing -> pure $ Left $ InvalidTransition (Just oldState) input
