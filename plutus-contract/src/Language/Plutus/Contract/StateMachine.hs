{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
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
    -- * Constructing the machine instance
    , SM.mkValidator
    , SM.mkStateMachine
    -- * Constructing the state machine client
    , mkStateMachineClient
    , defaultChooser
    -- * Running the state machine
    , runStep
    , runInitialise
    -- * Re-exports
    , Void
    ) where

import           Control.Lens
import           Control.Monad.Error.Lens
import           Data.Text                        (Text)
import qualified Data.Text                        as Text
import           Data.Void                        (absurd, Void)

import           Language.Plutus.Contract
import qualified Language.PlutusTx                as PlutusTx
import           Language.PlutusTx.StateMachine   (State (..), StateMachine (..), StateMachineInstance (..))
import qualified Language.PlutusTx.StateMachine   as SM
import           Ledger                           (Value)
import qualified Ledger
import           Ledger.AddressMap                (UtxoMap)
import           Ledger.Constraints               (ScriptLookups, TxConstraints (..), mustPayToTheScript)
import           Ledger.Constraints.OffChain      (UnbalancedTx)
import qualified Ledger.Constraints.OffChain      as Constraints
import           Ledger.Constraints.TxConstraints (InputConstraint (..), OutputConstraint (..))
import           Ledger.Crypto                    (pubKeyHash)
import           Ledger.Typed.Tx                  (TypedScriptTxOut (..))
import qualified Ledger.Typed.Tx                  as Typed

import qualified Wallet.Typed.StateMachine        as SM

-- $statemachine
-- To write your contract as a state machine you need
-- * Two types @state@ and @input@ for the state and inputs of the machine
-- * A 'SM.StateMachineInstance state input' describing the transitions and
--   checks of the state machine (this is the on-chain code)
-- * A 'StateMachineClient state input' with the state machine instance and
--   an allocation function
--
-- In many cases it is enough to define the transition function
-- @t :: (state, Value) -> input -> Maybe (PendingTxConstraints state)@ and use
-- 'mkStateMachine' and 'mkStateMachineClient' to get the client.
-- You can then use 'runInitialise' and 'runStep' to initialise and transition
-- the state machine. 'runStep' gets the current state from the utxo set and
-- makes the transition to the next state using the given input and taking care
-- of all payments.

data SMContractError s i =
    SMError (SM.SMError s i)
    | InvalidTransition s i
    | NonZeroValueAllocatedInFinalState
    | ChooserError Text
    deriving (Show)

makeClassyPrisms ''SMContractError

-- | Client-side definition of a state machine.
data StateMachineClient s i = StateMachineClient
    { scInstance :: SM.StateMachineInstance s i
    -- ^ The instance of the state machine, defining the machine's transitions,
    --   its final states and its check function.
    , scChooser  :: [SM.OnChainState s i] -> Either (SMContractError s i) (SM.OnChainState s i)
    -- ^ A function that chooses the relevant on-chain state, given a list of
    --   all potential on-chain states found at the contract address.
    }

-- | A state chooser function that fails if confronted with anything other
--   than exactly one output
defaultChooser ::
    forall state input
    . [SM.OnChainState state input]
    -> Either (SMContractError state input) (SM.OnChainState state input)
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

getOnChainState ::
    ( AsSMContractError e state i
    , PlutusTx.IsData state
    , HasUtxoAt schema)
    => StateMachineClient state i
    -> Contract schema e (SM.OnChainState state i, UtxoMap)
getOnChainState StateMachineClient{scInstance, scChooser} = do
    utxo <- utxoAt (SM.machineAddress scInstance)
    let states = SM.getStates scInstance utxo
    either (throwing _SMContractError) (\s -> pure (s, utxo)) (scChooser states)

-- | Tries to run one step of a state machine: If the /guard/ (the last argument) returns @'Nothing'@ when given the
-- unbalanced transaction to be submitted, the old state and the new step, the step is run and @'Right'@ the new state is returned.
-- If the guard returns @'Just' a@, @'Left' a@ is returned instead.
runGuardedStep ::
    forall a e state schema input.
    ( AsSMContractError e state input
    , AsContractError e
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasUtxoAt schema
    , HasWriteTx schema
    , HasOwnPubKey schema
    , HasTxConfirmation schema
    )
    => StateMachineClient state input
    -> input
    -> (UnbalancedTx -> state -> state -> Maybe a)
    -> Contract schema e (Either a state)
runGuardedStep smc input guard = do
    let StateMachineInstance{stateMachine} = scInstance smc
    (newConstraints, State{stateData=os}, State{stateData=ns, stateValue=v}, inp, lookups) <- mkStep smc input
    pk <- ownPubKey
    let lookups' = lookups { Constraints.slOwnPubkey = Just $ pubKeyHash pk }
        txConstraints =
            if smFinal stateMachine ns
                then newConstraints { txOwnInputs = [inp], txOwnOutputs = [] }
                else
                    let output = OutputConstraint{ocData = ns, ocValue = v}
                    in  newConstraints { txOwnInputs = [inp], txOwnOutputs = [output] }
    utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups' txConstraints)
    case guard utx os ns of
        Nothing -> do
            submitTxConfirmed utx
            pure $ Right ns
        Just a  -> pure $ Left a

-- | Run one step of a state machine, returning the new state.
runStep ::
    forall e state schema input.
    ( AsSMContractError e state input
    , AsContractError e
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
    -> Contract schema e state
runStep smc input =
    either absurd id <$> runGuardedStep smc input (\_ _ _ -> Nothing)

-- | Initialise a state machine
runInitialise ::
    forall e state schema input.
    ( AsContractError e
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasTxConfirmation schema
    , HasWriteTx schema
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> state
    -- ^ The initial state
    -> Value
    -- ^ The value locked by the contract at the beginning
    -> Contract schema e state
runInitialise StateMachineClient{scInstance} initialState initialValue = do
    let StateMachineInstance{validatorInstance} = scInstance
        tx = mustPayToTheScript initialState initialValue
    let lookups = Constraints.scriptInstanceLookups validatorInstance
    utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups tx)
    submitTxConfirmed utx
    pure initialState

type StateMachineTypedTx state input = (TxConstraints Void Void, State state, State state, InputConstraint input, ScriptLookups (StateMachine state input))

mkStep ::
    forall e state schema input.
    ( AsSMContractError e state input
    , HasUtxoAt schema
    , PlutusTx.IsData state
    )
    => StateMachineClient state input
    -> input
    -> Contract schema e (StateMachineTypedTx state input)
mkStep client@StateMachineClient{scInstance} input = do
    let StateMachineInstance{stateMachine=StateMachine{smTransition}, validatorInstance} = scInstance
    (onChainState, utxo) <- getOnChainState client
    let (TypedScriptTxOut{tyTxOutData=currentState, tyTxOutTxOut}, txOutRef) = onChainState
        oldState = State{stateData = currentState, stateValue = Ledger.txOutValue tyTxOutTxOut}

    case smTransition oldState input of
        Just (newConstraints, newState)  ->
            let lookups =
                    Constraints.scriptInstanceLookups validatorInstance
                    <> Constraints.unspentOutputs utxo
            in pure (newConstraints, oldState, newState, InputConstraint{icRedeemer=input, icTxOutRef = Typed.tyTxOutRefRef txOutRef }, lookups)
        Nothing -> throwing _InvalidTransition (currentState, input)
