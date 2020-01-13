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
    , ValueAllocation(..)
    , SMContractError(..)
    , AsSMContractError(..)
    , SM.StateMachine(..)
    , SM.StateMachineInstance(..)
    -- * Constructing the machine instance
    , SM.mkValidator
    -- * Constructing the state machine client
    , mkStateMachineClient
    , defaultChooser
    -- * Running the state machine
    , runStep
    , runInitialise
    ) where

import           Control.Lens
import           Control.Monad                     (unless)
import           Control.Monad.Error.Lens
import           Data.Text                         (Text)
import qualified Data.Text                         as Text

import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx       as Tx
import qualified Language.Plutus.Contract.Typed.Tx as Tx
import qualified Language.PlutusTx                 as PlutusTx
import           Language.PlutusTx.StateMachine    (StateMachine (..), StateMachineInstance (..))
import qualified Language.PlutusTx.StateMachine    as SM
import           Ledger                            (Value)
import           Ledger.Typed.Tx                   (TypedScriptTxOut (..))
import qualified Ledger.Typed.Tx                   as Typed
import qualified Ledger.Value                      as Value

import qualified Wallet.Typed.StateMachine         as SM

-- $statemachine
-- To write your contract as a state machine you need
-- * Two types @state@ and @input@ for the state and inputs of the machine
-- * A 'SM.StateMachineInstance state input' describing the transitions and
--   checks of the state machine (this is the on-chain code)
-- * A 'StateMachineClient state input' with the state machine instance and
--   an allocation function
--
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

-- | Allocation of funds to outputs of the state machine transition transaction.
data ValueAllocation =
    ValueAllocation
        { vaOwnAddress    :: Value
        -- ^ How much should stay locked in the contract
        , vaOtherPayments :: UnbalancedTx
        -- ^ Any other payments
        }

instance Semigroup ValueAllocation where
    l <> r =
        ValueAllocation
            { vaOwnAddress = vaOwnAddress l <> vaOwnAddress r
            , vaOtherPayments = vaOtherPayments l <> vaOtherPayments r
            }

instance Monoid ValueAllocation where
    mappend = (<>)
    mempty  = ValueAllocation mempty mempty

-- | Client-side definition of a state machine.
data StateMachineClient s i = StateMachineClient
    { scInstance :: SM.StateMachineInstance s i
    -- ^ The instance of the state machine, defining the machine's transitions,
    --   its final states and its check function.
    , scPayments :: s -> i -> Value -> Maybe ValueAllocation
    -- ^ A function that determines the 'ValueAllocation' of each transition,
    --   given the value currently locked by the contract.
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
    -> (state -> input -> Value -> Maybe ValueAllocation)
    -> StateMachineClient state input
mkStateMachineClient inst payments =
    StateMachineClient
        { scInstance = inst
        , scPayments = payments
        , scChooser  = defaultChooser
        }

getOnChainState :: (AsSMContractError e state i, PlutusTx.IsData state, HasUtxoAt schema) => StateMachineClient state i -> Contract schema e (SM.OnChainState state i)
getOnChainState StateMachineClient{scInstance, scChooser} = do
    utxo <- utxoAt (SM.machineAddress scInstance)
    let states = SM.getStates scInstance utxo
    either (throwing _SMContractError) pure $ scChooser states

-- | Run one step of a state machine, returning the new state.
runStep ::
    forall e state schema input.
    ( AsSMContractError e state input
    , AsContractError e
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    , HasUtxoAt schema
    , HasWriteTx schema
    , HasTxConfirmation schema
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> input
    -- ^ The input to apply to the state machine
    -> Contract schema e state
runStep smc input = do
    -- the transaction returned by 'mkStep' includes an output with the payments
    -- to the script address, so we only need to deal with the 'vaOtherPayments'
    -- field of the value allocation here.
    (typedTx, newState, ValueAllocation{vaOtherPayments}) <- mkStep smc input
    let tx = case typedTx of
            (Typed.TypedTxSomeOuts tx') -> Tx.fromLedgerTx (Typed.toUntypedTx tx')
    submitTxConfirmed (tx <> vaOtherPayments)
    pure newState

-- | Initialise a state machine
runInitialise ::
    forall e state schema input.
    ( PlutusTx.IsData state
    , AsContractError e
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
        tx = Tx.makeScriptPayment validatorInstance initialValue initialState
    submitTxConfirmed tx
    pure initialState

mkStep ::
    forall e state schema input.
    ( AsSMContractError e state input
    , HasUtxoAt schema
    , PlutusTx.IsData state
    , PlutusTx.IsData input
    )
    => StateMachineClient state input
    -> input
    -> Contract schema e (Typed.TypedTxSomeOuts '[SM.StateMachine state input], state, ValueAllocation)
mkStep client@StateMachineClient{scInstance, scPayments} input = do
    let StateMachineInstance{stateMachine=StateMachine{smTransition, smFinal}, validatorInstance} = scInstance
    (TypedScriptTxOut{tyTxOutData=currentState}, txOutRef) <- getOnChainState client
    newState <- case smTransition currentState input of
        Just s  -> pure s
        Nothing -> throwing _InvalidTransition (currentState, input)

    let typedTxIn = Typed.makeTypedScriptTxIn @(SM.StateMachine state input) validatorInstance input txOutRef
        tx = Typed.TypedTxSomeOuts (Typed.addTypedTxIn typedTxIn Typed.baseTx)

    valueAllocation <-
        maybe (throwing _InvalidTransition (currentState, input)) pure
            $ scPayments currentState input (Typed.txInValue typedTxIn)

    finalTx <- if smFinal newState
               then do
                    unless (Value.isZero (vaOwnAddress valueAllocation)) (throwing_ _NonZeroValueAllocatedInFinalState)
                    pure tx
               else do
                    let output = Typed.makeTypedScriptTxOut validatorInstance newState (vaOwnAddress valueAllocation)
                        fullTx = Typed.addSomeTypedTxOut output tx
                    pure fullTx

    pure (finalTx, newState, valueAllocation)
