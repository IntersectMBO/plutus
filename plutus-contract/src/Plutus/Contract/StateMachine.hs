{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
module Plutus.Contract.StateMachine(
    -- $statemachine
    StateMachineClient(..)
    , TxConstraints
    , SMContractError(..)
    , AsSMContractError(..)
    , SM.StateMachine(..)
    , SM.StateMachineInstance(..)
    , SM.State(..)
    , OnChainState(..)
    , WaitingResult(..)
    , InvalidTransition(..)
    , TransitionResult(..)
    , ThreadToken(..)
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
    , runGuardedStepWith
    , runStepWith
    , runInitialiseWith
    , getThreadToken
    , getOnChainState
    , waitForUpdate
    , waitForUpdateUntilSlot
    , waitForUpdateUntilTime
    , waitForUpdateTimeout
    -- * Lower-level API
    , StateMachineTransition(..)
    , mkStep
    -- * Re-exports
    , Void
    ) where

import           Control.Lens
import           Control.Monad.Error.Lens
import           Data.Aeson                                   (FromJSON, ToJSON)
import           Data.Default                                 (Default (def))
import           Data.Either                                  (rights)
import           Data.Map                                     (Map)
import qualified Data.Map                                     as Map
import           Data.Maybe                                   (listToMaybe, mapMaybe)
import qualified Data.Set                                     as Set
import           Data.Text                                    (Text)
import qualified Data.Text                                    as Text
import           Data.Void                                    (Void, absurd)
import           GHC.Generics                                 (Generic)
import           Ledger                                       (POSIXTime, Slot, TxOutRef, Value, scriptCurrencySymbol)
import qualified Ledger
import           Ledger.Constraints                           (ScriptLookups, TxConstraints (..), mintingPolicy,
                                                               mustMintValueWithRedeemer, mustPayToTheScript,
                                                               mustSpendPubKeyOutput)
import           Ledger.Constraints.OffChain                  (UnbalancedTx)
import qualified Ledger.Constraints.OffChain                  as Constraints
import           Ledger.Constraints.TxConstraints             (InputConstraint (..), OutputConstraint (..))
import           Ledger.Crypto                                (pubKeyHash)
import qualified Ledger.TimeSlot                              as TimeSlot
import qualified Ledger.Tx                                    as Tx
import qualified Ledger.Typed.Scripts                         as Scripts
import           Ledger.Typed.Tx                              (TypedScriptTxOut (..))
import qualified Ledger.Typed.Tx                              as Typed
import qualified Ledger.Value                                 as Value
import           Plutus.ChainIndex                            (ChainIndexTx (..))
import           Plutus.Contract
import           Plutus.Contract.StateMachine.MintingPolarity (MintingPolarity (..))
import           Plutus.Contract.StateMachine.OnChain         (State (..), StateMachine (..), StateMachineInstance (..))
import qualified Plutus.Contract.StateMachine.OnChain         as SM
import           Plutus.Contract.StateMachine.ThreadToken     (ThreadToken (..), curPolicy, ttOutRef)
import           Plutus.Contract.Wallet                       (getUnspentOutput)
import qualified PlutusTx
import           PlutusTx.Monoid                              (inv)

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

-- | Typed representation of the on-chain state of a state machine instance
data OnChainState s i =
    OnChainState
        { ocsTxOut    :: Typed.TypedScriptTxOut (SM.StateMachine s i) -- ^ Typed transaction output
        , ocsTxOutRef :: Typed.TypedScriptTxOutRef (SM.StateMachine s i) -- ^ Typed UTXO
        , ocsTx       :: ChainIndexTx -- ^ Transaction that produced the output
        }

getInput ::
    forall i.
    (PlutusTx.FromData i)
    => TxOutRef
    -> ChainIndexTx
    -> Maybe i
getInput outRef tx = do
    (_validator, Ledger.Redeemer r, _) <- listToMaybe $ mapMaybe Tx.inScripts $ filter (\Tx.TxIn{Tx.txInRef} -> outRef == txInRef) $ Set.toList $ _citxInputs tx
    PlutusTx.fromBuiltinData r

getStates
    :: forall s i
    . (PlutusTx.FromData s, PlutusTx.ToData s)
    => SM.StateMachineInstance s i
    -> Map Tx.TxOutRef (Tx.ChainIndexTxOut, ChainIndexTx)
    -> [OnChainState s i]
getStates (SM.StateMachineInstance _ si) refMap =
    let lkp (ref, (out, tx)) = do
            ocsTxOutRef <- Typed.typeScriptTxOutRef (\r -> fst <$> Map.lookup r refMap) si ref
            ocsTxOut <- Typed.typeScriptTxOut si ref out
            pure OnChainState{ocsTxOut, ocsTxOutRef, ocsTx = tx}
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
    | UnableToExtractTransition
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

-- | A state chooser function that searches for an output with the thread token
threadTokenChooser ::
    forall state input
    . Value
    -> [OnChainState state input]
    -> Either SMContractError (OnChainState state input)
threadTokenChooser val states =
    let hasToken OnChainState{ocsTxOut=TypedScriptTxOut{tyTxOutTxOut=Tx.TxOut{Tx.txOutValue}}} = val `Value.leq` txOutValue in
    case filter hasToken states of
        [x] -> Right x
        xs ->
            let msg = unwords ["Found", show (length xs), "outputs with thread token", show val, "expected 1"]
            in Left (ChooserError (Text.pack msg))

-- | A state machine client with the 'defaultChooser' function
mkStateMachineClient ::
    forall state input
    . SM.StateMachineInstance state input
    -> StateMachineClient state input
mkStateMachineClient inst =
    let threadTokenVal = SM.threadTokenValueOrZero inst
        scChooser = if Value.isZero threadTokenVal then defaultChooser else threadTokenChooser threadTokenVal
    in StateMachineClient
        { scInstance = inst
        , scChooser
        }

{-| Get the current on-chain state of the state machine instance.
    Return Nothing if there is no state on chain.
    Throws an @SMContractError@ if the number of outputs at the machine address is greater than one.
-}
getOnChainState ::
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    )
    => StateMachineClient state i
    -> Contract w schema e (Maybe (OnChainState state i, Map TxOutRef Tx.ChainIndexTxOut))
getOnChainState StateMachineClient{scInstance, scChooser} = mapError (review _SMContractError) $ do
    utxoTx <- utxosTxOutTxAt (SM.machineAddress scInstance)
    let states = getStates scInstance utxoTx
    case states of
        [] -> pure Nothing
        _  -> case scChooser states of
                Left err    -> throwing _SMContractError err
                Right state -> pure $ Just (state, fmap fst utxoTx)

-- | The outcome of 'waitForUpdateTimeout'
data WaitingResult t i s
    = Timeout t -- ^ The timeout happened before any change of the on-chain state was detected
    | ContractEnded ChainIndexTx i -- ^ The state machine instance ended
    | Transition ChainIndexTx i s -- ^ The state machine instance transitioned to a new state
    | InitialState ChainIndexTx s -- ^ The state machine instance was initialised
  deriving stock (Show,Generic,Functor)
  deriving anyclass (ToJSON, FromJSON)

-- | Wait for the on-chain state of the state machine instance to change until timeoutSlot,
--   and return the new state, or return 'ContractEnded' if the instance has been
--   terminated. If 'waitForUpdate' is called before the instance has even
--   started then it returns the first state of the instance as soon as it
--   has started.
waitForUpdateUntilSlot ::
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.FromData i
    )
    => StateMachineClient state i
    -> Slot
    -> Contract w schema e (WaitingResult Slot i state)
waitForUpdateUntilSlot client timeoutSlot = waitForUpdateTimeout client (isSlot timeoutSlot) >>= fmap (fmap (tyTxOutData . ocsTxOut)) . awaitPromise

-- | Same as 'waitForUpdateUntilSlot', but works with 'POSIXTime' instead.
waitForUpdateUntilTime ::
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.FromData i
    )
    => StateMachineClient state i
    -> POSIXTime
    -> Contract w schema e (WaitingResult Slot i state)
waitForUpdateUntilTime sm timeoutTime = waitForUpdateUntilSlot sm (TimeSlot.posixTimeToEnclosingSlot def timeoutTime)

-- | Wait until the on-chain state of the state machine instance has changed,
--   and return the new state, or return 'Nothing' if the instance has been
--   terminated. If 'waitForUpdate' is called before the instance has even
--   started then it returns the first state of the instance as soon as it
--   has started.
waitForUpdate ::
    forall state i w schema e.
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.FromData i
    )
    => StateMachineClient state i
    -> Contract w schema e (Maybe (OnChainState state i))
waitForUpdate client = waitForUpdateTimeout client never >>= awaitPromise >>= \case
    Timeout t        -> absurd t
    ContractEnded{}  -> pure Nothing
    InitialState _ r -> pure (Just r)
    Transition _ _ r -> pure (Just r)

-- | Construct a 'Promise' that waits for an update to the state machine's
--   on-chain state, or a user-defined timeout (whichever happens first).
waitForUpdateTimeout ::
    forall state i t w schema e.
    ( AsSMContractError e
    , AsContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.FromData i
    )
    => StateMachineClient state i -- ^ The state machine client
    -> Promise w schema e t -- ^ The timeout
    -> Contract w schema e (Promise w schema e (WaitingResult t i (OnChainState state i)))
waitForUpdateTimeout client@StateMachineClient{scInstance, scChooser} timeout = do
    currentState <- getOnChainState client
    let success = case currentState of
                    Nothing ->
                        -- There is no on-chain state, so we wait for an output to appear
                        -- at the address. Any output that appears needs to be checked
                        -- with scChooser'
                        let addr = Scripts.validatorAddress $ typedValidator scInstance in
                        promiseBind (utxoIsProduced addr) $ \txns -> do
                            outRefMaps <- traverse utxosTxOutTxFromTx txns
                            let produced = getStates @state @i scInstance (Map.fromList $ concat outRefMaps)
                            case scChooser produced of
                                Left e             -> throwing _SMContractError e
                                Right onChainState -> pure $ InitialState (ocsTx onChainState) onChainState
                    Just (OnChainState{ocsTxOutRef=Typed.TypedScriptTxOutRef{Typed.tyTxOutRefRef}, ocsTx}, _) ->
                        promiseBind (utxoIsSpent tyTxOutRefRef) $ \txn -> do
                            outRefMap <- Map.fromList <$> utxosTxOutTxFromTx txn
                            let newStates = getStates @state @i scInstance outRefMap
                                inp       = getInput tyTxOutRefRef txn
                            case (newStates, inp) of
                                ([], Just i) -> pure (ContractEnded ocsTx i)
                                (xs, Just i) -> case scChooser xs of
                                    Left e         -> throwing _SMContractError e
                                    Right newState -> pure (Transition ocsTx i newState)
                                _ -> throwing_ _UnableToExtractTransition
    pure $ select success (Timeout <$> timeout)

-- | Tries to run one step of a state machine: If the /guard/ (the last argument) returns @'Nothing'@ when given the
-- unbalanced transaction to be submitted, the old state and the new step, the step is run and @'Right'@ the new state is returned.
-- If the guard returns @'Just' a@, @'Left' a@ is returned instead.
runGuardedStep ::
    forall w a e state schema input.
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    )
    => StateMachineClient state input              -- ^ The state machine
    -> input                                       -- ^ The input to apply to the state machine
    -> (UnbalancedTx -> state -> state -> Maybe a) -- ^ The guard to check before running the step
    -> Contract w schema e (Either a (TransitionResult state input))
runGuardedStep = runGuardedStepWith mempty mempty

-- | Run one step of a state machine, returning the new state.
runStep ::
    forall w e state schema input.
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> input
    -- ^ The input to apply to the state machine
    -> Contract w schema e (TransitionResult state input)
runStep = runStepWith mempty mempty

-- | Create a thread token. The thread token contains a reference to an unspent output of the wallet,
-- so it needs to used with 'mkStateMachine' immediately, and the machine must be initialised,
-- to prevent the output from getting spent in the mean time.
getThreadToken :: AsSMContractError e => Contract w schema e ThreadToken
getThreadToken = mapError (review _SMContractError) $ do
    txOutRef <- getUnspentOutput
    pure $ ThreadToken txOutRef (scriptCurrencySymbol (curPolicy txOutRef))

-- | Initialise a state machine
runInitialise ::
    forall w e state schema input.
    ( PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    , AsSMContractError e
    )
    => StateMachineClient state input
    -- ^ The state machine
    -> state
    -- ^ The initial state
    -> Value
    -- ^ The value locked by the contract at the beginning
    -> Contract w schema e state
runInitialise = runInitialiseWith mempty mempty

-- | Constraints & lookups needed to transition a state machine instance
data StateMachineTransition state input =
    StateMachineTransition
        { smtConstraints :: TxConstraints input state
        , smtOldState    :: State state
        , smtNewState    :: State state
        , smtLookups     :: ScriptLookups (StateMachine state input)
        }

-- | Initialise a state machine and supply additional constraints and lookups for transaction.
runInitialiseWith ::
    forall w e state schema input.
    ( PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    , AsSMContractError e
    )
    => ScriptLookups (StateMachine state input)
    -- ^ Additional lookups
    -> TxConstraints input state
    -- ^ Additional constraints
    -> StateMachineClient state input
    -- ^ The state machine
    -> state
    -- ^ The initial state
    -> Value
    -- ^ The value locked by the contract at the beginning
    -> Contract w schema e state
runInitialiseWith customLookups customConstraints StateMachineClient{scInstance} initialState initialValue = mapError (review _SMContractError) $ do
    ownPK <- ownPubKey
    utxo <- utxosAt (Ledger.pubKeyAddress ownPK)
    let StateMachineInstance{stateMachine, typedValidator} = scInstance
        constraints = mustPayToTheScript initialState (initialValue <> SM.threadTokenValueOrZero scInstance)
            <> foldMap ttConstraints (smThreadToken stateMachine)
            <> customConstraints
        red = Ledger.Redeemer (PlutusTx.toBuiltinData (Scripts.validatorHash typedValidator, Mint))
        ttConstraints ThreadToken{ttOutRef} =
            mustMintValueWithRedeemer red (SM.threadTokenValueOrZero scInstance)
            <> mustSpendPubKeyOutput ttOutRef
        lookups = Constraints.typedValidatorLookups typedValidator
            <> foldMap (mintingPolicy . curPolicy . ttOutRef) (smThreadToken stateMachine)
            <> Constraints.unspentOutputs utxo
            <> customLookups
    utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups constraints)
    submitTxConfirmed utx
    pure initialState

-- | Run one step of a state machine, returning the new state. We can supply additional constraints and lookups for transaction.
runStepWith ::
    forall w e state schema input.
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    )
    => ScriptLookups (StateMachine state input)
    -- ^ Additional lookups
    -> TxConstraints input state
    -- ^ Additional constraints
    -> StateMachineClient state input
    -- ^ The state machine
    -> input
    -- ^ The input to apply to the state machine
    -> Contract w schema e (TransitionResult state input)
runStepWith lookups constraints smc input =
    runGuardedStepWith lookups constraints smc input (\_ _ _ -> Nothing) >>= pure . \case
        Left a  -> absurd a
        Right a -> a

-- | The same as 'runGuardedStep' but we can supply additional constraints and lookups for transaction.
runGuardedStepWith ::
    forall w a e state schema input.
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    , PlutusTx.ToData input
    )
    => ScriptLookups (StateMachine state input)    -- ^ Additional lookups
    -> TxConstraints input state                   -- ^ Additional constraints
    -> StateMachineClient state input              -- ^ The state machine
    -> input                                       -- ^ The input to apply to the state machine
    -> (UnbalancedTx -> state -> state -> Maybe a) -- ^ The guard to check before running the step
    -> Contract w schema e (Either a (TransitionResult state input))
runGuardedStepWith userLookups userConstraints smc input guard = mapError (review _SMContractError) $ mkStep smc input >>= \case
     Right StateMachineTransition{smtConstraints,smtOldState=State{stateData=os}, smtNewState=State{stateData=ns}, smtLookups} -> do
         pk <- ownPubKey
         let lookups = smtLookups { Constraints.slOwnPubkey = Just $ pubKeyHash pk }
         utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx (lookups <> userLookups) (smtConstraints <> userConstraints))
         case guard utx os ns of
             Nothing -> do
                 submitTxConfirmed utx
                 pure $ Right $ TransitionSuccess ns
             Just a  -> pure $ Left a
     Left e -> pure $ Right $ TransitionFailure e

-- | Given a state machine client and an input to apply to
--   the client's state machine instance, compute the 'StateMachineTransition'
--   that can produce an actual transaction performing the transition
mkStep ::
    forall w e state schema input.
    ( AsSMContractError e
    , PlutusTx.FromData state
    , PlutusTx.ToData state
    )
    => StateMachineClient state input
    -> input
    -> Contract w schema e (Either (InvalidTransition state input) (StateMachineTransition state input))
mkStep client@StateMachineClient{scInstance} input = do
    let StateMachineInstance{stateMachine, typedValidator} = scInstance
        StateMachine{smTransition} = stateMachine
    maybeState <- getOnChainState client
    case maybeState of
        Nothing -> pure $ Left $ InvalidTransition Nothing input
        Just (onChainState, utxo) -> do
            let OnChainState{ocsTxOut=TypedScriptTxOut{tyTxOutData=currentState, tyTxOutTxOut}, ocsTxOutRef} = onChainState
                oldState = State
                    { stateData = currentState
                      -- Hide the thread token value from the client code
                    , stateValue = Ledger.txOutValue tyTxOutTxOut <> inv (SM.threadTokenValueOrZero scInstance)
                    }
                inputConstraints = [InputConstraint{icRedeemer=input, icTxOutRef = Typed.tyTxOutRefRef ocsTxOutRef }]

            case smTransition oldState input of
                Just (newConstraints, newState)  ->
                    let isFinal = smFinal stateMachine (stateData newState)
                        lookups =
                            Constraints.typedValidatorLookups typedValidator
                            <> Constraints.unspentOutputs utxo
                            <> if isFinal then foldMap (mintingPolicy . curPolicy . ttOutRef) (smThreadToken stateMachine) else mempty
                        red = Ledger.Redeemer (PlutusTx.toBuiltinData (Scripts.validatorHash typedValidator, Burn))
                        unmint = if isFinal then mustMintValueWithRedeemer red (inv $ SM.threadTokenValueOrZero scInstance) else mempty
                        outputConstraints =
                            [ OutputConstraint
                                { ocDatum = stateData newState
                                  -- Add the thread token value back to the output
                                , ocValue = stateValue newState <> SM.threadTokenValueOrZero scInstance
                                }
                            | not isFinal ]
                    in pure
                        $ Right
                        $ StateMachineTransition
                            { smtConstraints =
                                (newConstraints <> unmint)
                                    { txOwnInputs = inputConstraints
                                    , txOwnOutputs = outputConstraints
                                    }
                            , smtOldState = oldState
                            , smtNewState = newState
                            , smtLookups = lookups
                            }
                Nothing -> pure $ Left $ InvalidTransition (Just oldState) input
