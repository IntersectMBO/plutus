{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Plutus.Contract.StateMachine.OnChain(
      StateMachine(..)
    , StateMachineInstance (..)
    , State(..)
    , mkStateMachine
    , machineAddress
    , mkValidator
    , threadTokenValueOrZero
    ) where

import           Data.Aeson                               (FromJSON, ToJSON)
import           Data.Void                                (Void)
import           GHC.Generics                             (Generic)
import           Ledger                                   (Address, ValidatorHash)
import           Ledger.Constraints
import           Ledger.Constraints.TxConstraints         (OutputConstraint (..))
import           Ledger.Contexts                          (ScriptContext (..), TxInInfo (..), findOwnInput, ownHash)
import           Ledger.Tx                                (TxOut (..))
import           Ledger.Typed.Scripts
import           Ledger.Value                             (Value, isZero)
import qualified PlutusTx
import           PlutusTx.Prelude                         hiding (check)
import qualified Prelude                                  as Haskell

import qualified Plutus.Contract.StateMachine.ThreadToken as TT

data State s = State { stateData :: s, stateValue :: Value }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Specification of a state machine, consisting of a transition function that determines the
-- next state from the current state and an input, and a checking function that checks the validity
-- of the transition in the context of the current transaction.
data StateMachine s i = StateMachine {
      -- | The transition function of the state machine. 'Nothing' indicates an invalid transition from the current state.
      smTransition  :: State s -> i -> Maybe (TxConstraints Void Void, State s),

      -- | Check whether a state is the final state
      smFinal       :: s -> Bool,

      -- | The condition checking function. Can be used to perform
      --   checks on the pending transaction that aren't covered by the
      --   constraints. 'smCheck' is always run in addition to checking the
      --   constraints, so the default implementation always returns true.
      smCheck       :: s -> i -> ScriptContext -> Bool,

      -- | The 'ThreadToken' that identifies the contract instance.
      --   Make one with 'getThreadToken' and pass it on to 'mkStateMachine'.
      --   Initialising the machine will then mint a thread token value.
      smThreadToken :: Maybe TT.ThreadToken
    }

{-# INLINABLE threadTokenValueInner #-}
threadTokenValueInner :: Maybe TT.ThreadToken -> ValidatorHash -> Value
threadTokenValueInner = maybe (const mempty) (TT.threadTokenValue . TT.ttCurrencySymbol)

{-# INLINABLE threadTokenValueOrZero #-}
-- | The 'Value' containing exactly the thread token, if one has been specified.
threadTokenValueOrZero :: StateMachineInstance s i -> Value
threadTokenValueOrZero StateMachineInstance{stateMachine,typedValidator} =
    threadTokenValueInner (smThreadToken stateMachine) (validatorHash typedValidator)

-- | A state machine that does not perform any additional checks on the
--   'ScriptContext' (beyond enforcing the constraints)
mkStateMachine
    :: Maybe TT.ThreadToken
    -> (State s -> i -> Maybe (TxConstraints Void Void, State s))
    -> (s -> Bool)
    -> StateMachine s i
mkStateMachine smThreadToken smTransition smFinal =
    StateMachine
        { smTransition
        , smFinal
        , smCheck = \_ _ _ -> True
        , smThreadToken
        }

instance ValidatorTypes (StateMachine s i) where
    type instance RedeemerType (StateMachine s i) = i
    type instance DatumType (StateMachine s i) = s

data StateMachineInstance s i = StateMachineInstance {
    -- | The state machine specification.
    stateMachine   :: StateMachine s i,
    -- | The validator code for this state machine.
    typedValidator :: TypedValidator (StateMachine s i)
    }

machineAddress :: StateMachineInstance s i -> Address
machineAddress = validatorAddress . typedValidator

{-# INLINABLE mkValidator #-}
-- | Turn a state machine into a validator script.
mkValidator :: forall s i. (PlutusTx.IsData s) => StateMachine s i -> ValidatorType (StateMachine s i)
mkValidator (StateMachine step isFinal check threadToken) currentState input ptx =
    let vl = maybe (error ()) (txOutValue . txInInfoResolved) (findOwnInput ptx)
        checkOk =
            traceIfFalse "State transition invalid - checks failed" (check currentState input ptx)
            && traceIfFalse "Thread token not found" (TT.checkThreadToken threadToken (ownHash ptx) vl 1)
        oldState = State{stateData=currentState, stateValue=vl}
        stateAndOutputsOk = case step oldState input of
            Just (newConstraints, State{stateData=newData, stateValue=newValue})
                | isFinal newData ->
                    traceIfFalse "Non-zero value allocated in final state" (isZero newValue)
                    && traceIfFalse "State transition invalid - constraints not satisfied by ScriptContext" (checkScriptContext newConstraints ptx)
                | otherwise ->
                    let txc =
                            newConstraints
                                { txOwnOutputs=
                                    [ OutputConstraint
                                        { ocDatum = newData
                                        , ocValue = newValue <> threadTokenValueInner threadToken (ownHash ptx)
                                        }
                                    ]
                                }
                    in traceIfFalse "State transition invalid - constraints not satisfied by ScriptContext" (checkScriptContext @_ @s txc ptx)
            Nothing -> trace "State transition invalid - input is not a valid transition at the current state" False
    in checkOk && stateAndOutputsOk
