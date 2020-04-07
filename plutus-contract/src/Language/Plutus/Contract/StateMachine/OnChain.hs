{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Language.Plutus.Contract.StateMachine.OnChain(
      StateMachine(..)
    , StateMachineInstance (..)
    , State(..)
    , mkStateMachine
    , machineAddress
    , mkValidator
    ) where

import Data.Void (Void)

import qualified Language.PlutusTx                as PlutusTx
import           Language.PlutusTx.Prelude        hiding (check)
import           Ledger.Constraints
import           Ledger.Constraints.TxConstraints (OutputConstraint (..))

import           Ledger                           (Address, Value)
import           Ledger.Typed.Scripts
import           Ledger.Validation                (PendingTx, PendingTx' (pendingTxItem),
                                                   PendingTxIn' (pendingTxInValue))
import           Ledger.Value                     (isZero)

data State s = State { stateData :: s, stateValue :: Value }

-- | Specification of a state machine, consisting of a transition function that determines the
-- next state from the current state and an input, and a checking function that checks the validity
-- of the transition in the context of the current transaction.
data StateMachine s i = StateMachine {
      -- | The transition function of the state machine. 'Nothing' indicates an invalid transition from the current state.
      smTransition :: State s -> i -> Maybe (TxConstraints Void Void, State s),

      -- | Check whether a state is the final state
      smFinal      :: s -> Bool,

      -- | The condition checking function. Can be used to perform
      --   checks on the pending transaction that aren't covered by the
      --   constraints. 'smCheck' is always run in addition to checking the
      --   constraints, so the default implementation always returns true.
      smCheck      :: s -> i -> PendingTx -> Bool
    }

-- | A state machine that does not perform any additional checks on the
--   'PendingTx' (beyond enforcing the constraints)
mkStateMachine
    :: (State s -> i -> Maybe (TxConstraints Void Void, State s))
    -> (s -> Bool)
    -> StateMachine s i
mkStateMachine transition final =
    StateMachine
        { smTransition = transition
        , smFinal      = final
        , smCheck      = \_ _ _ -> True
        }

instance ScriptType (StateMachine s i) where
    type instance RedeemerType (StateMachine s i) = i
    type instance DatumType (StateMachine s i) = s

data StateMachineInstance s i = StateMachineInstance {
    -- | The state machine specification.
    stateMachine      :: StateMachine s i,
    -- | The validator code for this state machine.
    validatorInstance :: ScriptInstance (StateMachine s i)
    }

machineAddress :: StateMachineInstance s i -> Address
machineAddress = scriptAddress . validatorInstance

{-# INLINABLE mkValidator #-}
-- | Turn a state machine into a validator script.
mkValidator :: forall s i. (PlutusTx.IsData s) => StateMachine s i -> ValidatorType (StateMachine s i)
mkValidator (StateMachine step isFinal check) currentState input ptx =
    let vl = pendingTxInValue (pendingTxItem ptx)
        checkOk = traceIfFalseH "State transition invalid - checks failed" (check currentState input ptx)
        oldState = State{stateData=currentState, stateValue=vl}
        stateAndOutputsOk = case step oldState input of
            Just (newConstraints, State{stateData=newData, stateValue=newValue})
                | isFinal newData ->
                    traceIfFalseH "Non-zero value allocated in final state" (isZero newValue)
                    && traceIfFalseH "State transition invalid - constraints not satisfied by PendingTx" (checkPendingTx newConstraints ptx)
                | otherwise ->
                    let txc =
                            newConstraints
                                { txOwnOutputs=
                                    [ OutputConstraint{ocDatum=newData, ocValue= newValue} ]
                                }
                    in traceIfFalseH "State transition invalid - constraints not satisfied by PendingTx" (checkPendingTx @_ @s txc ptx)
            Nothing -> traceH "State transition invalid - input is not a valid transition at the current state" False
    in checkOk && stateAndOutputsOk
