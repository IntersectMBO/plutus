{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Language.PlutusTx.StateMachine(
      StateMachine(..)
    , mkValidator
    , StateMachineRedeemer
    , mkRedeemer
    ) where

import           Language.PlutusTx.Prelude

import           Ledger.Validation         (PendingTx)

-- TODO: This should probably take the pending tx too.
-- | Specification of a state machine
newtype StateMachine s i = StateMachine {
      smTransition :: s -> i -> s
    }

-- | A state machine redeemer takes the data
-- script for the new state, and pairs it with the input.
type StateMachineRedeemer s i = Sealed s -> (i, Sealed s)

-- | A state machine validator takes the old state (the data script), and a pair of the
-- input and the new state (the redeemer output).
type StateMachineValidator s i = s -> (i, Sealed s) -> PendingTx -> Bool

{-# INLINABLE mkRedeemer #-}
mkRedeemer :: forall s i . i -> StateMachineRedeemer s i
mkRedeemer i ss = (i, ss)

{-# INLINABLE mkValidator #-}
-- | Turn a transition function 's -> i -> s' into a validator script.
mkValidator :: Eq s => StateMachine s i -> StateMachineValidator s i
mkValidator (StateMachine trans) currentState (input, unseal -> newState) _ =
    let
        expectedState = trans currentState input
        stateOk =
            traceIfFalseH "State transition invalid - 'expectedState' not equal to 'newState'"
            (expectedState == newState)
    in stateOk
