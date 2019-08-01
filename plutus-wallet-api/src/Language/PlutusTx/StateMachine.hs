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
    , StateMachineValidator
    , mkValidator
    , StateMachineRedeemer
    , mkRedeemer
    ) where

import           Language.PlutusTx.Prelude

import           Ledger.Scripts            (HashedDataScript (..))
import           Ledger.Validation         (PendingTx, findContinuingOutputs, findDataScriptOutputs)

-- | Specification of a state machine
newtype StateMachine s i = StateMachine {
      smTransition :: s -> i -> PendingTx -> s
    }

-- | A state machine redeemer takes the data
-- script for the new state, and pairs it with the input.
type StateMachineRedeemer s i = Sealed (HashedDataScript s) -> (i, Sealed (HashedDataScript s))

-- | A state machine validator takes the old state (the data script), and a pair of the
-- input and the new state (the redeemer output).
type StateMachineValidator s i = s -> (i, Sealed (HashedDataScript s)) -> PendingTx -> Bool

{-# INLINABLE mkRedeemer #-}
mkRedeemer :: forall s i . i -> StateMachineRedeemer s i
mkRedeemer i ss = (i, ss)

{-# INLINABLE mkValidator #-}
-- | Turn a transition function 's -> i -> s' into a validator script.
mkValidator :: Eq s => StateMachine s i -> StateMachineValidator s i
mkValidator (StateMachine trans) currentState (input, unseal -> HashedDataScript newState hsh) ptx =
    let
        vsOutput = uniqueElement (findContinuingOutputs ptx)
        dsOutputs = findDataScriptOutputs hsh ptx
        dataScriptOk = case vsOutput of
            -- It is *not* okay to have multiple outputs with the current validator script, that allows "spliting" the machine.
            -- This could be okay in principle, but then we'd have to validate the data script for each one, which would complicate
            -- this validator quite a bit.
            -- TODO: the state machine should probably be able to "halt" in which case it could be okay to have no outputs with
            -- the validator script. Argument from redeemer could then be 'Maybe-ified'.
            Nothing -> traceH "There must be precisely one output with the same validator script" False
            -- It's fine to duplicate the data script - only the one on the continuing output matters. So we just check
            -- that the unique continuing output is one of the ones with this data script.
            Just i  -> traceIfFalseH "The data script must be attached to the ongoing output" (i `elem` dsOutputs)

        expectedState = trans currentState input ptx
        stateOk =
            traceIfFalseH "State transition invalid - 'expectedState' not equal to 'newState'"
            (expectedState == newState)
    in dataScriptOk && stateOk
