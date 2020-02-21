{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Language.PlutusTx.StateMachine(
      StateMachine(..)
    , StateMachineInstance (..)
    , machineAddress
    , mkValidator
    ) where

import           Language.PlutusTx.Prelude hiding (check)
import qualified Language.PlutusTx as PlutusTx

import           Ledger                    (Address)
import           Ledger.Typed.Scripts
import           Ledger.Scripts (DataValue (..))
import           Ledger.Validation         (PendingTx, PendingTxOut (..), PendingTxOutType (..), getContinuingOutputs, findData)

-- | Specification of a state machine, consisting of a transition function that determines the
-- next state from the current state and an input, and a checking function that checks the validity
-- of the transition in the context of the current transaction.
data StateMachine s i = StateMachine {
      -- | The transition function of the state machine. 'Nothing' indicates an invalid transition from the current state.
      smTransition :: s -> i -> Maybe s,
      -- | The condition checking function. Checks whether a given state transition is allowed given the 'PendingTx'.
      smCheck :: s -> i -> PendingTx -> Bool,
      -- | The final state predicate. Indicates whether a given state is final (the machine halts in that state).
      smFinal :: s -> Bool
    }

instance ScriptType (StateMachine s i) where
    type instance RedeemerType (StateMachine s i) = i
    type instance DataType (StateMachine s i) = s

data StateMachineInstance s i = StateMachineInstance {
    -- | The state machine specification.
    stateMachine :: StateMachine s i,
    -- | The validator code for this state machine.
    validatorInstance :: ScriptInstance (StateMachine s i)
    }

machineAddress :: StateMachineInstance s i -> Address
machineAddress = scriptAddress . validatorInstance

{-# INLINABLE mkValidator #-}
-- | Turn a transition function 's -> i -> s' into a validator script.
mkValidator :: (Eq s, PlutusTx.IsData s) => StateMachine s i -> ValidatorType (StateMachine s i)
mkValidator (StateMachine step check final) currentState input ptx =
    let checkOk = traceIfFalseH "State transition invalid - checks failed" (check currentState input ptx)
        stateAndOutputsOk = case step currentState input of
            Just newState ->
                case (final newState, getContinuingOutputs ptx) of
                    -- Provided there are no ongoing outputs we don't care about the data scripts
                    (True, outs) -> traceIfFalseH "There must be no ongoing output from a final state" (null outs)
                    -- It's fine to duplicate the data script - only the one on the continuing output matters.
                    -- So we just check that the unique continuing output is one of the ones with this data script.
                    (False, [PendingTxOut{pendingTxOutType=(ScriptTxOut _ dsh)}]) | Just (DataValue d) <- findData dsh ptx, Just givenState <- PlutusTx.fromData d ->
                        traceIfFalseH "State transition invalid - 'givenState' not equal to 'newState'" (givenState == newState)
                    (False, [_]) -> traceH "Data didn't decode properly" False
                    -- It is *not* okay to have multiple outputs with the current validator script, that allows "spliting" the machine.
                    -- This could be okay in principle, but then we'd have to validate the data script for each one, which would complicate
                    -- this validator quite a bit.
                    (False, _) -> traceH "In a non final state there must be precisely one output with the same validator script and a data script must be passed." False
            Nothing -> traceH "State transition invalid - input is not a valid transition at the current state" False
    in checkOk && stateAndOutputsOk
