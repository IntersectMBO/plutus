{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Language.PlutusTx.StateMachine(
      StateMachine(..)
    , StateMachineInstance (..)
    , StateMachineValidator
    , StateMachineRedeemer
    , StateMachineRedeemerFunction
    , mkValidator
    , mkRedeemer
    ) where

import           Language.PlutusTx.Prelude hiding (check)
import qualified Language.PlutusTx as PlutusTx

import           Ledger.Scripts            (HashedDataScript (..))
import           Ledger.Typed.Tx
import           Ledger.Validation         (PendingTx, findContinuingOutputs, findDataScriptOutputs)

-- | Specification of a state machine, consisting of a transition function that determines the
-- next state from the current state and an input, and a checking function that checks the validity
-- of the transition in the context of the current transaction.
data StateMachine s i = StateMachine {
      smTransition :: s -> i -> Maybe s,
      smCheck :: s -> i -> PendingTx -> Bool
    }

instance ScriptType (StateMachine s i) where
    type instance RedeemerType (StateMachine s i) = StateMachineRedeemer s i
    type instance DataType (StateMachine s i) = s

data StateMachineInstance s i = StateMachineInstance {
    stateMachine :: StateMachine s i,
    validatorInstance :: ScriptInstance (StateMachine s i),
    redeemerInstance :: PlutusTx.CompiledCode (i -> RedeemerFunctionType '[(StateMachine s i)] (StateMachine s i))
    }

-- Type synonyms that don't require TypeFamilies
type StateMachineValidator s i = (s -> (i, Sealed (HashedDataScript s)) -> PendingTx -> Bool)
type StateMachineRedeemer s i = (i, Sealed (HashedDataScript s))
type StateMachineRedeemerFunction s i = Sealed (HashedDataScript s) -> (i, Sealed (HashedDataScript s))

{-# INLINABLE mkRedeemer #-}
mkRedeemer :: forall s i . i -> StateMachineRedeemerFunction s i
mkRedeemer i ss = (i, ss)

{-# INLINABLE mkValidator #-}
-- | Turn a transition function 's -> i -> s' into a validator script.
mkValidator :: Eq s => StateMachine s i -> StateMachineValidator s i
mkValidator (StateMachine step check) currentState (input, unseal -> HashedDataScript newState hsh) ptx =
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

        stateOk = case step currentState input of
            Just expectedState ->
                traceIfFalseH "State transition invalid - 'expectedState' not equal to 'newState'"
                (expectedState == newState)
            Nothing -> traceH "State transition invalid - input is not a valid transition at the current state" False
        checkOk =
            traceIfFalseH "State transition invalid - checks failed"
            (check currentState input ptx)
    in dataScriptOk && stateOk && checkOk
