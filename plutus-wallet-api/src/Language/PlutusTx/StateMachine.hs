{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'initialState' and 'transition' in off-chain
--   code to obtain the values for data and redeemer scripts.
module Language.PlutusTx.StateMachine(
      StateMachine(..)
    , mkValidator
    , initialState
    , transition
    ) where


import           Language.PlutusTx.Prelude

import           Ledger.Validation         (PendingTx)
import qualified Ledger.Validation         as V

-- | Specification of a state machine
data StateMachine s i = StateMachine {
      smTransition :: s -> i -> s
    , smStateEq    :: s -> s -> Bool
    }

-- | Create a transition script from an initial state of type
--   @s@.
initialState :: forall s i. s -> (s, Maybe i)
initialState s = (s, Nothing)

-- | Create a transition script from a new state of type @s@ and
--   an input of type @i@.
transition :: forall s i. s -> i -> (s, Maybe i)
transition newState input = (newState, Just input)

-- | Turn a transition function 's -> i -> s' into a validator script.
mkValidator :: StateMachine s i -> (s, Maybe i) -> (s, Maybe i) -> PendingTx -> Bool
mkValidator sm (currentState, _) (newState, Just input) p =
    let
        StateMachine trans sEq = sm
        (vh, V.RedeemerHash rh) = V.ownHashes p
        expectedState = trans currentState input

        stateOk =
            traceIfFalseH "State transition invalid - 'expectedState' not equal to 'newState'"
            (sEq expectedState newState)

        dataScriptHashOk =
            let relevantOutputs =
                    map fst
                    (V.scriptOutputsAt vh p)
                dsHashOk (V.DataScriptHash dh) = equalsByteString dh rh
            in
                traceIfFalseH "State transition invalid - data script hash not equal to redeemer hash"
                (all dsHashOk relevantOutputs)
    in stateOk && dataScriptHashOk
mkValidator _ _ _ _ = False
