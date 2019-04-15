{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TemplateHaskell     #-}
module Language.PlutusTx.Coordination.Contracts.GameStateMachine.Stage0(
      StateMachine(..)
    , mkValidator
    , initialState
    , transition
    ) where


import qualified Language.PlutusTx            as P

import           Ledger.Validation         (PendingTx)
import qualified Ledger.Validation         as V

import           Language.Haskell.TH       (Q, TExp)

-- | Specification of a state machine 
data StateMachine s i = StateMachine {
      smTransition :: s -> i -> s
    , smStateEq    :: s -> s -> Bool
    }

initialState :: forall s i. s -> (s, Maybe i)
initialState s = (s, Nothing)

transition :: forall s i. s -> i -> (s, Maybe i)
transition newState input = (newState, Just input)

-- | Turn a transition function 's -> i -> s' into a validator script
mkValidator :: Q (TExp (StateMachine s i -> (s, Maybe i) -> (s, Maybe i) -> PendingTx -> ()))
mkValidator = [|| 
        let 
            mkValidator' :: forall s i. StateMachine s i -> (s, Maybe i) -> (s, Maybe i) -> PendingTx -> ()
            mkValidator' sm (currentState, _) (newState, Just input) p = 
                let 
                    StateMachine trans sEq = sm
                    (vh, V.RedeemerHash rh) = $$(V.ownHashes) p
                    expectedState = trans currentState input

                    stateOk =
                        $$(P.traceIfFalseH) "State transition invalid - 'expectedState' not equal to 'newState'"
                        (sEq expectedState newState)

                    dataScriptHashOk = 
                        let relevantOutputs = 
                                $$(P.map) (\(ds, _) -> ds)
                                ($$(V.scriptOutputsAt) vh p)
                            dsHashOk (V.DataScriptHash dh) = $$(P.equalsByteString) dh rh
                        in 
                            $$(P.traceIfFalseH) "State transition invalid - data script hash not equal to redeemer hash"
                            ($$(P.all) dsHashOk relevantOutputs)
                in 
                    if $$(P.and) stateOk dataScriptHashOk
                    then ()
                    else ($$(P.error) ($$(P.traceH) "State transition failed" ()))


        in mkValidator'
    ||]