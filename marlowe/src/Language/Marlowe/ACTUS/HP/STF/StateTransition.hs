{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.STF.StateTransition where

import Data.Time
import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Language.Marlowe.ACTUS.HP.POF.PAM
import Language.Marlowe.ACTUS.HP.ContractTerms

stateTransition :: ScheduledEvent -> ContractTerms -> ContractState -> ContractTermsContext -> ContractStateContext -> ContractState
stateTransition ev terms st@ContractState{..} termsCtx stateCtx = st