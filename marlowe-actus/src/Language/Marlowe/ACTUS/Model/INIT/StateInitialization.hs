module Language.Marlowe.ACTUS.Model.INIT.StateInitialization where

import           Data.Maybe                                                 (fromJust)
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (ContractTerms)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (initialize)

initializeState :: ContractTerms -> ContractState
initializeState = fromJust . initialize -- FIXME: reconsider fromJust
